use super::{
    actors::{batcher, resolver, voter},
    config::{Config, SkipPolicy},
    elector::{self, Elector as _},
    phase2::{
        Plain,
        aggregation::Aggregation,
        voting::{NoExtension, Participation, Voting},
    },
    types::{ActivityWith, Context},
};
use crate::{
    CertifiableAutomaton, Relay, Reporter,
    simplex::{Lookahead, Plan, scheme::Scheme},
};
use commonware_cryptography::Digest;
use commonware_macros::select;
use commonware_p2p::{Blocker, Receiver, Sender};
use commonware_parallel::Strategy;
use commonware_runtime::{
    BufferPooler, Clock, ContextCell, Handle, Metrics, Spawner, Storage, spawn_cell,
};
use rand_core::CryptoRng;
use tracing::debug;

/// Instance of `simplex` consensus engine.
pub struct Engine<
    E: BufferPooler + Clock + CryptoRng + Spawner + Storage + Metrics,
    S: Scheme<D>,
    L: elector::Config<S>,
    B: Blocker<PublicKey = S::PublicKey>,
    D: Digest,
    A: CertifiableAutomaton<Context = Context<D, S::PublicKey>, Digest = D>,
    R: Relay<Digest = D, PublicKey = S::PublicKey, Plan = Plan<S::PublicKey>>,
    F: Reporter<Activity = ActivityWith<S, D, M>>,
    T: Strategy,
    M: Aggregation<S, D> + Voting<S, D> = Plain,
    X: Participation<S, D, M> = NoExtension,
> {
    context: ContextCell<E>,

    voter: voter::ActorWith<E, S, L::Elector, B, D, A, R, F, M, X>,
    voter_mailbox: voter::Mailbox<S, D, M>,

    batcher: batcher::ActorWith<E, S, B, D, F, R, T, M>,
    batcher_mailbox: batcher::Mailbox<S, D, M>,

    resolver: resolver::ActorWith<E, S, B, D, T, M>,
    resolver_mailbox: resolver::Mailbox<S, D, M>,
}

impl<
    E: BufferPooler + Clock + CryptoRng + Spawner + Storage + Metrics,
    S: Scheme<D>,
    L: elector::Config<S>,
    B: Blocker<PublicKey = S::PublicKey>,
    D: Digest,
    A: CertifiableAutomaton<Context = Context<D, S::PublicKey>, Digest = D>,
    R: Relay<Digest = D, PublicKey = S::PublicKey, Plan = Plan<S::PublicKey>>,
    F: Reporter<Activity = ActivityWith<S, D, M>>,
    T: Strategy,
    M: Aggregation<S, D> + Voting<S, D>,
    X: Participation<S, D, M>,
> Engine<E, S, L, B, D, A, R, F, T, M, X>
{
    /// Constructs an engine with a static vote representation and trusted evidence adapter.
    ///
    /// The adapter must restore durable evidence before startup and authenticate
    /// application material before making it ready. It cannot grant native vote
    /// eligibility or parent authority. Extended split-vote recovery and bounded
    /// exact-history fetching are not yet integrated; this is an experimental API.
    #[commonware_macros::stability(ALPHA)]
    pub fn new_with(
        context: E,
        cfg: Config<S, L, B, D, A, R, F, T, M>,
        mode_context: M::Context,
        participation: X,
    ) -> Self {
        Self::build(context, cfg, mode_context, participation)
    }

    fn build(
        mut context: E,
        cfg: Config<S, L, B, D, A, R, F, T, M>,
        mode_context: M::Context,
        participation: X,
    ) -> Self {
        // Ensure configuration is valid
        cfg.assert(&mut context);
        let skip_budget = match cfg.skip {
            SkipPolicy::Disabled => 0,
            SkipPolicy::Enabled { budget, .. } => budget.resolve(cfg.scheme.participants().len()),
        };
        let elector = cfg.elector.build(cfg.scheme.participants());
        let terms = elector.terms();
        let term_length = terms.length();
        if let Some(stall_timeout) = terms.stall_timeout() {
            assert!(
                stall_timeout > cfg.certification_timeout,
                "stall timeout must be greater than certification timeout"
            );
        }

        // Create batcher
        let (batcher, batcher_mailbox) = batcher::ActorWith::new(
            context.child("batcher"),
            batcher::Config {
                scheme: cfg.scheme.clone(),
                blocker: cfg.blocker.clone(),
                reporter: cfg.reporter.clone(),
                track_historical_votes: cfg.track_historical_votes,
                relay: cfg.relay.clone(),
                strategy: cfg.strategy.clone(),
                epoch: cfg.epoch,
                mailbox_size: cfg.mailbox_size,
                view_retention: cfg.view_retention,
                skip: cfg.skip,
                lookahead: Lookahead::new(&terms),
                forward: cfg.forward,
                floor: cfg.floor.view(),
            },
        );

        // Create voter
        let (voter, voter_mailbox) = voter::ActorWith::new_with(
            context.child("voter"),
            voter::Config {
                scheme: cfg.scheme.clone(),
                elector,
                blocker: cfg.blocker.clone(),
                automaton: cfg.automaton,
                relay: cfg.relay,
                reporter: cfg.reporter,
                partition: cfg.partition,
                mailbox_size: cfg.mailbox_size,
                epoch: cfg.epoch,
                floor: cfg.floor,
                leader_timeout: cfg.leader_timeout,
                certification_timeout: cfg.certification_timeout,
                timeout_retry: cfg.timeout_retry,
                skip_budget,
                view_retention: cfg.view_retention,
                replay_buffer: cfg.replay_buffer,
                write_buffer: cfg.write_buffer,
                page_cache: cfg.page_cache,
            },
            mode_context,
            participation,
        );

        // Create resolver
        let (resolver, resolver_mailbox) = resolver::ActorWith::new(
            context.child("resolver"),
            resolver::Config {
                blocker: cfg.blocker,
                scheme: cfg.scheme,
                strategy: cfg.strategy,
                mailbox_size: cfg.mailbox_size,
                epoch: cfg.epoch,
                fetch_timeout: cfg.fetch_timeout,
                term_length,
            },
        );

        // Return the engine
        Self {
            context: ContextCell::new(context),

            voter,
            voter_mailbox,

            batcher,
            batcher_mailbox,

            resolver,
            resolver_mailbox,
        }
    }

    /// Returns a local readiness notifier. It cannot inject votes or certificates.
    #[commonware_macros::stability(ALPHA)]
    pub fn readiness(&self) -> Readiness<S, D, M> {
        Readiness {
            mailbox: self.voter_mailbox.clone(),
        }
    }

    /// Start the `simplex` consensus engine.
    ///
    /// This will also rebuild the state of the engine from provided `Journal`.
    ///
    /// # Network Channels
    ///
    /// The engine requires three separate network channels, each carrying votes or
    /// certificates to help drive the consensus engine.
    ///
    /// ## `vote_network`
    ///
    /// Carries **individual votes**:
    /// - [`Notarize`](super::types::Notarize): Vote to notarize a proposal
    /// - [`Nullify`](super::types::Nullify): Vote to skip a view
    /// - [`Finalize`](super::types::Finalize): Vote to finalize a notarized proposal
    ///
    /// These messages are sent to the batcher, which performs batch signature
    /// verification before forwarding valid votes to the voter for aggregation.
    ///
    /// ## `certificate_network`
    ///
    /// Carries **certificates**:
    /// - [`Notarization`](super::types::Notarization): Proof that a proposal was notarized
    /// - [`Nullification`](super::types::Nullification): Proof that a view was skipped
    /// - [`Finalization`](super::types::Finalization): Proof that a proposal was finalized
    ///
    /// Certificates are broadcast on this channel as soon as they are constructed
    /// from collected votes. We separate this from the `vote_network` to optimistically
    /// allow for certificate processing to short-circuit vote processing (if we receive
    /// a certificate before processing pending votes, we can skip them).
    ///
    /// ## `resolver_network`
    ///
    /// Used for request-response certificate fetching. When a node needs to
    /// catch up on a view it missed (e.g., to verify a proposal's parent), it
    /// uses this channel to request certificates from peers. The resolver handles
    /// retries and peer selection for these requests.
    pub fn start(
        mut self,
        vote_network: (
            impl Sender<PublicKey = S::PublicKey>,
            impl Receiver<PublicKey = S::PublicKey>,
        ),
        certificate_network: (
            impl Sender<PublicKey = S::PublicKey>,
            impl Receiver<PublicKey = S::PublicKey>,
        ),
        resolver_network: (
            impl Sender<PublicKey = S::PublicKey>,
            impl Receiver<PublicKey = S::PublicKey>,
        ),
    ) -> Handle<()> {
        spawn_cell!(
            self.context,
            self.run(vote_network, certificate_network, resolver_network)
        )
    }

    async fn run(
        self,
        vote_network: (
            impl Sender<PublicKey = S::PublicKey>,
            impl Receiver<PublicKey = S::PublicKey>,
        ),
        certificate_network: (
            impl Sender<PublicKey = S::PublicKey>,
            impl Receiver<PublicKey = S::PublicKey>,
        ),
        resolver_network: (
            impl Sender<PublicKey = S::PublicKey>,
            impl Receiver<PublicKey = S::PublicKey>,
        ),
    ) {
        // Start the batcher (receives votes via vote_network, certificates via certificate_network)
        // Batcher sends proposals/certificates to voter via voter_mailbox
        let (vote_sender, vote_receiver) = vote_network;
        let (certificate_sender, certificate_receiver) = certificate_network;
        let mut batcher_task = self.batcher.start(
            self.voter_mailbox.clone(),
            vote_receiver,
            certificate_receiver,
        );

        // Start the resolver (sends certificates to voter via voter_mailbox)
        let (resolver_sender, resolver_receiver) = resolver_network;
        let mut resolver_task =
            self.resolver
                .start(self.voter_mailbox, resolver_sender, resolver_receiver);

        // Start the voter
        let mut voter_task = self.voter.start(
            self.batcher_mailbox,
            self.resolver_mailbox,
            vote_sender,
            certificate_sender,
        );

        // If any task completes, the engine should stop
        let mut shutdown = self.context.stopped();
        select! {
            _ = &mut shutdown => {
                debug!("context shutdown, stopping engine");
            },
            voter = &mut voter_task => {
                debug!(?voter, "voter stopped, shutting down engine");
            },
            batcher = &mut batcher_task => {
                debug!(?batcher, "batcher stopped, shutting down engine");
            },
            resolver = &mut resolver_task => {
                debug!(?resolver, "resolver stopped, shutting down engine");
            },
        }
    }
}

impl<
    E: BufferPooler + Clock + CryptoRng + Spawner + Storage + Metrics,
    S: Scheme<D>,
    L: elector::Config<S>,
    B: Blocker<PublicKey = S::PublicKey>,
    D: Digest,
    A: CertifiableAutomaton<Context = Context<D, S::PublicKey>, Digest = D>,
    R: Relay<Digest = D, PublicKey = S::PublicKey, Plan = Plan<S::PublicKey>>,
    F: Reporter<Activity = ActivityWith<S, D, Plain>>,
    T: Strategy,
> Engine<E, S, L, B, D, A, R, F, T>
{
    /// Creates the stock Simplex engine without extension state or wire fields.
    pub fn new(context: E, cfg: Config<S, L, B, D, A, R, F, T>) -> Self {
        Self::build(context, cfg, (), NoExtension)
    }
}

commonware_macros::stability_scope!(ALPHA {
    /// Exact Accept request admitted by the live native voter for material retention.
    /// This is neither a vote nor durable authority. After custody, the voter repeats
    /// election, deadline, ancestry, proof and local fence checks before staging.
    /// No decoder or public constructor can recreate this live admission.
    pub struct AdmittedRecovery<S: Scheme<D>, D: Digest> {
        request: super::extension::request::Request<S,D>,
    }
    impl<S: Scheme<D>, D: Digest> AdmittedRecovery<S,D> {
        /// The exact immutable request checked by the native voter.
        pub const fn request(&self) -> &super::extension::request::Request<S,D> { &self.request }
        /// Consumes admission and returns its original request as untrusted data.
        pub fn into_request(self) -> super::extension::request::Request<S,D> { self.request }
    }
    /// A trusted application may announce that its retained evidence changed.
    /// Native eligibility, ancestry and journal durability still govern voting.
    #[derive(Clone)]
    pub struct Readiness<S: Scheme<D>, D: Digest, M: Voting<S, D>> {
        mailbox: voter::Mailbox<S, D, M>,
    }
    impl<S:Scheme<D>,D:Digest> Readiness<S,D,super::phase2::Extended> {
        /// Admits an exact Accept for custody only after read-only native validation.
        /// Closure or refusal yields no token. Eligibility can change during custody;
        /// request_recovery must still perform the normal validation and sync barrier.
        pub fn admit_recovery(&mut self,request:super::extension::request::Request<S,D>) -> impl std::future::Future<Output=Option<AdmittedRecovery<S,D>>> + Send + 'static {
            use commonware_codec::EncodeSize as _;
            let reply = (request.encode_size() <= super::extension::request::MAX_BYTES)
                .then(|| self.mailbox.validate_recovery(request.clone()));
            async move {
                if reply?.await.ok()? { Some(AdmittedRecovery { request }) } else { None }
            }
        }
        /// Polls native leader/deadline/ancestry state or prepares a request from
        /// a retained original status quorum. It does not grant a voting decision.
        pub fn prepare_recovery(&mut self,query:super::extension::request::Query<S,D>)->commonware_utils::channel::oneshot::Receiver<Option<super::extension::request::Request<S,D>>> {
            self.mailbox.prepare_recovery(query)
        }
        /// Installs an authenticated parent interpretation after native journal sync.
        /// True is durable retention, not canonical finality or delivery authority.
        pub fn install_recovered(&mut self,certificate:super::extension::certificate::Recovered<S,D>)->commonware_utils::channel::oneshot::Receiver<bool> {
            self.mailbox.install_recovered(certificate)
        }
        /// Submits a signed replacement-leader request to the native voter.
        /// A response is produced only after native validation and journal sync.
        /// Neither this handle nor an evidence callback can grant voting authority.
        pub fn request_recovery(&mut self,request:super::extension::request::Request<S,D>)->commonware_utils::channel::oneshot::Receiver<Option<super::extension::request::Response<S,D>>> {
            self.mailbox.recover_extension(request)
        }
    }
    impl<S: Scheme<D>, D: Digest, M: Voting<S, D>> Readiness<S, D, M> {
        /// Retry this view after evidence has been authenticated and made durable.
        /// Repeated pending notifications for the same view are coalesced.
        pub fn notify(&mut self, view: crate::types::View) {
            self.mailbox.interpretation_ready(view);
        }
    }
    #[cfg(test)]
    #[path = "extension/coordinator_tests.rs"]
    mod coordinator_tests;
});
