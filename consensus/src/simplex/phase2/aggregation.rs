//! Native final-vote accumulator selection. Plain retains the single-context
//! fast path; Extended groups complete signed interpretation subjects.
use super::{Mode, Plain};
pub use crate::simplex::actors::batcher::{
    Round as BatcherRound, RoundWith, Verifier, VerifierWith,
};
use crate::{
    simplex::{
        scheme::Scheme,
        types::{Finalization, Finalize, Proposal, Subject},
    },
    types::{Participant, Round},
};
use commonware_cryptography::{
    Digest,
    certificate::{Attestation, Scheme as CertificateScheme},
};
use commonware_parallel::Strategy;
use commonware_runtime::telemetry::traces::TracedExt as _;
use commonware_utils::non_empty;
use rand::rngs::StdRng;
use rand_core::{CryptoRng, SeedableRng};
use std::{future::Future, mem, sync::Arc};
use tracing::{Instrument as _, Span, info_span};

/// Native-owned accumulation policy selected by the sealed representation mode.
pub trait Aggregation<S: Scheme<D>, D: Digest>: Mode<S, D> {
    /// Final votes never share a quorum across different signed subjects.
    type FinalBuffer: FinalBuffer<S, D, Vote = Self::Vote, Certificate = Self::Certificate>;
}
/// Native final-vote accumulation. The caller verifies sender identity and admits
/// at most one vote per participant per phase. Application validation is separate.
pub trait FinalBuffer<S: Scheme<D>, D: Digest>: Send {
    /// Mode-specific individual final vote.
    type Vote;
    /// Mode-specific original-round certificate.
    type Certificate: Send + 'static;
    /// Opens bounded per-view accumulation using the native roster and quorum.
    fn new(quorum: usize, participants: usize) -> Self;
    /// Retains a locally verified or source-authenticated remote vote.
    fn push(&mut self, vote: Self::Vote, verified: bool);
    /// Filters to the independently established original proposal.
    fn retain_proposal(&mut self, proposal: &Proposal<D>);
    /// Drops buffered votes after an authenticated certificate is recorded.
    fn complete(&mut self);
    /// Whether an authenticated certificate already completed collection.
    fn is_complete(&self) -> bool;
    /// Whether prior individually verified votes already have an exact quorum.
    fn has_constructable_quorum(&self) -> bool;
    /// Verifies pending votes and constructs an exact-subject certificate.
    fn construct<R: CryptoRng + Send>(
        &mut self,
        scheme: &Arc<S>,
        round: Round,
        rng: &mut R,
        strategy: &impl Strategy,
    ) -> impl Future<Output = Option<Batch<Self::Certificate>>> + Send;
}
impl<S: Scheme<D>, D: Digest> Aggregation<S, D> for Plain {
    type FinalBuffer = Certification<Proposal<D>, S>;
}
impl<S: Scheme<D>, D: Digest> FinalBuffer<S, D> for Certification<Proposal<D>, S> {
    type Vote = Finalize<S, D>;
    type Certificate = Finalization<S, D>;
    fn new(quorum: usize, _participants: usize) -> Self {
        Self::new(quorum)
    }
    fn push(&mut self, vote: Self::Vote, verified: bool) {
        self.add(vote.proposal, vote.attestation, verified);
    }
    fn retain_proposal(&mut self, proposal: &Proposal<D>) {
        self.retain(|context| context == proposal);
    }
    fn complete(&mut self) {
        self.complete();
    }
    fn is_complete(&self) -> bool {
        self.is_complete()
    }
    fn has_constructable_quorum(&self) -> bool {
        self.has_constructable_quorum()
    }
    async fn construct<R: CryptoRng + Send>(
        &mut self,
        scheme: &Arc<S>,
        round: Round,
        rng: &mut R,
        strategy: &impl Strategy,
    ) -> Option<Batch<Self::Certificate>> {
        self.try_construct(
            scheme,
            rng,
            strategy,
            || {
                info_span!(
                    "simplex.batcher.construct.finalization",
                    epoch = round.epoch().traced(),
                    view = round.view().traced()
                )
            },
            |proposal| Subject::Finalize { proposal },
            |proposal, certificate| Finalization {
                proposal,
                certificate,
            },
        )
        .await
    }
}
commonware_macros::stability_mod!(ALPHA, pub mod extended);

/// Runs a CPU-bound job through [Strategy::spawn], entering `span` on the worker thread and
/// instrumenting the returned future so the offloaded work stays attributed to the caller's trace.
fn offload<P, F, T>(len: usize, span: Span, strategy: &P, job: F) -> impl Future<Output = T> + Send
where
    P: Strategy,
    F: FnOnce(P) -> T + Send + 'static,
    T: Send + 'static,
{
    let worker_span = span.clone();
    strategy
        .spawn(len, move |strategy| worker_span.in_scope(|| job(strategy)))
        .instrument(span)
}

/// The outcome of processing one vote kind.
pub struct Batch<C> {
    /// Pending votes processed, whether individually or through a certificate.
    pub processed: usize,
    /// Signers identified as invalid by attestation verification.
    ///
    /// An empty result does not mean every input vote was individually verified:
    /// successful optimistic assembly returns no per-vote results.
    pub invalid: Vec<Participant>,
    /// A certificate authenticated from the buffered votes.
    pub certificate: Option<C>,
    /// Whether `optimistic_assemble` returned pending attestation verification results.
    pub fallback: bool,
}

/// Native common-subject verification and assembly buffer.
///
/// Public for static mode selection; mutations remain native-owned.
/// Certification progress for one kind of vote.
///
/// Each kind certifies independently: a view can legitimately certify both
/// a notarization and a nullification.
pub struct Certification<C, S: CertificateScheme, const RESERVE_QUORUM: bool = true> {
    /// Votes required to construct a certificate.
    quorum: usize,
    /// Progress toward a certificate.
    pub(crate) state: State<C, S>,
}

/// The state of a [Certification].
pub(crate) enum State<C, S: CertificateScheme> {
    /// No certificate yet. Votes accumulate toward a quorum.
    Incomplete {
        /// Votes awaiting signature verification.
        pending: Vec<(C, Attestation<S>)>,
        /// Votes with verified signatures, held for certificate construction.
        verified: Vec<(C, Attestation<S>)>,
    },
    /// A certificate exists. Further votes are dropped.
    Complete,
}

impl<C, S: CertificateScheme, const RESERVE_QUORUM: bool> Certification<C, S, RESERVE_QUORUM> {
    /// Creates an empty [State::Incomplete] whose vote buffers allocate lazily.
    pub(crate) const fn new(quorum: usize) -> Self {
        Self {
            quorum,
            state: State::Incomplete {
                pending: Vec::new(),
                verified: Vec::new(),
            },
        }
    }

    /// Buffers a vote for verification (or, if already verified, for
    /// certificate construction). The caller owns signer uniqueness. Votes that
    /// arrive after completion are dropped.
    pub(crate) fn add(&mut self, context: C, attestation: Attestation<S>, is_verified: bool) {
        let State::Incomplete { pending, verified } = &mut self.state else {
            return;
        };

        // Verified votes may accumulate to quorum. A batchable pending buffer
        // only needs the remaining unverified slots, while a non-batchable
        // pending buffer is consumed after each vote.
        let initial_capacity = if RESERVE_QUORUM && (is_verified || S::is_batchable()) {
            self.quorum.saturating_sub(verified.len()).max(1)
        } else {
            1
        };
        let votes = if is_verified { verified } else { pending };
        if votes.capacity() == 0 {
            votes.reserve_exact(initial_capacity);
        }
        votes.push((context, attestation));
    }

    /// Whether an unfinished kind has a verified quorum, allowing construction
    /// before proposal selection.
    pub(crate) const fn has_constructable_quorum(&self) -> bool {
        matches!(&self.state, State::Incomplete { verified, .. } if verified.len() >= self.quorum)
    }

    /// Whether to attempt construction: a verified quorum exists, or pending
    /// votes exist and (for batchable schemes) the buffers together could reach one.
    pub(crate) fn should_construct(&self) -> bool {
        match &self.state {
            State::Incomplete { pending, verified } => {
                verified.len() >= self.quorum
                    || (!pending.is_empty()
                        && (!S::is_batchable() || verified.len() + pending.len() >= self.quorum))
            }
            State::Complete => false,
        }
    }

    /// Processes pending votes and assembles any resulting quorum in one worker.
    /// Pending verification requires one context, retained with every attestation so
    /// proposal changes can filter both buffers. An existing verified quorum skips
    /// pending votes and can complete before proposal selection.
    pub(crate) async fn try_construct<R, D, O, F, G>(
        &mut self,
        scheme: &Arc<S>,
        rng: &mut R,
        strategy: &impl Strategy,
        span: impl FnOnce() -> Span,
        subject: F,
        wrap: G,
    ) -> Option<Batch<O>>
    where
        R: CryptoRng,
        D: Digest,
        S: Scheme<D>,
        C: Clone + Send + Sync + 'static,
        F: for<'a> Fn(&'a C) -> Subject<'a, D> + Send + 'static,
        G: FnOnce(C, S::Certificate) -> O + Send + 'static,
        O: Send + 'static,
    {
        if !self.should_construct() {
            return None;
        }
        let State::Incomplete { pending, verified } = &mut self.state else {
            unreachable!("complete certification cannot require construction");
        };

        // A verified quorum can construct the certificate without processing pending votes.
        if verified.len() >= self.quorum {
            pending.clear();
        }

        // Move the inputs into one worker for assembly and any fallback verification.
        let processed = pending.len();
        let len = processed + verified.len();
        let quorum = self.quorum;
        let (pending, mut verified) = (mem::take(pending), mem::take(verified));
        let scheme = Arc::clone(scheme);
        let mut rng = StdRng::from_rng(rng);
        let (votes, result) = offload(len, span(), strategy, move |strategy| {
            let context = verified
                .first()
                .or_else(|| pending.first())
                .expect("construction attempt requires votes")
                .0
                .clone();

            // A candidate quorum can authenticate the certificate without establishing
            // individual vote validity. Failure returns verification results for pending votes.
            // Below quorum, non-batchable schemes verify pending votes directly.
            let (result, fallback) = if len >= quorum {
                match scheme.optimistic_assemble::<_, D, _, _>(
                    &mut rng,
                    subject(&context),
                    pending.into_iter().map(|(_, attestation)| attestation),
                    verified.iter().map(|(_, attestation)| attestation),
                    &strategy,
                ) {
                    Ok(certificate) => {
                        return (
                            Vec::new(),
                            Batch {
                                processed,
                                invalid: Vec::new(),
                                certificate: Some(wrap(context, certificate)),
                                fallback: false,
                            },
                        );
                    }
                    Err(result) => (result, true),
                }
            } else {
                (
                    scheme.verify_attestations::<_, D, _>(
                        &mut rng,
                        subject(&context),
                        pending.into_iter().map(|(_, attestation)| attestation),
                        &strategy,
                    ),
                    false,
                )
            };

            // A quorum of prior and newly verified votes must assemble. Otherwise retain
            // them with their context so proposal changes can filter them.
            let certificate = if verified.len() + result.verified.len() >= quorum {
                let prior = verified.drain(..).map(|(_, attestation)| attestation);
                let certificate = scheme
                    .assemble(non_empty![@prior.chain(result.verified)], &strategy)
                    .expect("verified quorum must assemble");
                Some(wrap(context, certificate))
            } else {
                verified.extend(
                    result
                        .verified
                        .into_iter()
                        .map(|attestation| (context.clone(), attestation)),
                );
                None
            };
            (
                verified,
                Batch {
                    processed,
                    invalid: result.invalid,
                    certificate,
                    fallback,
                },
            )
        })
        .await;

        // Only verified votes survive an incomplete attempt. A certificate completes
        // this kind and releases its buffers.
        if result.certificate.is_some() {
            self.complete();
        } else {
            let State::Incomplete { verified, .. } = &mut self.state else {
                unreachable!("certification completed mid-construction");
            };
            *verified = votes;
        }
        Some(result)
    }

    /// Completes, dropping all buffered votes.
    pub(crate) fn complete(&mut self) {
        self.state = State::Complete;
    }

    /// Returns true if a certificate exists.
    pub(crate) const fn is_complete(&self) -> bool {
        matches!(self.state, State::Complete)
    }

    /// Retains only the votes matching `f`.
    pub(crate) fn retain(&mut self, f: impl Fn(&C) -> bool) {
        if let State::Incomplete { pending, verified } = &mut self.state {
            pending.retain(|(context, _)| f(context));
            verified.retain(|(context, _)| f(context));
        }
    }
}
