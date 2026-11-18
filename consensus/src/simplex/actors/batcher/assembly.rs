//! Bounded local custody for immutable assembly material.
//!
//! This queue is separate from the reliable vote mailbox. Leases cover queued
//! and currently processed requests; retained round material has its own bound.

use crate::{Epochable, Viewable, simplex::Viewport, types::Epoch};
use commonware_utils::channel::{
    mpsc::{self, error::TrySendError},
    oneshot,
};
use std::{
    future::pending,
    num::NonZeroUsize,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

struct Budget {
    limit: usize,
    used: AtomicUsize,
}

impl Budget {
    fn reserve(self: &Arc<Self>, bytes: usize) -> Option<Lease> {
        let mut used = self.used.load(Ordering::Relaxed);
        loop {
            let next = used.checked_add(bytes).filter(|next| *next <= self.limit)?;
            match self
                .used
                .compare_exchange_weak(used, next, Ordering::Relaxed, Ordering::Relaxed)
            {
                Ok(_) => {
                    return Some(Lease {
                        budget: Arc::clone(self),
                        bytes,
                    });
                }
                Err(current) => used = current,
            }
        }
    }
}

struct Lease {
    budget: Arc<Budget>,
    bytes: usize,
}

impl Drop for Lease {
    fn drop(&mut self) {
        self.budget.used.fetch_sub(self.bytes, Ordering::Relaxed);
    }
}

pub(super) struct Request<A> {
    material: A,
    reply: oneshot::Sender<bool>,
    lease: Lease,
}

impl<A> Request<A> {
    pub(super) const fn material(&self) -> &A {
        &self.material
    }

    /// Processes accepted custody even if its acknowledgement was cancelled.
    pub(super) fn complete(self, install: impl FnOnce(A) -> bool) {
        let Self {
            material,
            reply,
            lease,
        } = self;
        let installed = install(material);
        drop(lease);
        let _ = reply.send(installed);
    }
}

pub(super) struct Sender<A> {
    sender: mpsc::Sender<Request<A>>,
    budget: Arc<Budget>,
}

impl<A> Clone for Sender<A> {
    fn clone(&self) -> Self {
        Self {
            sender: self.sender.clone(),
            budget: Arc::clone(&self.budget),
        }
    }
}

impl<A> Sender<A> {
    pub(super) fn submit(
        &self,
        material: A,
        bytes: usize,
    ) -> Result<oneshot::Receiver<bool>, TrySendError<A>> {
        if self.sender.is_closed() {
            return Err(TrySendError::Closed(material));
        }
        let Some(lease) = self.budget.reserve(bytes) else {
            return Err(TrySendError::Full(material));
        };
        let (reply, receiver) = oneshot::channel();
        let request = Request {
            material,
            reply,
            lease,
        };
        match self.sender.try_send(request) {
            Ok(()) => Ok(receiver),
            Err(TrySendError::Full(request)) => Err(TrySendError::Full(request.material)),
            Err(TrySendError::Closed(request)) => Err(TrySendError::Closed(request.material)),
        }
    }
}

pub(super) type Receiver<A> = mpsc::Receiver<Request<A>>;

/// Local material cannot create rounds outside bounded vote admission.
pub(super) fn admitted(
    epoch: Epoch,
    viewport: Viewport,
    material: &(impl Epochable + Viewable),
) -> bool {
    material.epoch() == epoch
        && material.view() > viewport.finalized
        && viewport.admits_vote(material.view())
}

/// A zero budget allocates neither a channel nor a shared byte counter.
pub(super) fn channel<A>(
    capacity: NonZeroUsize,
    bytes: usize,
) -> (Option<Sender<A>>, Option<Receiver<A>>) {
    if bytes == 0 {
        return (None, None);
    }
    let (sender, receiver) = mpsc::channel(capacity.get());
    (
        Some(Sender {
            sender,
            budget: Arc::new(Budget {
                limit: bytes,
                used: AtomicUsize::new(0),
            }),
        }),
        Some(receiver),
    )
}

/// Closing this optional port never stops the native vote/certificate loop.
pub(super) async fn recv<A>(receiver: &mut Option<Receiver<A>>) -> Request<A> {
    if let Some(channel) = receiver {
        if let Some(request) = channel.recv().await {
            return request;
        }
        *receiver = None;
    }
    pending().await
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        simplex::{
            Lookahead,
            phase2::{Mode, Plain},
            scheme::ed25519,
        },
        types::{Round, TermLength, View, ViewDelta},
    };
    use commonware_cryptography::sha256::Digest;
    use commonware_runtime::{Runner as _, deterministic};
    use futures::FutureExt as _;

    #[test]
    fn plain_has_no_allocated_port() {
        let (sender, receiver) = channel::<<Plain as Mode<ed25519::Scheme, Digest>>::Assembly>(
            NonZeroUsize::new(1).unwrap(),
            <Plain as Mode<ed25519::Scheme, Digest>>::ASSEMBLY_BUDGET,
        );
        assert!(sender.is_none());
        assert!(receiver.is_none());
    }

    #[test]
    fn local_material_cannot_open_unbounded_future_or_finalized_rounds() {
        let epoch = Epoch::new(1);
        let viewport = Viewport {
            finalized: View::new(2),
            current: View::new(4),
            view_retention: ViewDelta::new(10),
            lookahead: Lookahead {
                term_length: TermLength::ONE,
                optimistic_views: ViewDelta::new(0),
            },
        };
        for view in [3, 4, 5] {
            assert!(admitted(
                epoch,
                viewport,
                &Round::new(epoch, View::new(view))
            ));
        }
        for view in [0, 1, 2, 6, u64::MAX] {
            assert!(!admitted(
                epoch,
                viewport,
                &Round::new(epoch, View::new(view))
            ));
        }
        assert!(!admitted(
            epoch,
            viewport,
            &Round::new(Epoch::new(2), View::new(4)),
        ));
    }

    #[test]
    fn queue_full_returns_custody_without_leaking_bytes() {
        let (sender, mut receiver) = channel(NonZeroUsize::new(1).unwrap(), 10);
        let sender = sender.unwrap();
        let receiver = receiver.as_mut().unwrap();
        let mut reply = sender.submit(vec![1; 3], 3).unwrap();
        assert!(
            matches!(sender.submit(vec![2; 4], 4), Err(TrySendError::Full(value)) if value == vec![2; 4])
        );
        assert_eq!(sender.budget.used.load(Ordering::Relaxed), 3);
        let request = receiver.try_recv().unwrap();
        assert_eq!(request.material(), &vec![1; 3]);
        assert_eq!(sender.budget.used.load(Ordering::Relaxed), 3);
        assert!(reply.try_recv().is_err());
        request.complete(|material| material == vec![1; 3]);
        assert_eq!(reply.try_recv(), Ok(true));
        assert_eq!(sender.budget.used.load(Ordering::Relaxed), 0);
        assert!(sender.submit(vec![3; 10], 10).is_ok());
    }

    #[test]
    fn clones_share_byte_budget_until_processing_finishes() {
        let (sender, mut receiver) = channel(NonZeroUsize::new(3).unwrap(), 8);
        let sender = sender.unwrap();
        let other = sender.clone();
        let receiver = receiver.as_mut().unwrap();
        let _first = sender.submit(5, 5).unwrap();
        assert!(matches!(other.submit(4, 4), Err(TrySendError::Full(4))));
        let _second = other.submit(3, 3).unwrap();
        assert_eq!(sender.budget.used.load(Ordering::Relaxed), 8);
        let request = receiver.try_recv().unwrap();
        assert!(matches!(other.submit(1, 1), Err(TrySendError::Full(1))));
        drop(request);
        assert_eq!(sender.budget.used.load(Ordering::Relaxed), 3);
        let _third = other.submit(4, 4).unwrap();
        assert!(matches!(
            sender.submit(usize::MAX, usize::MAX),
            Err(TrySendError::Full(usize::MAX))
        ));
        assert_eq!(sender.budget.used.load(Ordering::Relaxed), 7);
        drop(receiver.try_recv().unwrap());
        drop(receiver.try_recv().unwrap());
        assert_eq!(sender.budget.used.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn cancelled_reply_does_not_cancel_installation_and_rejection_releases() {
        let (sender, mut receiver) = channel(NonZeroUsize::new(1).unwrap(), 8);
        let sender = sender.unwrap();
        let receiver = receiver.as_mut().unwrap();
        let reply = sender.submit(View::new(4), 8).unwrap();
        drop(reply);
        let mut installed = None;
        receiver.try_recv().unwrap().complete(|material| {
            installed = Some(material);
            true
        });
        assert_eq!(installed, Some(View::new(4)));
        assert_eq!(sender.budget.used.load(Ordering::Relaxed), 0);
        let mut reply = sender.submit(View::new(5), 8).unwrap();
        receiver.try_recv().unwrap().complete(|_| false);
        assert_eq!(reply.try_recv(), Ok(false));
        assert_eq!(sender.budget.used.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn shutdown_reclaims_queued_leases_and_returns_closed_custody() {
        let (sender, receiver) = channel(NonZeroUsize::new(2).unwrap(), 8);
        let sender = sender.unwrap();
        let mut reply = sender.submit(vec![1; 8], 8).unwrap();
        drop(receiver);
        assert!(reply.try_recv().is_err());
        assert_eq!(sender.budget.used.load(Ordering::Relaxed), 0);
        assert!(
            matches!(sender.submit(vec![2; 8], 8), Err(TrySendError::Closed(value)) if value == vec![2; 8])
        );
        assert_eq!(sender.budget.used.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn optional_receive_acknowledges_install_and_stays_pending_after_close() {
        deterministic::Runner::default().start(|_| async move {
            let (sender, mut receiver) = channel(NonZeroUsize::new(1).unwrap(), 8);
            let sender = sender.unwrap();
            let reply = sender.submit(7, 8).unwrap();
            recv(&mut receiver).await.complete(|value| value == 7);
            assert_eq!(reply.await, Ok(true));
            drop(sender);
            assert!(recv(&mut receiver).now_or_never().is_none());
            assert!(receiver.is_none());
            assert!(recv(&mut receiver).now_or_never().is_none());
        });
    }
}
