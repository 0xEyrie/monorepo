//! Consumer of marshal's total order.

use super::{Block, Mailbox};
use crate::gui::OrderedReporter;
use commonware_actor::Feedback;
use commonware_consensus::{Reporter, multimmit::marshal::Update};
use commonware_runtime::Clock;
use commonware_utils::Acknowledgement as _;
use tracing::debug;

/// Tells the application about each ordered block, then hands the block to the terminal UI or
/// acknowledges it directly.
pub struct OutputReporter<C> {
    application: Mailbox<C>,
    sink: Option<OrderedReporter>,
}

impl<C> Clone for OutputReporter<C> {
    fn clone(&self) -> Self {
        Self {
            application: self.application.clone(),
            sink: self.sink.clone(),
        }
    }
}

impl<C: Clock> OutputReporter<C> {
    /// Creates a reporter that feeds `application` and, when set, the terminal UI's `sink`.
    pub const fn new(application: Mailbox<C>, sink: Option<OrderedReporter>) -> Self {
        Self { application, sink }
    }
}

impl<C: Clock> Reporter for OutputReporter<C> {
    type Activity = Update<Block>;

    fn report(&mut self, activity: Self::Activity) -> Feedback {
        let reference = activity.block.reference();
        debug!(
            index = activity.index.get(),
            chain = reference.chain().get(),
            height = reference.height().get(),
            digest = %reference.digest(),
            "ordered block"
        );
        self.application.ordered(reference);
        match &mut self.sink {
            Some(sink) => sink.report(activity),
            None => {
                let Update {
                    acknowledgement, ..
                } = activity;
                acknowledgement.acknowledge();
                Feedback::Ok
            }
        }
    }
}
