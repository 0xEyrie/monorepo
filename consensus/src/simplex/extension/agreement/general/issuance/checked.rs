//! Reuses immutable application checks without replacing current crypto or fences.
use super::*;
use crate::simplex::extension::agreement::general::{VerifiedBody, normal::Assembly};

impl<S: scheme::Scheme<D>, D: Digest> State<S, D> {
    fn check_body_cap<H: Hasher<Digest = D>>(
        &self,
        body: &OriginBody<S, D>,
        checked: &VerifiedBody<D>,
    ) -> Result<(), Error> {
        self.preflight_body(body)?;
        if body.core != self.core
            || body.decision.slot != self.core.slot
            || body.decision.input != self.input
            || checked.slot() != self.core.slot.id::<H>()
            || checked.decision() != body.decision.id::<H>()
            || checked.body() != body.id::<H>()
            || checked.limits() != self.limits
        {
            return Err(Error::Authority);
        }
        Ok(())
    }

    pub(super) fn checked_route_select<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        body: &OriginBody<S, D>,
        checked: &VerifiedBody<D>,
        strategy: &impl Strategy,
    ) -> Result<Record<D>, Error> {
        self.check_body_cap::<H>(body, checked)?;
        let scope = checked.route_scope().ok_or(Error::Authority)?;
        body.verify_route_selection::<H, R>(
            rng,
            self.context.scheme(),
            &self.core,
            self.input,
            scope,
            self.limits,
            |_| true,
            strategy,
        )?;
        self.selection_record::<H>(body, checked)
    }

    /// Reserves SELECT using a private-constructor full application check.
    /// The existing verifier reauthenticates every original under this owner's
    /// current scheme and rechecks all local signing fences. No peer can decode
    /// the checked token. The caller separately establishes native eligibility.
    pub fn reserve_select_checked<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        body: &OriginBody<S, D>,
        checked: &VerifiedBody<D>,
        strategy: &impl Strategy,
    ) -> Result<Record<D>, Error> {
        if checked.route_scope().is_some() {
            self.active()?;
            let record = self.checked_route_select::<H, R>(rng, body, checked, strategy)?;
            return Ok(self.commit::<H>(record));
        }
        self.check_body_cap::<H>(body, checked)?;
        self.reserve_select::<H, R>(
            rng,
            body,
            |row| contains_row(body, row),
            |rows, candidate| {
                rows.core() == &body.core
                    && rows.input() == body.decision.input
                    && candidate.id::<H>() == checked.body()
            },
            strategy,
        )
    }

    /// Replays the exact SELECT authority after the application has revalidated
    /// its raw body. A same-decision body alias is not its original authority.
    pub fn restore_select_checked<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        record: &Record<D>,
        body: &OriginBody<S, D>,
        checked: &VerifiedBody<D>,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        if !matches!(
            &record.action,
            Action::Reserve {
                message: Message {
                    kind: Kind::Select { .. },
                    ..
                },
                ..
            }
        ) {
            return Err(Error::Authority);
        }
        self.check_body_cap::<H>(body, checked)?;
        self.restore::<H, R>(
            rng,
            record,
            if checked.route_scope().is_some() {
                Material::RouteBody(body, checked)
            } else {
                Material::Body(body)
            },
            |row| contains_row(body, row),
            |rows, candidate| {
                rows.core() == &body.core
                    && rows.input() == body.decision.input
                    && candidate.id::<H>() == checked.body()
            },
            strategy,
        )
    }

    fn check_assembly<R: CryptoRng>(
        &self,
        rng: &mut R,
        checked: &Assembly<S, D>,
        strategy: &impl Strategy,
    ) -> Result<(), Error>
    where
        S::Certificate: super::super::normal::CertificateSigners,
    {
        if checked.core() != &self.core
            || checked.input() != self.input
            || checked.limits() != self.limits
        {
            return Err(Error::Authority);
        }
        self.preflight_origin(checked.origin())?;
        if !checked
            .notarization()
            .verify(rng, self.context.scheme(), strategy)
        {
            return Err(super::super::Error::Signature.into());
        }
        Ok(())
    }

    /// Stages the joint original pair using retained full application meaning.
    /// Current signatures, exact own FIRST/SELECT and local fences are checked
    /// by the existing original-issuance transition, without a replacement policy.
    pub fn reserve_normal_checked<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        checked: &Assembly<S, D>,
        strategy: &impl Strategy,
    ) -> Result<super::super::normal::Reservation<D>, Error>
    where
        S::Certificate: super::super::normal::CertificateSigners,
    {
        self.check_assembly(rng, checked, strategy)?;
        let origin = checked.origin();
        if let Some(cap) = checked.route_authority() {
            self.active()?;
            let agreement = self.route_final::<H, R>(rng, origin, cap, strategy)?;
            return self.reserve_joint::<H>(origin, agreement);
        }
        self.reserve_normal::<H, R>(
            rng,
            origin,
            |row| contains_row(&origin.body, row),
            |rows, body| {
                rows.core() == checked.core()
                    && rows.input() == checked.input()
                    && body.id::<H>() == origin.body.id::<H>()
            },
            strategy,
        )
    }

    /// Restores a joint reservation only from its exact revalidated own Origin.
    /// Current crypto is rechecked even if another scheme admitted the token.
    pub fn restore_normal_checked<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        reservation: &super::super::normal::Reservation<D>,
        checked: &Assembly<S, D>,
        strategy: &impl Strategy,
    ) -> Result<(), Error>
    where
        S::Certificate: super::super::normal::CertificateSigners,
    {
        self.check_assembly(rng, checked, strategy)?;
        let origin = checked.origin();
        if let Some(cap) = checked.route_authority() {
            reservation.check::<H>()?;
            if reservation.subject != super::super::normal::subject::<H>(&origin.body.decision) {
                return Err(Error::Context);
            }
            return self.restore::<H, R>(
                rng,
                &reservation.agreement,
                Material::RouteOrigin(origin, cap),
                |_| false,
                |_, _| false,
                strategy,
            );
        }
        self.restore_normal::<H, R>(
            rng,
            reservation,
            origin,
            |row| contains_row(&origin.body, row),
            |rows, body| {
                rows.core() == checked.core()
                    && rows.input() == checked.input()
                    && body.id::<H>() == origin.body.id::<H>()
            },
            strategy,
        )
    }
}

fn contains_row<S: scheme::Scheme<D>, D: Digest>(body: &OriginBody<S, D>, row: &First<D>) -> bool {
    body.firsts
        .iter()
        .any(|original| matches!(&original.message.kind, Kind::First(first) if first == row))
}
