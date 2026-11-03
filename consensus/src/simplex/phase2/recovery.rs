//! Journal records and local fences for the native extension slow path.
//! No record is a certificate, leader authorization or durable publication ACK.
use crate::{
    Epochable, Viewable,
    types::{Epoch, View},
};
use bytes::BufMut;
use commonware_codec::{Buf, EncodeSize, Error, Read, Write};

/// Uninhabited recovery record for stock Simplex; it has no wire encoding.
#[derive(Clone, Debug, PartialEq)]
pub enum NoRecovery {}
impl Write for NoRecovery {
    fn write(&self, _: &mut impl BufMut) {
        match *self {}
    }
}
impl EncodeSize for NoRecovery {
    fn encode_size(&self) -> usize {
        match *self {}
    }
}
impl Read for NoRecovery {
    type Cfg = ();
    fn read_cfg(_: &mut impl Buf, _: &()) -> Result<Self, Error> {
        Err(Error::Invalid("simplex recovery", "disabled mode"))
    }
}
impl Epochable for NoRecovery {
    fn epoch(&self) -> Epoch {
        match *self {}
    }
}
impl Viewable for NoRecovery {
    fn view(&self) -> View {
        match *self {}
    }
}
#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for NoRecovery {
    fn arbitrary(_: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Err(arbitrary::Error::IncorrectFormat)
    }
}

commonware_macros::stability_scope!(ALPHA {
    use crate::simplex::{extension::vote::Statement,types::Proposal};
    use crate::types::Round;
    use commonware_cryptography::Digest;
    use commonware_codec::ReadExt as _;

    /// A local decision in the same journal as the original native votes.
    /// The voter must synchronize the record before publishing a status or vote.
    #[derive(Clone, Debug, PartialEq)]
    pub enum Record<D:Digest> {
        /// Frozen full acceptance before entering a strictly later ballot.
        Promise { proposal:Proposal<D>, domain:D, ballot:Round, accepted:Option<Statement<D>> },
        /// Exact later-ballot subject authorized by a verified status proof.
        /// Native ancestry and application validity must also be checked by the caller.
        Accept(Statement<D>),
    }
    impl<D:Digest> Record<D> {
        pub const fn proposal(&self)->&Proposal<D> {match self {Self::Promise{proposal,..}=>proposal,Self::Accept(s)=>&s.proposal}}
        pub const fn domain(&self)->D {match self {Self::Promise{domain,..}=>*domain,Self::Accept(s)=>s.domain}}
        pub const fn ballot(&self)->Round {match self {Self::Promise{ballot,..}=>*ballot,Self::Accept(s)=>s.ballot}}
    }
    impl<D:Digest> Epochable for Record<D> {fn epoch(&self)->Epoch {self.proposal().round.epoch()}}
    impl<D:Digest> Viewable for Record<D> {fn view(&self)->View {self.proposal().round.view()}}
    impl<D:Digest> Write for Record<D> {
        fn write(&self,b:&mut impl BufMut) {match self {
            Self::Promise{proposal,domain,ballot,accepted}=>{0u8.write(b);proposal.write(b);domain.write(b);ballot.write(b);accepted.write(b);}
            Self::Accept(s)=>{1u8.write(b);s.write(b);}
        }}
    }
    impl<D:Digest> EncodeSize for Record<D> {
        fn encode_size(&self)->usize {1+match self {
            Self::Promise{proposal,domain,ballot,accepted}=>proposal.encode_size()+domain.encode_size()+ballot.encode_size()+accepted.encode_size(),
            Self::Accept(s)=>s.encode_size(),
        }}
    }
    impl<D:Digest> Read for Record<D> {
        type Cfg=();
        fn read_cfg(b:&mut impl Buf,_:&())->Result<Self,Error> {match u8::read(b)? {
            0=>Ok(Self::Promise{proposal:Proposal::read(b)?,domain:D::read(b)?,ballot:Round::read(b)?,accepted:Option::<Statement<D>>::read(b)?}),
            1=>Ok(Self::Accept(Statement::read(b)?)),
            _=>Err(Error::Invalid("simplex recovery record","unknown kind")),
        }}
    }
    #[cfg(feature="arbitrary")]
    impl<'a,D:Digest+for<'b> arbitrary::Arbitrary<'b>> arbitrary::Arbitrary<'a> for Record<D> {
        fn arbitrary(u:&mut arbitrary::Unstructured<'a>)->arbitrary::Result<Self>{
            Ok(if u.arbitrary()? {Self::Accept(u.arbitrary()?)} else {Self::Promise{proposal:u.arbitrary()?,domain:u.arbitrary()?,ballot:u.arbitrary()?,accepted:u.arbitrary()?}})
        }
    }
    /// Native round-local replay state. Application callbacks cannot clear it.
    #[derive(Clone, Debug, Default)]
    pub struct State<D:Digest> {
        promise:Option<Record<D>>,
        accepted:Option<Statement<D>>,
    }
    impl<D:Digest> State<D> {
        pub const EMPTY:Self=Self{promise:None,accepted:None};
        pub const fn allows_original(&self)->bool {self.promise.is_none()}
        pub fn accepted<'a>(&'a self,original:Option<&'a Statement<D>>)->Option<&'a Statement<D>> {self.accepted.as_ref().or(original)}
        pub const fn promise(&self)->Option<&Record<D>> {self.promise.as_ref()}
        /// Checks transition consistency. A status proof and native eligibility
        /// remain prerequisites before staging a live acceptance.
        pub fn apply(&mut self, original:Option<&Statement<D>>,record:&Record<D>)->bool {
            let p=record.proposal();let ballot=record.ballot();
            if ballot.epoch()!=p.round.epoch() || ballot.view()<=p.round.view() {return false;}
            if let Some(old)=&self.promise {
                if old.proposal()!=p || old.domain()!=record.domain() || old.ballot()>ballot {return false;}
                if matches!(record,Record::Promise{..}) && old.ballot()==ballot {return old==record;}
            }
            match record {
                Record::Promise{accepted,..}=>{
                    if accepted.as_ref()!=self.accepted(original) {return false;}
                    if accepted.as_ref().is_some_and(|s|s.proposal!=*p || s.domain!=record.domain() || s.ballot>=ballot) {return false;}
                    self.promise=Some(record.clone());true
                }
                Record::Accept(s)=>{
                    if self.promise.as_ref().is_none_or(|r|r.ballot()!=ballot) {return false;}
                    if let Some(old)=self.accepted(original) && old.ballot==ballot {return old==s;}
                    self.accepted=Some(s.clone());true
                }
            }
        }
    }
});
