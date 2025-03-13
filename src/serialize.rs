use crate::ACDC;
use egg::{Analysis, EGraph, FlatTerm, Id, Language};
use serde::Serialize as Ser;
use serde::Serializer;
use serde::ser::SerializeStruct;
use serde_derive::{Deserialize, Serialize};

#[derive(Debug, Clone)]
pub struct SerFlatTermWrap<'a, L: Language + 'static, A: Analysis<L> + 'static>(
    FlatTerm<L>,
    &'a EGraph<L, A>,
);

#[derive(Debug, Clone)]
pub struct SerADCDWrap<'a, A: Analysis<ACDC> + 'static>(ACDC, &'a EGraph<ACDC, A>);

impl<'a, A: Analysis<ACDC> + 'static> ToSer<'a, SerADCDWrap<'a, A>, ACDC, A> for ACDC {
    fn to_ser(&self, egraph: &'a EGraph<ACDC, A>) -> SerADCDWrap<'a, A> {
        SerADCDWrap(self.clone(), egraph)
    }
}

#[derive(Clone, Debug)]
pub struct SizedZX<'a, A: Analysis<ACDC> + 'static> {
    pub n: SerADCDWrap<'a, A>,
    pub m: SerADCDWrap<'a, A>,
}

impl<'a, A: Analysis<ACDC>> Ser for SizedZX<'a, A> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("SizedZX", 2)?;
        state.serialize_field("n", &self.n)?;
        state.serialize_field("m", &self.m)?;
        state.end()
    }
}

macro_rules! serialize_bin_ops {
    ($state:expr, $self:expr, $ids:expr) => {
        $state.serialize_field("a", &id_to_ser_acdc_warp($self.1, $ids[0]))?;
        $state.serialize_field("b", &id_to_ser_acdc_warp($self.1, $ids[0]))?;
    };
}

macro_rules! serialize_spider {
    ($state:expr, $self:expr, $ids:expr, $color:expr, $serializer:expr) => {
        $state = $serializer.serialize_struct("ACDC",5)?;
        ser_type!("spider",$state);
        $state.serialize_field("color", $color)?;
        $state.serialize_field("n", &id_to_ser_acdc_warp($self.1, $ids[0]))?;
        $state.serialize_field("m", &id_to_ser_acdc_warp($self.1, $ids[1]))?;
        $state.serialize_field("alpha", &id_to_ser_acdc_warp($self.1, $ids[2]))?;
    };
}

macro_rules! ser_type {
    ($t:expr, $state:expr) => {
       $state.serialize_field("type", $t)?;
    };
}

impl<'a, A: Analysis<ACDC>> Ser for SerADCDWrap<'a, A> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        #[inline(always)]
        fn id_to_ser_acdc_warp<A: Analysis<ACDC>>(
            egraph: &EGraph<ACDC, A>,
            id: Id,
        ) -> SerADCDWrap<A> {
            egraph.id_to_node(id).to_ser(egraph)
        }
        let mut state: <S as Serializer>::SerializeStruct;
        match &self.0 {
            ACDC::Lit(lit) => {
                state = serializer.serialize_struct("ACDC",2)?;
                ser_type!("const",state);
                state.serialize_field("lit", &lit)?;
            }
            ACDC::Add(ids) => {
                state = serializer.serialize_struct("ACDC",3)?;
                ser_type!("+",state);
                serialize_bin_ops!(state, self, ids);
            }
            ACDC::Sub(ids) => {
                state = serializer.serialize_struct("ACDC",3)?;
                ser_type!("-",state);
                serialize_bin_ops!(state, self, ids);
            }
            ACDC::Mul(ids) => {
                state = serializer.serialize_struct("ACDC",3)?;
                ser_type!("*",state);
                serialize_bin_ops!(state, self, ids);
            }
            ACDC::Dep1(id) => {
                state = serializer.serialize_struct("ACDC",2)?;
                ser_type!("dep1",state);
                state.serialize_field("of", &id_to_ser_acdc_warp(self.1, *id))?;
            }
            ACDC::Dep2(id) => {
                state = serializer.serialize_struct("ACDC",2)?;
                ser_type!("dep2",state);
                state.serialize_field("of", &id_to_ser_acdc_warp(self.1, *id))?;
            }
            ACDC::Var(s) => {
                state = serializer.serialize_struct("ACDC",2)?;
                ser_type!("symbol",state);
                state.serialize_field("symbol", s.as_str())?;
            }
            ACDC::Cast(ids) => {
                state = serializer.serialize_struct("ACDC",4)?;
                ser_type!("cast",state);
                state.serialize_field("n", &id_to_ser_acdc_warp(self.1, ids[0]))?;
                state.serialize_field("m", &id_to_ser_acdc_warp(self.1, ids[1]))?;
                state.serialize_field("zx", &id_to_ser_acdc_warp(self.1, ids[2]))?;
            }
            ACDC::Stack(ids) => {
                state = serializer.serialize_struct("ACDC",3)?;
                ser_type!("stack",state);
                serialize_bin_ops!(state, self, ids);
            }
            ACDC::Compose(ids) => {
                state = serializer.serialize_struct("ACDC",3)?;
                ser_type!("compose",state);
                serialize_bin_ops!(state, self, ids);
            }
            ACDC::Val(ids) => {
                state = serializer.serialize_struct("ACDC",3)?;
                ser_type!("symbol",state);
                state.serialize_field(
                    "size",
                    &SizedZX {
                        n: id_to_ser_acdc_warp(self.1, ids[0]),
                        m: id_to_ser_acdc_warp(self.1, ids[1]),
                    },
                )?;
                state.serialize_field("val", &id_to_ser_acdc_warp(self.1, ids[2]))?;
            }
            ACDC::Z(ids) => {
                serialize_spider!(state, self, ids, "z", serializer);
            }
            ACDC::X(ids) => {
                serialize_spider!(state, self, ids, "x", serializer);
            }
            ACDC::NWire(id) => {
                state = serializer.serialize_struct("ACDC",2)?;
                ser_type!("n_wire",state);
                state.serialize_field("n", &id_to_ser_acdc_warp(self.1, *id))?;
            }
            ACDC::Fn(fn_name, ids) => {
                let args: Vec<SerADCDWrap<'a, A>> = ids
                    .iter()
                    .map(|id| id_to_ser_acdc_warp(self.1, *id))
                    .collect();
                state = serializer.serialize_struct("ACDC",3)?;
                ser_type!("fn",state);
                state.serialize_field("fn_name", fn_name.as_str())?;
                state.serialize_field("args", &args)?;
            }
        }
        state.end()
    }
}

trait ToSer<'a, S, L: Language, A: Analysis<L>>
where
    S: Ser,
{
    fn to_ser(&self, egraph: &'a EGraph<L, A>) -> S;
}

impl<'a, L: Language + 'static, A: Analysis<L>> SerFlatTermWrap<'a, L, A> {
    pub fn from(flat_term: FlatTerm<L>, egraph: &'a EGraph<L, A>) -> Self {
        SerFlatTermWrap(flat_term, egraph)
    }

    pub fn children(&self) -> Vec<SerFlatTermWrap<L, A>> {
        self.0
            .children
            .iter()
            .map(|ft| SerFlatTermWrap::from(ft.clone(), self.1))
            .collect()
    }
}

// impl<L: Language + 'static + ToSer<T, L, A>, A: Analysis<L>, T: Ser> Ser
//     for SerFlatTermWrap<L, A> - Weird rust typing reasons make this not work
impl<'a, A: Analysis<ACDC>> Ser for SerFlatTermWrap<'a, ACDC, A> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let fwd_rule = &self.0.forward_rule.map(|x| x.to_string());
        let bwd_rule = &self.0.backward_rule.map(|x| x.to_string());
        let mut state = serializer.serialize_struct("SerFlatTermWrap", 4)?;
        state.serialize_field("node", &self.0.node.to_ser(self.1))?;
        state.serialize_field("backward_rule", bwd_rule)?;
        state.serialize_field("forward_rule", fwd_rule)?;
        state.serialize_field("children", &self.children())?;
        state.end()
    }
}
