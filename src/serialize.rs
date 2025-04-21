use crate::{ACDC, ACDCZX};
use crate::vyzxlemma::{Lemma, LemmaContainer, REVERSE_LEMMA_SUFFIX};
use egg::{Analysis, EGraph, FlatTerm, Id, Language, RecExpr};
use crate::conv::{acdc_to_acdc_zx_or_dim};
use serde::ser::SerializeStruct;
use serde::Serialize as Ser;
use serde::Serializer;
use std::fmt::Debug;
use crate::recexpr::{recexpr_to_ACDC};
use crate::subtrees::rewrite_at_idx;

#[derive(Debug, Clone)]
pub struct SerFlatTermWrap<'a, A: Analysis<ACDC> + Clone + Debug + 'static> {
    prev_top: RecExpr<ACDC>,
    curr_top: RecExpr<ACDC>,
    term : FlatTerm<ACDC>,
    egraph: & 'a EGraph<ACDC, A>,
    container: & 'a LemmaContainer<A>,
}

#[derive(Debug, Clone)]
pub struct SerADCDWrap<'a, A: Analysis<ACDC> + Clone + Debug + 'static>(ACDC, &'a EGraph<ACDC, A>);

impl<'a, A: Analysis<ACDC> + Clone + Debug + 'static> ToSer<'a, SerADCDWrap<'a, A>, ACDC, A>
    for ACDC
{
    fn to_ser(&self, egraph: &'a EGraph<ACDC, A>) -> SerADCDWrap<'a, A> {
        SerADCDWrap(self.clone(), egraph)
    }
}

#[derive(Clone, Debug)]
pub struct SizedZX<'a, A: Analysis<ACDC> + Clone + Debug + 'static> {
    pub n: SerADCDWrap<'a, A>,
    pub m: SerADCDWrap<'a, A>,
}

impl<'a, A: Analysis<ACDC> + Clone + Debug> Ser for SizedZX<'a, A> {
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
        $state = $serializer.serialize_struct("ACDC", 5)?;
        ser_type!("spider", $state);
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

impl<'a, A: Analysis<ACDC> + Clone + Debug> Ser for SerADCDWrap<'a, A> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        acdc_to_acdc_zx_or_dim::<A>(&self.0, self.1).serialize(serializer)
        // #[inline(always)]
        // fn id_to_ser_acdc_warp<A: Analysis<ACDC>>(
        //     egraph: &EGraph<ACDC, A>,
        //     id: Id,
        // ) -> SerADCDWrap<A> {
        //     egraph.id_to_node(id).to_ser(egraph)
        // }
        // let mut state: <S as Serializer>::SerializeStruct;
        // match &self.0 {
        //     ACDC::Lit(lit) => {
        //         state = serializer.serialize_struct("ACDC", 2)?;
        //         ser_type!("const", state);
        //         state.serialize_field("lit", &lit)?;
        //     }
        //     ACDC::Add(ids) => {
        //         state = serializer.serialize_struct("ACDC", 3)?;
        //         ser_type!("+", state);
        //         serialize_bin_ops!(state, self, ids);
        //     }
        //     ACDC::Sub(ids) => {
        //         state = serializer.serialize_struct("ACDC", 3)?;
        //         ser_type!("-", state);
        //         serialize_bin_ops!(state, self, ids);
        //     }
        //     ACDC::Mul(ids) => {
        //         state = serializer.serialize_struct("ACDC", 3)?;
        //         ser_type!("*", state);
        //         serialize_bin_ops!(state, self, ids);
        //     }
        //     ACDC::Dep1(id) => {
        //         state = serializer.serialize_struct("ACDC", 2)?;
        //         ser_type!("dep1", state);
        //         state.serialize_field("of", &id_to_ser_acdc_warp(self.1, *id))?;
        //     }
        //     ACDC::Dep2(id) => {
        //         state = serializer.serialize_struct("ACDC", 2)?;
        //         ser_type!("dep2", state);
        //         state.serialize_field("of", &id_to_ser_acdc_warp(self.1, *id))?;
        //     }
        //     ACDC::Var(s) => {
        //         state = serializer.serialize_struct("ACDC", 2)?;
        //         ser_type!("symbol", state);
        //         state.serialize_field("symbol", s.as_str())?;
        //     }
        //     ACDC::Cast(ids) => {
        //         state = serializer.serialize_struct("ACDC", 4)?;
        //         ser_type!("cast", state);
        //         state.serialize_field("n", &id_to_ser_acdc_warp(self.1, ids[0]))?;
        //         state.serialize_field("m", &id_to_ser_acdc_warp(self.1, ids[1]))?;
        //         state.serialize_field("zx", &id_to_ser_acdc_warp(self.1, ids[2]))?;
        //     }
        //     ACDC::Stack(ids) => {
        //         state = serializer.serialize_struct("ACDC", 3)?;
        //         ser_type!("stack", state);
        //         serialize_bin_ops!(state, self, ids);
        //     }
        //     ACDC::Compose(ids) => {
        //         state = serializer.serialize_struct("ACDC", 3)?;
        //         ser_type!("compose", state);
        //         serialize_bin_ops!(state, self, ids);
        //     }
        //     ACDC::Val(ids) => {
        //         state = serializer.serialize_struct("ACDC", 3)?;
        //         ser_type!("symbol", state);
        //         state.serialize_field(
        //             "size",
        //             &SizedZX {
        //                 n: id_to_ser_acdc_warp(self.1, ids[0]),
        //                 m: id_to_ser_acdc_warp(self.1, ids[1]),
        //             },
        //         )?;
        //         state.serialize_field("val", &id_to_ser_acdc_warp(self.1, ids[2]))?;
        //     }
        //     ACDC::Z(ids) => {
        //         serialize_spider!(state, self, ids, "z", serializer);
        //     }
        //     ACDC::X(ids) => {
        //         serialize_spider!(state, self, ids, "x", serializer);
        //     }
        //     ACDC::NWire(id) => {
        //         state = serializer.serialize_struct("ACDC", 2)?;
        //         ser_type!("n_wire", state);
        //         state.serialize_field("n", &id_to_ser_acdc_warp(self.1, *id))?;
        //     }
        //     ACDC::Fn(fn_name, ids) => {
        //         let args: Vec<SerADCDWrap<'a, A>> = ids
        //             .iter()
        //             .map(|id| id_to_ser_acdc_warp(self.1, *id))
        //             .collect();
        //         state = serializer.serialize_struct("ACDC", 3)?;
        //         ser_type!("fn", state);
        //         state.serialize_field("fn_name", fn_name.as_str())?;
        //         state.serialize_field("args", &args)?;
        //     }
        // }
        // state.end()
    }
}

trait ToSer<'a, S, L: Language, A: Analysis<L>>
where
    S: Ser,
{
    fn to_ser(&self, egraph: &'a EGraph<L, A>) -> S;
}

impl<'a, A: Analysis<ACDC> + Clone + Debug> SerFlatTermWrap<'a, A> {
    pub fn from(
        prev_top: RecExpr<ACDC>,
        curr_top: RecExpr<ACDC>,
        flat_term: FlatTerm<ACDC>,
        egraph: &'a EGraph<ACDC, A>,
        lemmas: &'a LemmaContainer<A>,
    ) -> Self {
        SerFlatTermWrap { prev_top,curr_top, term: flat_term, egraph, container: lemmas}
    }

    pub fn children(&self) -> Vec<SerFlatTermWrap<A>> {
        self.term
            .children
            .iter()
            .map(|ft| SerFlatTermWrap::from(self.prev_top.clone(),self.curr_top.clone(), ft.clone(),self.egraph,self.container ))
            .collect()
    }

    fn contains_proof(&self) -> bool {
        self.term.forward_rule.is_some()
            || self.term.backward_rule.is_some()
            || self.children().iter().any(|child| child.contains_proof())
    }

    pub fn non_empty_children(&self) -> Vec<SerFlatTermWrap<A>> {
        self.children()
            .into_iter()
            .filter(|child| child.contains_proof())
            .collect::<Vec<_>>()
    }
}

// impl<L: Language + 'static + ToSer<T, L, A>, A: Analysis<L>, T: Ser> Ser
//     for SerFlatTermWrap<L, A> - Weird rust typing reasons make this not work
impl<'a, A: Analysis<ACDC> + Clone + Debug> Ser for SerFlatTermWrap<'a, A> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let fwd_rule = &self.term.forward_rule.map(|x| x.to_string());
        let bwd_rule = &self.term.backward_rule.map(|x| x.to_string());
        if !self.contains_proof() {
            let mut state = serializer.serialize_struct("SerFlatTermWrap", 0)?;
            return state.end();
        }
        let mut state = serializer.serialize_struct("SerFlatTermWrap", 5)?;
        state.serialize_field("backward_rule", bwd_rule)?;
        state.serialize_field("forward_rule", fwd_rule)?;
        state.serialize_field("children", &self.non_empty_children())?;
        let mut arguments = vec![];
        let mut at = None;
        if bwd_rule.is_some() || fwd_rule.is_some() {
            let rule_name = bwd_rule.clone().or_else(|| fwd_rule.clone()).unwrap();
            let acdc = &self.term.node;
            let acdczx = acdc_to_acdc_zx_or_dim(acdc, self.egraph);
            let prev = recexpr_to_ACDC(&self.prev_top);
            let new = recexpr_to_ACDC(&self.curr_top);
            assert!(&prev.is_zx());
            assert!(&new.is_zx());
            let prev = prev.get_zx().unwrap();
            let new = new.get_zx().unwrap();
            if acdczx.is_zx() {
                let acdczx = &acdczx.get_zx().unwrap();
                let (raw_args, rhs) = self
                    .container
                    .get_match_side_args(&rule_name,&acdczx )
                    .or_else(|| Some((vec![], false)))
                    .unwrap();
                let lemma=self.container.get(&rule_name);
                if let Some(lemma) = lemma {
                    arguments= lemma.to_ordered_params(&raw_args);
                    eprintln!("Raw args: {}",raw_args.iter().map(|p|p.clone().name).collect::<Vec<_>>().join(","));
                    let subtree = lemma.build_subtree_from_application(&acdczx);
                    eprintln!("Rewrite at idx for {}", rule_name);
                    let (idx, has_idx) = rewrite_at_idx(&prev, &new, &subtree);
                    if has_idx { at = Some(idx); }
                }
            }
        }
        state.serialize_field("arguments", &arguments)?;
        state.serialize_field("node", &recexpr_to_ACDC(&self.curr_top).get_zx())?;
        state.serialize_field("at", &at)?;
        state.end()
    }
}
