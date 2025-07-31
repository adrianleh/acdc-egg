use crate::conv::acdc_to_acdc_zx_or_dim;
use crate::recexpr::recexpr_to_ACDC;
use crate::serialize::Direction::Backward;
use crate::subtrees::rewrite_at_idx;
use crate::vyzxlemma::{LemmaContainer, REVERSE_LEMMA_SUFFIX};
use crate::{ACDC, ACDCTiming};
use egg::{Analysis, EGraph, FlatTerm, Language, RecExpr};
use serde::Serialize as Ser;
use serde::Serializer;
use serde::ser::SerializeStruct;
use serde_derive::{Deserialize, Serialize};
use std::fmt::Debug;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Direction {
    Forward,
    Backward,
}

impl Direction {
    // A method callable on the enum
    fn invert(&self) -> Direction {
        match self {
            Direction::Forward => Direction::Backward,
            Direction::Backward => Direction::Forward,
        }
    }

    fn invert_if(&self, condition: bool) -> Direction {
        if condition {
            self.invert()
        } else {
            self.clone()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Proof {
    pub name: String,
    pub direction: Direction,
}
impl Proof {
    pub fn new(name: String, direction: Direction) -> Self {
        Proof {
            name: name.clone(),
            direction: direction.invert_if(name.ends_with(REVERSE_LEMMA_SUFFIX)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SerFlatTermWrap<'a, A: Analysis<ACDC> + Clone + Debug + 'static> {
    prev_top: RecExpr<ACDC>,
    curr_top: RecExpr<ACDC>,
    term: FlatTerm<ACDC>,
    egraph: &'a EGraph<ACDC, A>,
    container: &'a LemmaContainer<A>,
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
        SerFlatTermWrap {
            prev_top,
            curr_top,
            term: flat_term,
            egraph,
            container: lemmas,
        }
    }

    pub fn children(&self) -> Vec<SerFlatTermWrap<A>> {
        self.term
            .children
            .iter()
            .map(|ft| {
                SerFlatTermWrap::from(
                    self.prev_top.clone(),
                    self.curr_top.clone(),
                    ft.clone(),
                    self.egraph,
                    self.container,
                )
            })
            .collect()
    }

    pub fn get_proof(&self) -> Option<Proof> {
        if self.term.forward_rule.is_some() {
            Some(Proof::new(
                self.term.forward_rule?.to_string(),
                Direction::Forward,
            ))
        } else if self.term.backward_rule.is_some() {
            Some(Proof::new(
                self.term.backward_rule?.to_string(),
                Direction::Backward,
            ))
        } else {
            self.children()
                .iter()
                .flat_map(|c| c.get_proof()) // turn children into an iterator of Option<Proof>
                .next() // get the first non-None proof
        }
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
        let mut state = serializer.serialize_struct("SerFlatTermWrap", 5)?;
        let proof = self.get_proof();
        state.serialize_field("proof", &proof)?;
        let mut arguments = vec![];
        let mut at = None;
        if proof.is_some() {
            let rule_name = &proof.clone().unwrap().name;
            let acdc = &self.term.node;
            let acdczx = acdc_to_acdc_zx_or_dim(acdc, self.egraph);
            let prev = recexpr_to_ACDC(&self.prev_top);
            let new = recexpr_to_ACDC(&self.curr_top);
            if (&prev).is_zx() && (&new).is_zx() {
                let prev = prev.get_zx().unwrap();
                let new = new.get_zx().unwrap();
                if acdczx.is_zx() {
                    let acdczx = &acdczx.get_zx().unwrap();
                    eprintln!(
                        "Getting proof args for {:?} on {:?}",
                        proof.clone().unwrap(),
                        acdczx
                    );
                    let (raw_args, _) = self
                        .container
                        .get_match_side_args(&proof.clone().unwrap(), &acdczx)
                        .or_else(|| Some((vec![], false)))
                        .unwrap();
                    let lemma = self.container.get(&rule_name);
                    if let Some(lemma) = lemma {
                        arguments = lemma.to_ordered_params(&raw_args);
                        eprintln!(
                            "Raw args: {}",
                            raw_args
                                .iter()
                                .map(|p| p.clone().name)
                                .collect::<Vec<_>>()
                                .join(",")
                        );
                        let subtree = lemma.build_subtree_from_application(
                            &acdczx,
                            proof.unwrap().direction != Backward,
                        );
                        eprintln!("Rewrite at idx for {}", rule_name);
                        let (idx, has_idx) = rewrite_at_idx(&prev, &new, &subtree);
                        if has_idx {
                            at = Some(idx);
                        }
                    }
                }
            }
        }
        state.serialize_field("arguments", &arguments)?;
        state.serialize_field("node", &recexpr_to_ACDC(&self.curr_top).get_zx())?;
        state.serialize_field("prev", &recexpr_to_ACDC(&self.prev_top).get_zx())?;
        state.serialize_field("at", &at)?;
        state.end()
    }
}

#[derive(Debug, Clone)]
pub struct ACDCResult<'a, T>
where
    T: Analysis<ACDC> + Clone + Debug + 'static,
{
    expl: Vec<SerFlatTermWrap<'a, T>>,
    timing: ACDCTiming,
}

impl<'a, T: Analysis<ACDC> + Clone + Debug + 'static> ACDCResult<'a, T> {
    pub fn new(expl: Vec<SerFlatTermWrap<'a, T>>, timing: ACDCTiming) -> Self {
        ACDCResult {
            expl,
            timing
        }
    }
}   

impl<'a, T: Analysis<ACDC> + Clone + Debug + 'static> Ser for ACDCResult<'a, T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("Result", 3)?;
        state.serialize_field("expl", &self.expl)?;
        state.serialize_field("expl_time", &self.timing)?;
        state.end()
    }
}
