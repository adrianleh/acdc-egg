use egg::{Analysis, Condition, ConditionEqual, FromOp, Language, Pattern, Var};
use std::sync::Arc;

#[derive(Clone)]
pub struct AndCondition<L, N>
where
    L: Language,
    N: Analysis<L>,
{
    pub c1: Arc<dyn Condition<L, N> + Send + Sync>,
    pub c2: Arc<dyn Condition<L, N> + Send + Sync>,
}

impl<L: Language, N: Analysis<L>> Condition<L, N> for AndCondition<L, N> {
    #[inline]
    fn check(&self, egraph: &mut egg::EGraph<L, N>, id: egg::Id, subst: &egg::Subst) -> bool {
        self.c1.check(egraph, id, subst) && self.c2.check(egraph, id, subst)
    }
    fn vars(&self) -> Vec<Var> {
        let mut vars = self.c1.vars();
        vars.extend(self.c2.vars());
        vars
    }
}

#[derive(Clone)]
pub struct OrCondition<L, N>
where
    L: Language,
    N: Analysis<L>,
{
    pub c1: Arc<dyn Condition<L, N> + Send + Sync>,
    pub c2: Arc<dyn Condition<L, N> + Send + Sync>,
}

impl<L: Language, N: Analysis<L>> Condition<L, N> for OrCondition<L, N> {
    #[inline]
    fn check(&self, egraph: &mut egg::EGraph<L, N>, id: egg::Id, subst: &egg::Subst) -> bool {
        self.c1.check(egraph, id, subst) || self.c2.check(egraph, id, subst)
    }
    fn vars(&self) -> Vec<Var> {
        let mut vars = self.c1.vars();
        vars.extend(self.c2.vars());
        vars
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrueCondition {}

impl<L: Language, N: Analysis<L>> Condition<L, N> for TrueCondition {
    #[inline(always)]
    fn check(&self, _egraph: &mut egg::EGraph<L, N>, _id: egg::Id, _subst: &egg::Subst) -> bool {
        true
    }
    #[inline(always)]
    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FalseCondition {}

impl<L: Language, N: Analysis<L>> Condition<L, N> for FalseCondition {
    #[inline(always)]
    fn check(&self, _egraph: &mut egg::EGraph<L, N>, _id: egg::Id, _subst: &egg::Subst) -> bool {
        false
    }
    #[inline(always)]
    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConditionEqualWrap<L> {
    p1: Pattern<L>,
    p2: Pattern<L>,
}

pub fn to_condition_equal<L>(cew: &ConditionEqualWrap<L>) -> ConditionEqual<L>
where
    L: Clone + Language,
{
    ConditionEqual::new(cew.p1.clone(), cew.p2.clone())
}

impl<L: Language> ConditionEqualWrap<L> {
    /// Create a new [`ConditionEqual`] condition given two patterns.

    #[inline]
    pub fn new(p1: Pattern<L>, p2: Pattern<L>) -> Self {
        ConditionEqualWrap { p1, p2 }
    }
}

impl<L: FromOp> ConditionEqualWrap<L> {
    /// Create a ConditionEqual by parsing two pattern strings.
    ///
    /// This panics if the parsing fails.
    ///
    #[inline]
    pub fn parse(a1: &str, a2: &str) -> Self {
        Self {
            p1: a1.parse().unwrap(),
            p2: a2.parse().unwrap(),
        }
    }
}

pub fn any<L, N>(conds: Vec<Arc<dyn Condition<L, N>  + Send + Sync>>) -> Arc<dyn Condition<L, N> + Send + Sync>
where
    L: Language + 'static,
    N: Analysis<L> + 'static,
{
    conds
        .into_iter()
        .fold(Arc::new(FalseCondition {}), |acc, c| {
            Arc::new(OrCondition { c1: acc, c2: c })
        })
}

pub fn all<L, N>(conds: Vec<Arc<dyn Condition<L, N> + Send + Sync>>) -> Arc<dyn Condition<L, N> + Send + Sync>
where
    L: Language + 'static,
    N: Analysis<L> + 'static,
{
    conds
        .into_iter()
        .fold(Arc::new(TrueCondition {}), |acc, c| {
            Arc::new(AndCondition { c1: acc, c2: c })
        })
}
