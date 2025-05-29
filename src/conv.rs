use crate::{ACDC, ACDCDim, ACDCZX, ZXOrDim};
use egg::EGraph;
use serde_derive::{Deserialize, Serialize};
use std::fmt::Debug;

macro_rules! acdc_to_binop_dim {
    ($c:ident,$ids:ident,$egraph:ident) => {{
        let mut dims = vec![];
        for id in $ids {
            let node = $egraph.id_to_node(*id);
            let dim = acdc_to_acdc_zx_or_dim(node, $egraph).get_dim()
                .or_else(|| panic!("Type error: binop points to ZX"))
                .unwrap();
            dims.push(dim);
        }
        assert_eq!(dims.len(), 2);
        ZXOrDimOrEither::Dim(ACDCDim::$c {
            a: Box::from(dims[0].clone()),
            b: Box::from(dims[1].clone()),
        })
    }};
}
macro_rules! acdc_to_binop_zx {
    ($c:ident,$ids:ident,$egraph:ident) => {{
        let mut dims = vec![];
        for id in $ids {
            let node = $egraph.id_to_node(*id);
            let dim = acdc_to_acdc_zx_or_dim(node, $egraph).get_zx()
                .or_else(|| panic!("Type error: binop points to Dim"))
                .unwrap();
            dims.push(dim);
        }
        assert_eq!(dims.len(), 2);
        ZXOrDimOrEither::ZX(ACDCZX::$c {
            a: Box::from(dims[0].clone()),
            b: Box::from(dims[1].clone()),
        })
    }};
}

macro_rules! acdc_to_dep {
    ($dep:ident,$id:ident,$egraph:ident) => {{
        let node = $egraph.id_to_node(*$id);
        let zx = acdc_to_acdc_zx_or_dim(node, $egraph).get_zx()
            .or_else(|| panic!("Type error: Dep points to Dim"))
            .unwrap();
        ZXOrDimOrEither::Dim(ACDCDim::$dep { zx: Box::from(zx) })
    }};
}

macro_rules! acdc_to_spider {
    ($c:ident,$ids:ident,$egraph:ident) => {{
        let mut dims = vec![];
        for id in $ids {
            let node = $egraph.id_to_node(*id);
            let dim = acdc_to_acdc_zx_or_dim(node, $egraph).get_dim()
                .or_else(|| panic!("Type error: spider points to ZX"))
                .unwrap();
            dims.push(dim);
        }
        assert_eq!(dims.len(), 3);
        ZXOrDimOrEither::ZX(ACDCZX::$c {
            n: dims[0].clone(),
            m: dims[1].clone(),
            alpha: dims[2].clone(),
        })
    }};
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(untagged)]
pub enum ZXOrDimOrEither {
    ZX(ACDCZX),
    Dim(ACDCDim),
    Either(ACDCZX, ACDCDim),
}


impl ZXOrDimOrEither {
    #[inline]
    pub fn get_zx(self: &ZXOrDimOrEither) -> Option<ACDCZX> {
        match self {
            ZXOrDimOrEither::ZX(zx) => Some(zx.clone()),
            ZXOrDimOrEither::Dim(_) => None,
            ZXOrDimOrEither::Either(zx, _) => Some(zx.clone()),
        }
    }

    #[inline]
    pub fn get_dim(self: &ZXOrDimOrEither) -> Option<ACDCDim> {
        match self {
            ZXOrDimOrEither::ZX(_) => None,
            ZXOrDimOrEither::Dim(dim) => Some(dim.clone()),
            ZXOrDimOrEither::Either(_, dim) => Some(dim.clone()),
        }
    }


    #[inline]
    pub fn is_dim(self: &ZXOrDimOrEither) -> bool {
        match self {
            ZXOrDimOrEither::ZX(_) => false,
            ZXOrDimOrEither::Dim(_) => true,
            ZXOrDimOrEither::Either(_, _) => true,
        }
    }

    #[inline]
    pub fn is_zx(self: &ZXOrDimOrEither) -> bool {
        match self {
            ZXOrDimOrEither::ZX(_) => true,
            ZXOrDimOrEither::Dim(_) => false,
            ZXOrDimOrEither::Either(_, _) => true,
        }
    }

    pub fn to_zx_or_dim(self: &ZXOrDimOrEither, prio_dim: bool) -> ZXOrDim {
        match self {
            ZXOrDimOrEither::ZX(zx) => ZXOrDim::ZX(zx.clone()),
            ZXOrDimOrEither::Dim(dim) => ZXOrDim::Dim(dim.clone()),
            ZXOrDimOrEither::Either(zx, dim) => {
                if prio_dim {
                    ZXOrDim::Dim(dim.clone())
                } else {
                    ZXOrDim::ZX(zx.clone())
                }
            }
        }
    }

}




pub fn acdc_to_acdc_zx_or_dim<T>(acdc: &ACDC, egraph: &EGraph<ACDC, T>) -> ZXOrDimOrEither
where
    T: egg::Analysis<ACDC> + 'static + Clone + Debug,
{
    match acdc {
        ACDC::Lit(lit) => ZXOrDimOrEither::Dim(ACDCDim::Lit { lit: *lit }),
        ACDC::Add(ids) => {
            acdc_to_binop_dim!(Add, ids, egraph)
        }
        ACDC::Sub(ids) => {
            acdc_to_binop_dim!(Sub, ids, egraph)
        }
        ACDC::Mul(ids) => {
            acdc_to_binop_dim!(Mul, ids, egraph)
        }
        ACDC::Dep1(id) => {
            acdc_to_dep!(Dep1, id, egraph)
        }
        ACDC::Dep2(id) => {
            acdc_to_dep!(Dep2, id, egraph)
        }
        ACDC::Var(symbol) => ZXOrDimOrEither::Either(
            ACDCZX::Val {
                val: symbol.to_string(),
                n: None,
                m: None,
            },
            ACDCDim::Symbol {
                symbol: symbol.to_string(),
            },
        ),
        ACDC::Cast(ids) => {
            let n = egraph.id_to_node(ids[0]);
            let m = egraph.id_to_node(ids[1]);
            let zx = egraph.id_to_node(ids[2]);
            let n = acdc_to_acdc_zx_or_dim(n, egraph).get_dim()
                .or_else(|| panic!("Type error: Cast n points to ZX"))
                .unwrap();
            let m = acdc_to_acdc_zx_or_dim(m, egraph).get_dim()
                .or_else(|| panic!("Type error: Cast m points to ZX"))
                .unwrap();
            let zx = acdc_to_acdc_zx_or_dim(zx, egraph).get_zx()
                .or_else(|| panic!("Type error: Cast zx points to Dim"))
                .unwrap();
            ZXOrDimOrEither::ZX(ACDCZX::Cast {
                n,
                m,
                zx: Box::from(zx),
            })
        }
        ACDC::Stack(ids) => {
            acdc_to_binop_zx!(Stack, ids, egraph)
        }
        ACDC::Compose(ids) => {
            acdc_to_binop_zx!(Compose, ids, egraph)
        }
        ACDC::Val(ids) => {
            let mut dims = vec![];
            for id in ids {
                let node = egraph.id_to_node(*id);
                let dim = acdc_to_acdc_zx_or_dim(node, egraph).get_dim()
                    .or_else(|| panic!("Type error: Val points to ZX"))
                    .unwrap();
                dims.push(dim);
            }
            assert_eq!(dims.len(), 3);
            let val = match &dims[2] {
                ACDCDim::Symbol { symbol } => { symbol.clone() }
                _ => "_".to_string()
            };
            ZXOrDimOrEither::ZX(ACDCZX::Val {
                n: Some(dims[0].clone()),
                m: Some(dims[1].clone()),
                val
            })
        }
        ACDC::Z(ids) => {
            acdc_to_spider!(Z, ids, egraph)
        }
        ACDC::X(ids) => {
            acdc_to_spider!(X, ids, egraph)
        }
        ACDC::NWire(id) => {
            let node = egraph.id_to_node(*id);
            let dim = &acdc_to_acdc_zx_or_dim(node, egraph).get_dim()
                .or_else(|| panic!("Type error: NWire points to ZX"))
                .unwrap();
            ZXOrDimOrEither::ZX(ACDCZX::NWire { n: dim.clone() })
        }
        ACDC::Fn(fn_name, args) => {
            let args = args
                .iter()
                .map(|id| egraph.id_to_node(*id))
                .map(|acdc| acdc_to_acdc_zx_or_dim(acdc, egraph))
                .collect::<Vec<_>>();
            let all_dims = (&args).iter().fold(true, |acc, arg| acc && arg.is_dim());
            let zx_or_dim_args = (&args).iter().map(|arg| arg.to_zx_or_dim(false)).collect();
            if !all_dims {
                return ZXOrDimOrEither::ZX(ACDCZX::Fn {
                    fn_name: fn_name.to_string(),
                    args: zx_or_dim_args,
                });
            }
            let dim_args = (&args).iter().map(|arg| arg.get_dim().unwrap()).collect();
            ZXOrDimOrEither::Either(
                ACDCZX::Fn {
                    fn_name: fn_name.to_string(),
                    args: zx_or_dim_args,
                },
                ACDCDim::Fn {
                    fn_name: fn_name.to_string(),
                    args: dim_args,
                },
            )
        }
    }
}
