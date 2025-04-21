use crate::conv::ZXOrDimOrEither;
use crate::{ACDC, ACDCDim, ACDCZX};
use egg::{Id, RecExpr};
use std::ops::Index;

macro_rules! binop_to_dim {
    ($op:ident, $rec_expr:expr, $a:expr, $b:expr) => {{
        let a = recexpr_to_ACDC_at($rec_expr, *$a).get_dim().unwrap();
        let b = recexpr_to_ACDC_at($rec_expr, *$b).get_dim().unwrap();
        ZXOrDimOrEither::Dim(ACDCDim::$op {
            a: Box::from(a),
            b: Box::from(b),
        })
    }};
}

macro_rules! binop_to_zx {
    ($op:ident, $rec_expr:expr, $a:expr, $b:expr) => {{
        let a = recexpr_to_ACDC_at($rec_expr, *$a).get_zx().unwrap();
        let b = recexpr_to_ACDC_at($rec_expr, *$b).get_zx().unwrap();
        ZXOrDimOrEither::ZX(ACDCZX::$op {
            a: Box::from(a),
            b: Box::from(b),
        })
    }};
}

fn get_val_name(zx_dim: &ZXOrDimOrEither) -> String {
    if zx_dim.is_zx() {
        match zx_dim.get_zx().unwrap() {
            ACDCZX::Val { val, n: _, m: _ } => val,
            _ => panic!("Not a string"),
        }
    } else {
        match zx_dim.get_dim().unwrap() {
            ACDCDim::Symbol { symbol } => symbol,
            _ => panic!("Not a string"),
        }
    };
}

fn recexpr_to_ACDC_at(rec_expr: &RecExpr<ACDC>, i: Id) -> ZXOrDimOrEither {
    let curr = rec_expr.index(i);
    match curr {
        ACDC::Lit(lit) => ZXOrDimOrEither::Dim(ACDCDim::Lit { lit: lit.clone() }),
        ACDC::Add([a, b]) => {
            binop_to_dim!(Add, rec_expr, a, b)
        }
        ACDC::Sub([a, b]) => {
            binop_to_dim!(Sub, rec_expr, a, b)
        }
        ACDC::Mul([a, b]) => {
            binop_to_dim!(Mul, rec_expr, a, b)
        }
        ACDC::Dep1(id) => {
            let expr = recexpr_to_ACDC_at(rec_expr, *id).get_zx().unwrap();
            ZXOrDimOrEither::Dim(ACDCDim::Dep1 { zx: Box::new(expr) })
        }
        ACDC::Dep2(id) => {
            let expr = recexpr_to_ACDC_at(rec_expr, *id).get_zx().unwrap();
            ZXOrDimOrEither::Dim(ACDCDim::Dep2 { zx: Box::new(expr) })
        }
        ACDC::Var(s) => ZXOrDimOrEither::Either(
            ACDCZX::Val {
                val: s.to_string(),
                n: None,
                m: None,
            },
            ACDCDim::Symbol {
                symbol: s.to_string(),
            },
        ),
        ACDC::Cast([n, m, zx]) => {
            let n = recexpr_to_ACDC_at(rec_expr, *n).get_dim().unwrap();
            let m = recexpr_to_ACDC_at(rec_expr, *m).get_dim().unwrap();
            let zx = recexpr_to_ACDC_at(rec_expr, *zx).get_zx().unwrap();
            ZXOrDimOrEither::ZX(ACDCZX::Cast {
                n,
                m,
                zx: Box::from(zx),
            })
        }
        ACDC::Stack([a, b]) => {
            binop_to_zx!(Stack, rec_expr, a, b)
        }
        ACDC::Compose([a, b]) => {
            binop_to_zx!(Compose, rec_expr, a, b)
        }
        ACDC::Val([n, m, s]) => {
            let n = recexpr_to_ACDC_at(rec_expr, *n).get_dim().unwrap();
            let m = recexpr_to_ACDC_at(rec_expr, *m).get_dim().unwrap();
            let s = recexpr_to_ACDC_at(rec_expr, *s);
            let symbol = get_val_name(&s);
            ZXOrDimOrEither::ZX(ACDCZX::Val {
                n: Some(n),
                m: Some(m),
                val: symbol,
            })
        }
        ACDC::Z([n, m, a]) => {
            let n = recexpr_to_ACDC_at(rec_expr, *n).get_dim().unwrap();
            let m = recexpr_to_ACDC_at(rec_expr, *m).get_dim().unwrap();
            let alpha = recexpr_to_ACDC_at(rec_expr, *a).get_dim().unwrap();
            ZXOrDimOrEither::ZX(ACDCZX::Z { n, m, alpha })
        }
        ACDC::X([n, m, a]) => {
            let n = recexpr_to_ACDC_at(rec_expr, *n).get_dim().unwrap();
            let m = recexpr_to_ACDC_at(rec_expr, *m).get_dim().unwrap();
            let alpha = recexpr_to_ACDC_at(rec_expr, *a).get_dim().unwrap();
            ZXOrDimOrEither::ZX(ACDCZX::X { n, m, alpha })
        }
        ACDC::NWire(n) => {
            let n = recexpr_to_ACDC_at(rec_expr, *n).get_dim().unwrap();
            ZXOrDimOrEither::ZX(ACDCZX::NWire { n })
        }
        ACDC::Fn(s, ids) => {
            let args = ids
                .iter()
                .map(|id| recexpr_to_ACDC_at(rec_expr, *id))
                .collect::<Vec<_>>();
            let all_dim_args = args.iter().all(|arg| arg.is_dim());
            let zx_or_dim_args = args.iter().map(|arg| arg.to_zx_or_dim(true)).collect();
            let zx_fn = ACDCZX::Fn {
                fn_name: s.to_string(),
                args: zx_or_dim_args,
            };
            if !all_dim_args {
                ZXOrDimOrEither::ZX(zx_fn)
            } else {
                let dim_args = args.iter().map(|arg| arg.get_dim().unwrap()).collect();
                ZXOrDimOrEither::Either(
                    zx_fn,
                    ACDCDim::Fn {
                        fn_name: s.to_string(),
                        args: dim_args,
                    },
                )
            }
        }
    }
}
pub fn recexpr_to_ACDC(rec_expr: &RecExpr<ACDC>) -> ZXOrDimOrEither {
    recexpr_to_ACDC_at(rec_expr, Id::from(0))
}
