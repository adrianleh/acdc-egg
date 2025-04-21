use std::collections::HashMap;
use std::fmt::Debug;
use egg::Analysis;
use crate::{ACDCDim, ACDCZX, ZXOrDim};
use crate::vyzxlemma::Lemma;

fn is_equal_subtree_dim(a: &ACDCDim, b: &ACDCDim) -> bool {
    match (a, b) {
        (ACDCDim::Lit { lit: lit1 }, ACDCDim::Lit { lit: lit2 }) => lit1 == lit2,
        (ACDCDim::Dep1 { zx: zx1 }, ACDCDim::Dep1 { zx: zx2 }) => is_equal_subtree_zx(zx1, zx2),
        (ACDCDim::Dep2 { zx: zx1 }, ACDCDim::Dep2 { zx: zx2 }) => is_equal_subtree_zx(zx1, zx2),
        (ACDCDim::Symbol { symbol: s1 }, ACDCDim::Symbol { symbol: s2 }) => s1 == s2,
        (ACDCDim::Add { a: a1, b: b1 }, ACDCDim::Add { a: a2, b: b2 }) => {
            is_equal_subtree_dim(a1, a2) && is_equal_subtree_dim(b1, b2)
        }
        (ACDCDim::Sub { a: a1, b: b1 }, ACDCDim::Sub { a: a2, b: b2 }) => {
            is_equal_subtree_dim(a1, a2) && is_equal_subtree_dim(b1, b2)
        }
        (ACDCDim::Mul { a: a1, b: b1 }, ACDCDim::Mul { a: a2, b: b2 }) => {
            is_equal_subtree_dim(a1, a2) && is_equal_subtree_dim(b1, b2)
        }
        (
            ACDCDim::Fn {
                fn_name: fn1,
                args: a1,
            },
            ACDCDim::Fn {
                fn_name: fn2,
                args: a2,
            },
        ) => {
            if fn1 != fn2 {
                return false;
            }
            if a1.len() != a2.len() {
                return false;
            }
            a1.iter()
                .zip(a2.iter())
                .all(|(a, b)| is_equal_subtree_dim(a, b))
        }
        (_, _) => false,
    }
}
fn is_equal_subtree_zx(a: &ACDCZX, b: &ACDCZX) -> bool {
    fn zx_or_dim_eq(a: &ZXOrDim, b: &ZXOrDim) -> bool {
        match (a, b) {
            (ZXOrDim::Dim(a), ZXOrDim::Dim(b)) => is_equal_subtree_dim(a, b),
            (ZXOrDim::ZX(a), ZXOrDim::ZX(b)) => is_equal_subtree_zx(a, b),
            (_, _) => false,
        }
    }
    match (a, b) {
        (
            ACDCZX::Z {
                n: n1,
                m: m1,
                alpha: a1,
            },
            ACDCZX::Z {
                n: n2,
                m: m2,
                alpha: a2,
            },
        ) => {
            is_equal_subtree_dim(n1, n2)
                && is_equal_subtree_dim(m1, m2)
                && is_equal_subtree_dim(a1, a2)
        }
        (
            ACDCZX::X {
                n: n1,
                m: m1,
                alpha: a1,
            },
            ACDCZX::X {
                n: n2,
                m: m2,
                alpha: a2,
            },
        ) => {
            is_equal_subtree_dim(n1, n2)
                && is_equal_subtree_dim(m1, m2)
                && is_equal_subtree_dim(a1, a2)
        }
        (
            ACDCZX::Val {
                val: v1,
                n: n1,
                m: m1,
            },
            ACDCZX::Val {
                val: v2,
                n: n2,
                m: m2,
            },
        ) => {
            if n1.is_some() != n2.is_some() || m1.is_some() != m2.is_some() {
                return false;
            }
            if n1.is_some() && !is_equal_subtree_dim(&n1.clone().unwrap(), &n2.clone().unwrap()) {
                return false;
            }
            if m1.is_some() && !is_equal_subtree_dim(&m1.clone().unwrap(), &m2.clone().unwrap()) {
                return false;
            }
            v1 == v2
        }
        (ACDCZX::NWire { n: n1 }, ACDCZX::NWire { n: n2 }) => is_equal_subtree_dim(n1, n2),
        (ACDCZX::Compose { a: a1, b: b1 }, ACDCZX::Compose { a: a2, b: b2 }) => {
            is_equal_subtree_zx(a1, a2) && is_equal_subtree_zx(b1, b2)
        }
        (ACDCZX::Stack { a: a1, b: b1 }, ACDCZX::Stack { a: a2, b: b2 }) => {
            is_equal_subtree_zx(a1, a2) && is_equal_subtree_zx(b1, b2)
        }
        (
            ACDCZX::Cast {
                n: n1,
                m: m1,
                zx: zx1,
            },
            ACDCZX::Cast {
                n: n2,
                m: m2,
                zx: zx2,
            },
        ) => {
            is_equal_subtree_dim(n1, n2)
                && is_equal_subtree_dim(m1, m2)
                && is_equal_subtree_zx(zx1, zx2)
        }
        (
            ACDCZX::Fn {
                fn_name: fn1,
                args: a1,
            },
            ACDCZX::Fn {
                fn_name: fn2,
                args: a2,
            },
        ) => {
            if (fn1 != fn2) {
                return false;
            }
            if a1.len() != a2.len() {
                return false;
            }
            a1.iter().zip(a2).all(|(a, b)| zx_or_dim_eq(a, b))
        }
        (_, _) => false,
    }
}


/*
This function is to determine the how many'th match fired in a rewrite.
We basically check for equivalent subtrees in a by going left to right and then return the index of the subtree where it is not also found in b
0 -indexed!
The bool indicates if any diff has been found at all; if false, behavior of the first argument is undef
 */
pub fn rewrite_at_idx(a: &ACDCZX, b: &ACDCZX, subtree: &ACDCZX) -> (usize, bool) {
    if is_equal_subtree_zx(a,b) {
        eprintln!("Base eq");
        return (0, false)
    }
    println!("Non base eq");

    fn helper(a: &ACDCZX, b: &ACDCZX, subtree: &ACDCZX, idx: usize) -> (usize, bool) {
        // eprintln!("11111111111111111111111\nSearch for idx with\na = {:?}\nb = {:?}\nsubtree={:?}\n11111111111111111111111", a, b, subtree);
        if is_equal_subtree_zx(a,b) {
            eprintln!("Sub base eq");
            return (0, false)
        }
        if is_equal_subtree_zx(a,subtree) {
            eprintln!("Found subtree! is b eq? {}", is_equal_subtree_zx(b,subtree));
            return (idx+ 1, !is_equal_subtree_zx(b,subtree));} // If we find that a matches return 1
        match (a,b) {

            // Only need to check diagrams with subdiags, i.e., stack, compose, cast, fn
            (ACDCZX::Stack {a: a1, b:b1}, ACDCZX::Stack {a: a2, b:b2}) => {
                let (idx, found) = helper(a1, a2, subtree, idx);
                if found { return (idx,found); }
                helper(b1, b2, subtree, idx)
            }
            (ACDCZX::Compose {a: a1, b:b1}, ACDCZX::Compose {a: a2, b:b2}) => {
                let (idx, found) = helper(a1, a2, subtree, idx);
                if found { return (idx,found); }
                helper(b1, b2, subtree, idx)
            }
            (ACDCZX::Cast {zx:zx1,..}, ACDCZX::Cast {zx:zx2,..}) => {
                helper(zx1, zx2, subtree, idx)
            }
            (ACDCZX::Fn {args:a1,..}, ACDCZX::Fn {args:a2,..}) => {
                let mut idx = idx;
                let mut found = false;
                for (p1, p2) in a1.iter().zip(a2) {
                    match (p1,p2){
                        (ZXOrDim::Dim(d1), ZXOrDim::Dim(d2)) => {}
                        (ZXOrDim::ZX(zx1), ZXOrDim::ZX(zx2)) => {
                            (idx, found) = helper(zx1,zx2,subtree, idx);
                            if found { return (idx,found); }
                        }
                        (_ ,_ ) => {}
                    }
                }
                assert_eq!(found, false);
                (idx, found)
            }
            (x, y) => {
                // eprintln!("neq:\n{:?}\n-\n{:?}",x,y);
                (idx,false)},
        }
    }
    helper(a, b, subtree, 0)
}

