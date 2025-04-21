use crate::vyzxlemma::Lemma;
use crate::{ACDCDim, ACDCZX, ZXOrDim};
use egg::Analysis;
use std::collections::HashMap;
use std::fmt::Debug;

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
            v1.eq(v2)
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
    if is_equal_subtree_zx(a, b) {
        eprintln!("Base eq");
        return (0, false);
    }
    println!("Non base eq");

    fn helper(a: &ACDCZX, b: &ACDCZX, subtree: &ACDCZX, idx: usize) -> (usize, bool) {
        // eprintln!("11111111111111111111111\nSearch for idx with\na = {:?}\nb = {:?}\nsubtree={:?}\n11111111111111111111111", a, b, subtree);
        println!(
            "Search for idx (curr {}) with\na = {:?}\nb = {:?}\nsubtree={:?}",
            idx, a, b, subtree
        );
        if is_equal_subtree_zx(a, subtree) {
            eprintln!(
                "Found subtree! is b eq? {}",
                is_equal_subtree_zx(b, subtree)
            );
            return (idx + 1, !is_equal_subtree_zx(b, subtree));
        } // If we find that a matches return 1
        match (a, b) {
            // Only need to check diagrams with subdiags, i.e., stack, compose, cast, fn
            (ACDCZX::Stack { a: a1, b: b1 }, ACDCZX::Stack { a: a2, b: b2 }) => {
                eprintln!("Stack {:?}, {:?}", a1, b1);
                let (idx, found) = helper(a1, a2, subtree, idx);
                eprintln!("Found {} at idx {}", found, idx);
                if found {
                    return (idx, found);
                }
                helper(b1, b2, subtree, idx)
            }
            (ACDCZX::Compose { a: a1, b: b1 }, ACDCZX::Compose { a: a2, b: b2 }) => {
                eprintln!("Compose {:?}, {:?}", a1, b1);
                let (idx, found) = helper(a1, a2, subtree, idx);
                eprintln!("Found {} at idx {}", found, idx);
                if found {
                    return (idx, found);
                }
                helper(b1, b2, subtree, idx)
            }
            (ACDCZX::Cast { zx: zx1, .. }, ACDCZX::Cast { zx: zx2, .. }) => {
                helper(zx1, zx2, subtree, idx)
            }
            (ACDCZX::Fn { args: a1, .. }, ACDCZX::Fn { args: a2, .. }) => {
                let mut idx = idx;
                let mut found = false;
                for (p1, p2) in a1.iter().zip(a2) {
                    match (p1, p2) {
                        (ZXOrDim::Dim(d1), ZXOrDim::Dim(d2)) => {}
                        (ZXOrDim::ZX(zx1), ZXOrDim::ZX(zx2)) => {
                            (idx, found) = helper(zx1, zx2, subtree, idx);
                            if found {
                                return (idx, found);
                            }
                        }
                        (_, _) => {}
                    }
                }
                assert_eq!(found, false);
                (idx, found)
            }
            (x, y) => {
                // eprintln!("neq:\n{:?}\n-\n{:?}",x,y);
                (idx, false)
            }
        }
    }
    helper(a, b, subtree, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ACDCZX::Compose;
    use crate::{ACDCDim, ACDCZX, ZXOrDim, simple_lit};

    fn create_sample_acdczx() -> ACDCZX {
        ACDCZX::Stack {
            a: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 1 },
                m: ACDCDim::Lit { lit: 2 },
                alpha: ACDCDim::Lit { lit: 3 },
            }),
            b: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 1 },
                m: ACDCDim::Lit { lit: 2 },
                alpha: ACDCDim::Lit { lit: 3 },
            }),
        }
    }

    fn create_subtree() -> ACDCZX {
        ACDCZX::Z {
            n: ACDCDim::Lit { lit: 1 },
            m: ACDCDim::Lit { lit: 2 },
            alpha: ACDCDim::Lit { lit: 3 },
        }
    }

    fn create_different_acdczx() -> ACDCZX {
        ACDCZX::Stack {
            a: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 1 },
                m: ACDCDim::Lit { lit: 2 },
                alpha: ACDCDim::Lit { lit: 3 },
            }),
            b: Box::new(ACDCZX::X {
                n: ACDCDim::Lit { lit: 1 },
                m: ACDCDim::Lit { lit: 2 },
                alpha: ACDCDim::Lit { lit: 3 },
            }),
        }
    }

    fn base_val() -> ACDCZX {
        val("test".to_string())
    }
    fn val(val: String) -> ACDCZX {
        ACDCZX::Val {
            val,
            n: Some(simple_lit(1)),
            m: Some(simple_lit(1)),
        }
    }
    fn create_sample_acdczx_deeper() -> ACDCZX {
        ACDCZX::Stack {
            a: Box::new(base_val()),
            b: Box::new(ACDCZX::Stack {
                a: Box::new(ACDCZX::Z {
                    n: ACDCDim::Lit { lit: 1 },
                    m: ACDCDim::Lit { lit: 2 },
                    alpha: ACDCDim::Lit { lit: 3 },
                }),
                b: Box::new(Compose {
                    a: Box::from(base_val()),
                    b: Box::from(base_val()),
                }),
            }),
        }
    }

    fn create_sample_acdczx_deeper_start() -> ACDCZX {
        ACDCZX::Stack {
            a: Box::new(val("CHANGED".to_string())),
            b: Box::new(ACDCZX::Stack {
                a: Box::new(ACDCZX::Z {
                    n: ACDCDim::Lit { lit: 1 },
                    m: ACDCDim::Lit { lit: 2 },
                    alpha: ACDCDim::Lit { lit: 3 },
                }),
                b: Box::new(Compose {
                    a: Box::from(base_val()),
                    b: Box::from(base_val()),
                }),
            }),
        }
    }

    fn create_sample_acdczx_deeper_mid() -> ACDCZX {
        ACDCZX::Stack {
            a: Box::new(base_val()),
            b: Box::new(ACDCZX::Stack {
                a: Box::new(ACDCZX::Z {
                    n: ACDCDim::Lit { lit: 1 },
                    m: ACDCDim::Lit { lit: 2 },
                    alpha: ACDCDim::Lit { lit: 3 },
                }),
                b: Box::new(Compose {
                    a: Box::from(val("CHANGED".to_string())),
                    b: Box::from(base_val()),
                }),
            }),
        }
    }

    fn create_sample_acdczx_deeper_tail() -> ACDCZX {
        ACDCZX::Stack {
            a: Box::new(base_val()),
            b: Box::new(ACDCZX::Stack {
                a: Box::new(ACDCZX::Z {
                    n: ACDCDim::Lit { lit: 1 },
                    m: ACDCDim::Lit { lit: 2 },
                    alpha: ACDCDim::Lit { lit: 3 },
                }),
                b: Box::new(Compose {
                    a: Box::new(base_val()),
                    b: Box::from(val("CHANGED".to_string())),
                }),
            }),
        }
    }

    #[test]
    fn rewrite_at_idx_returns_correct_index_when_subtree_found() {
        let a = create_sample_acdczx();
        let b = create_different_acdczx();
        let subtree = create_subtree();
        let (idx, found) = rewrite_at_idx(&a, &b, &subtree);
        assert_eq!(idx, 2);
        assert!(found);
    }

    #[test]
    fn rewrite_at_idx_returns_when_trees_are_equal() {
        let a = create_sample_acdczx();
        let b = create_sample_acdczx();
        let subtree = create_subtree();
        let (idx, found) = rewrite_at_idx(&a, &b, &subtree);
        assert!(!found);
    }

    #[test]
    fn rewrite_at_idx_returns_zero_and_false_when_subtree_not_found() {
        let a = create_sample_acdczx();
        let b = create_sample_acdczx();
        let subtree = create_different_acdczx();
        let (idx, found) = rewrite_at_idx(&a, &b, &subtree);
        assert!(!found);
    }

    #[test]
    fn rewrite_at_idx_front() {
        let a = create_sample_acdczx_deeper();
        let b = create_sample_acdczx_deeper_start();
        let subtree = base_val();
        let (idx, found) = rewrite_at_idx(&a, &b, &subtree);
        assert_eq!(idx, 1);
        assert!(found);
    }

    #[test]
    fn rewrite_at_idx_mid() {
        let a = create_sample_acdczx_deeper();
        let b = create_sample_acdczx_deeper_mid();
        let subtree = base_val();
        let (idx, found) = rewrite_at_idx(&a, &b, &subtree);
        assert_eq!(idx, 2);
        assert!(found);
    }

    #[test]
    fn rewrite_at_idx_tail() {
        let a = create_sample_acdczx_deeper();
        let b = create_sample_acdczx_deeper_tail();
        let subtree = base_val();
        let (idx, found) = rewrite_at_idx(&a, &b, &subtree);
        assert_eq!(idx, 3);
        assert!(found);
    }

    #[test]
    fn rewrite_at_idx_handles_empty_subtree() {
        let a = create_sample_acdczx();
        let b = create_sample_acdczx();
        let subtree = ACDCZX::Val {
            val: "".to_string(),
            n: None,
            m: None,
        };
        let (idx, found) = rewrite_at_idx(&a, &b, &subtree);
        assert_eq!(idx, 0);
        assert!(!found);
    }
    #[test]
    fn is_equal_subtree_zx_identical_simple_z_nodes() {
        let a = ACDCZX::Z {
            n: ACDCDim::Lit { lit: 1 },
            m: ACDCDim::Lit { lit: 2 },
            alpha: ACDCDim::Lit { lit: 3 },
        };
        let b = ACDCZX::Z {
            n: ACDCDim::Lit { lit: 1 },
            m: ACDCDim::Lit { lit: 2 },
            alpha: ACDCDim::Lit { lit: 3 },
        };
        assert!(is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_different_simple_z_nodes() {
        let a = ACDCZX::Z {
            n: ACDCDim::Lit { lit: 1 },
            m: ACDCDim::Lit { lit: 2 },
            alpha: ACDCDim::Lit { lit: 3 },
        };
        let b = ACDCZX::Z {
            n: ACDCDim::Lit { lit: 4 },
            m: ACDCDim::Lit { lit: 5 },
            alpha: ACDCDim::Lit { lit: 6 },
        };
        assert!(!is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_identical_simple_x_nodes() {
        let a = ACDCZX::X {
            n: ACDCDim::Lit { lit: 1 },
            m: ACDCDim::Lit { lit: 2 },
            alpha: ACDCDim::Lit { lit: 3 },
        };
        let b = ACDCZX::X {
            n: ACDCDim::Lit { lit: 1 },
            m: ACDCDim::Lit { lit: 2 },
            alpha: ACDCDim::Lit { lit: 3 },
        };
        assert!(is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_different_simple_x_nodes() {
        let a = ACDCZX::X {
            n: ACDCDim::Lit { lit: 1 },
            m: ACDCDim::Lit { lit: 2 },
            alpha: ACDCDim::Lit { lit: 3 },
        };
        let b = ACDCZX::X {
            n: ACDCDim::Lit { lit: 4 },
            m: ACDCDim::Lit { lit: 5 },
            alpha: ACDCDim::Lit { lit: 6 },
        };
        assert!(!is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_identical_stack_nodes() {
        let a = ACDCZX::Stack {
            a: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 1 },
                m: ACDCDim::Lit { lit: 2 },
                alpha: ACDCDim::Lit { lit: 3 },
            }),
            b: Box::new(ACDCZX::X {
                n: ACDCDim::Lit { lit: 4 },
                m: ACDCDim::Lit { lit: 5 },
                alpha: ACDCDim::Lit { lit: 6 },
            }),
        };
        let b = ACDCZX::Stack {
            a: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 1 },
                m: ACDCDim::Lit { lit: 2 },
                alpha: ACDCDim::Lit { lit: 3 },
            }),
            b: Box::new(ACDCZX::X {
                n: ACDCDim::Lit { lit: 4 },
                m: ACDCDim::Lit { lit: 5 },
                alpha: ACDCDim::Lit { lit: 6 },
            }),
        };
        assert!(is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_different_stack_nodes() {
        let a = ACDCZX::Stack {
            a: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 1 },
                m: ACDCDim::Lit { lit: 2 },
                alpha: ACDCDim::Lit { lit: 3 },
            }),
            b: Box::new(ACDCZX::X {
                n: ACDCDim::Lit { lit: 4 },
                m: ACDCDim::Lit { lit: 5 },
                alpha: ACDCDim::Lit { lit: 6 },
            }),
        };
        let b = ACDCZX::Stack {
            a: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 7 },
                m: ACDCDim::Lit { lit: 8 },
                alpha: ACDCDim::Lit { lit: 9 },
            }),
            b: Box::new(ACDCZX::X {
                n: ACDCDim::Lit { lit: 10 },
                m: ACDCDim::Lit { lit: 11 },
                alpha: ACDCDim::Lit { lit: 12 },
            }),
        };
        assert!(!is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_identical_compose_nodes() {
        let a = ACDCZX::Compose {
            a: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 1 },
                m: ACDCDim::Lit { lit: 2 },
                alpha: ACDCDim::Lit { lit: 3 },
            }),
            b: Box::new(ACDCZX::X {
                n: ACDCDim::Lit { lit: 4 },
                m: ACDCDim::Lit { lit: 5 },
                alpha: ACDCDim::Lit { lit: 6 },
            }),
        };
        let b = ACDCZX::Compose {
            a: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 1 },
                m: ACDCDim::Lit { lit: 2 },
                alpha: ACDCDim::Lit { lit: 3 },
            }),
            b: Box::new(ACDCZX::X {
                n: ACDCDim::Lit { lit: 4 },
                m: ACDCDim::Lit { lit: 5 },
                alpha: ACDCDim::Lit { lit: 6 },
            }),
        };
        assert!(is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_different_compose_nodes() {
        let a = ACDCZX::Compose {
            a: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 1 },
                m: ACDCDim::Lit { lit: 2 },
                alpha: ACDCDim::Lit { lit: 3 },
            }),
            b: Box::new(ACDCZX::X {
                n: ACDCDim::Lit { lit: 4 },
                m: ACDCDim::Lit { lit: 5 },
                alpha: ACDCDim::Lit { lit: 6 },
            }),
        };
        let b = ACDCZX::Compose {
            a: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 7 },
                m: ACDCDim::Lit { lit: 8 },
                alpha: ACDCDim::Lit { lit: 9 },
            }),
            b: Box::new(ACDCZX::X {
                n: ACDCDim::Lit { lit: 10 },
                m: ACDCDim::Lit { lit: 11 },
                alpha: ACDCDim::Lit { lit: 12 },
            }),
        };
        assert!(!is_equal_subtree_zx(&a, &b));
    }
    #[test]
    fn is_equal_subtree_zx_handles_empty_val_nodes() {
        let a = ACDCZX::Val {
            val: "".to_string(),
            n: None,
            m: None,
        };
        let b = ACDCZX::Val {
            val: "".to_string(),
            n: None,
            m: None,
        };
        assert!(is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_handles_empty_non_empty_n() {
        let a = ACDCZX::Val {
            val: "".to_string(),
            n: Some(ACDCDim::Lit { lit: 1 }),
            m: None,
        };
        let b = ACDCZX::Val {
            val: "".to_string(),
            n: None,
            m: None,
        };
        assert!(!is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_handles_empty_non_empty_m() {
        let a = ACDCZX::Val {
            val: "".to_string(),
            m: Some(ACDCDim::Lit { lit: 1 }),
            n: None,
        };
        let b = ACDCZX::Val {
            val: "".to_string(),
            n: None,
            m: None,
        };
        assert!(!is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_handles_different_empty_val_nodes() {
        let a = ACDCZX::Val {
            val: "".to_string(),
            n: None,
            m: None,
        };
        let b = ACDCZX::Val {
            val: "non-empty".to_string(),
            n: None,
            m: None,
        };
        assert!(!is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_handles_nested_cast_nodes() {
        let a = ACDCZX::Cast {
            n: ACDCDim::Lit { lit: 1 },
            m: ACDCDim::Lit { lit: 2 },
            zx: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 3 },
                m: ACDCDim::Lit { lit: 4 },
                alpha: ACDCDim::Lit { lit: 5 },
            }),
        };
        let b = ACDCZX::Cast {
            n: ACDCDim::Lit { lit: 1 },
            m: ACDCDim::Lit { lit: 2 },
            zx: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 3 },
                m: ACDCDim::Lit { lit: 4 },
                alpha: ACDCDim::Lit { lit: 5 },
            }),
        };
        assert!(is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_handles_different_nested_cast_nodes() {
        let a = ACDCZX::Cast {
            n: ACDCDim::Lit { lit: 1 },
            m: ACDCDim::Lit { lit: 2 },
            zx: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 3 },
                m: ACDCDim::Lit { lit: 4 },
                alpha: ACDCDim::Lit { lit: 5 },
            }),
        };
        let b = ACDCZX::Cast {
            n: ACDCDim::Lit { lit: 6 },
            m: ACDCDim::Lit { lit: 7 },
            zx: Box::new(ACDCZX::Z {
                n: ACDCDim::Lit { lit: 8 },
                m: ACDCDim::Lit { lit: 9 },
                alpha: ACDCDim::Lit { lit: 10 },
            }),
        };
        assert!(!is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_handles_fn_nodes_with_identical_args() {
        let a = ACDCZX::Fn {
            fn_name: "test_fn".to_string(),
            args: vec![
                ZXOrDim::Dim(ACDCDim::Lit { lit: 1 }),
                ZXOrDim::ZX(ACDCZX::Z {
                    n: ACDCDim::Lit { lit: 2 },
                    m: ACDCDim::Lit { lit: 3 },
                    alpha: ACDCDim::Lit { lit: 4 },
                }),
            ],
        };
        let b = ACDCZX::Fn {
            fn_name: "test_fn".to_string(),
            args: vec![
                ZXOrDim::Dim(ACDCDim::Lit { lit: 1 }),
                ZXOrDim::ZX(ACDCZX::Z {
                    n: ACDCDim::Lit { lit: 2 },
                    m: ACDCDim::Lit { lit: 3 },
                    alpha: ACDCDim::Lit { lit: 4 },
                }),
            ],
        };
        assert!(is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_handles_fn_nodes_with_different_args() {
        let a = ACDCZX::Fn {
            fn_name: "test_fn".to_string(),
            args: vec![
                ZXOrDim::Dim(ACDCDim::Lit { lit: 1 }),
                ZXOrDim::ZX(ACDCZX::Z {
                    n: ACDCDim::Lit { lit: 2 },
                    m: ACDCDim::Lit { lit: 3 },
                    alpha: ACDCDim::Lit { lit: 4 },
                }),
            ],
        };
        let b = ACDCZX::Fn {
            fn_name: "test_fn".to_string(),
            args: vec![
                ZXOrDim::Dim(ACDCDim::Lit { lit: 5 }),
                ZXOrDim::ZX(ACDCZX::Z {
                    n: ACDCDim::Lit { lit: 6 },
                    m: ACDCDim::Lit { lit: 7 },
                    alpha: ACDCDim::Lit { lit: 8 },
                }),
            ],
        };
        assert!(!is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_handles_fn_nodes_with_different_names() {
        let a = ACDCZX::Fn {
            fn_name: "fn_a".to_string(),
            args: vec![ZXOrDim::Dim(ACDCDim::Lit { lit: 1 })],
        };
        let b = ACDCZX::Fn {
            fn_name: "fn_b".to_string(),
            args: vec![ZXOrDim::Dim(ACDCDim::Lit { lit: 1 })],
        };
        assert!(!is_equal_subtree_zx(&a, &b));
    }

    #[test]
    fn is_equal_subtree_zx_handles_fn_nodes_with_different_arg_lengths() {
        let a = ACDCZX::Fn {
            fn_name: "test_fn".to_string(),
            args: vec![ZXOrDim::Dim(ACDCDim::Lit { lit: 1 })],
        };
        let b = ACDCZX::Fn {
            fn_name: "test_fn".to_string(),
            args: vec![
                ZXOrDim::Dim(ACDCDim::Lit { lit: 1 }),
                ZXOrDim::Dim(ACDCDim::Lit { lit: 2 }),
            ],
        };
        assert!(!is_equal_subtree_zx(&a, &b));
    }
    // Additional tests for edge cases, nested structures, and empty nodes can be added similarly.
}
