use crate::{ZXOrDim, ACDCZX};
use std::ops::Deref;

// Idea
// 1. Find largest diff resulting from rw
// 2. Extract parameters from the diff
// 3. Count how manyth instance the one matched upon was in the original
fn largest_diff(a: &ACDCZX, b: &ACDCZX) -> Option<(ACDCZX, ACDCZX)> {
    if a == b {
        return None;
    }
    match (a, b) {
        (
            ACDCZX::Cast {
                n: _,
                m: _,
                zx: zx1,
            },
            ACDCZX::Cast {
                n: _,
                m: _,
                zx: zx2,
            },
        ) => largest_diff(zx1.deref(), zx2.deref()),
        (ACDCZX::Stack { a: a1, b: b1 }, ACDCZX::Stack { a: a2, b: b2 }) => {
            let diff_a = largest_diff(a1.deref(), a2.deref());
            let diff_b = largest_diff(b1.deref(), b2.deref());
            if diff_a.is_some() && diff_b.is_some() {
                return Some((a.clone(), b.clone()));
            }
            diff_a.or(diff_b)
        }
        (ACDCZX::Compose { a: a1, b: b1 }, ACDCZX::Compose { a: a2, b: b2 }) => {
            let diff_a = largest_diff(a1.deref(), a2.deref());
            let diff_b = largest_diff(b1.deref(), b2.deref());
            if diff_a.is_some() && diff_b.is_some() {
                return Some((a.clone(), b.clone()));
            }
            diff_a.or(diff_b)
        }
        (ACDCZX::Fn {fn_name: fn_name1, args: args1}, ACDCZX::Fn {fn_name: fn_name2, args: args2}) => {
            if fn_name1 != fn_name2 {
                return Some((a.clone(), b.clone()));
            }
            let mut diff = None;
            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                match (arg1, arg2) {
                    (ZXOrDim::ZX(a1), ZXOrDim::ZX(a2)) => {
                        if let Some(d) = largest_diff(a1, a2) {
                            if diff.is_some() { // Means we found a second diff
                                return Some((a.clone(), b.clone()));
                            }
                            diff = Some((a1.clone(), a2.clone()));
                        }
                    }
                    _ => continue
                }
            }
            diff
        }
        _ => {
            // If they are not the same type, return them as a difference
             Some((a.clone(), b.clone()))
        }
    }
}

// fn diff_count<T>(a: &ACDCZX, b: &ACDCZX, lemma: &Lemma<T>, params: &HashMap<String, Box<ACDCZX>>) -> usize {
//
// }