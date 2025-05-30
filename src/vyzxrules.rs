use crate::vyzxlemma::{Lemma, ZXParam, generate_rw};
use crate::{ACDC, ACDCDim, ACDCZX, simple_lit, simple_symbol, simple_var};
use egg::{Analysis, Rewrite};
use std::fmt::Debug;

pub fn vyzx_rules<T>() -> Vec<Lemma<T>>
where
    T: Analysis<ACDC> + Clone + 'static + std::fmt::Debug,
{
    let lemmata = vec![
        stack_assoc(),
        stack_assoc_back(),
        stack_empty_top(),
        stack_empty_bot(),
        stack_compose_dist(),
        compose_assoc(),
        nwire_l(),
        nwire_r(),
        cast_id(),
        cast_contract(),
        nwire_add(),
        wire_to_nwire(),
        empty_to_n_wire(),
        stack_nwire_distribute_l(),
        stack_nwire_distribute_r(),
        cast_stack_l(),
        cast_stack_r(),
        cast_X(),
        cast_Z(),
        cast_n_wire(),
        x_0_wire(),
        z_0_wire(),
        Z_abs_fusion(),
    ];
    lemmata
}

pub fn vyzx_rws<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + Debug + 'static,
{
    vyzx_rules::<T>()
        .into_iter()
        .flat_map(|x| x.get_rewrites())
        .collect()
}

fn stack_assoc<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone + Debug + 'static,
{
    generate_rw(
        "stack_assoc",
        &ACDCZX::Stack {
            a: Box::from(ACDCZX::Stack {
                a: Box::from(simple_var("a")),
                b: Box::from(simple_var("b")),
            }),
            b: Box::from(simple_var("c")),
        },
        &ACDCZX::Cast {
            zx: Box::from(ACDCZX::Stack {
                a: Box::from(simple_var("a")),
                b: Box::from(ACDCZX::Stack {
                    a: Box::from(simple_var("b")),
                    b: Box::from(simple_var("c")),
                }),
            }),
            n: ACDCDim::Add {
                a: Box::from(ACDCDim::Add {
                    a: Box::from(simple_symbol("n1")),
                    b: Box::from(simple_symbol("n2")),
                }),
                b: Box::from(simple_symbol("n3")),
            },
            m: ACDCDim::Add {
                a: Box::from(ACDCDim::Add {
                    a: Box::from(simple_symbol("m1")),
                    b: Box::from(simple_symbol("m2")),
                }),
                b: Box::from(simple_symbol("m3")),
            },
        },
        vec![
            ZXParam::new(simple_symbol("n1"), simple_symbol("m1"), "a"),
            ZXParam::new(simple_symbol("n2"), simple_symbol("m2"), "b"),
            ZXParam::new(simple_symbol("n3"), simple_symbol("m3"), "c"),
        ],
        false,
    )
}

fn stack_assoc_back<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "stack_assoc_back",
        &ACDCZX::Stack {
            a: Box::from(simple_var("a")),
            b: Box::from(ACDCZX::Stack {
                a: Box::from(simple_var("b")),
                b: Box::from(simple_var("c")),
            }),
        },
        &ACDCZX::Cast {
            zx: Box::from(ACDCZX::Stack {
                a: Box::from(ACDCZX::Stack {
                    a: Box::from(simple_var("a")),
                    b: Box::from(simple_var("b")),
                }),
                b: Box::from(simple_var("c")),
            }),
            n: ACDCDim::Add {
                a: Box::from(simple_symbol("n1")),
                b: Box::from(ACDCDim::Add {
                    a: Box::from(simple_symbol("n2")),
                    b: Box::from(simple_symbol("n3")),
                }),
            },
            m: ACDCDim::Add {
                a: Box::from(simple_symbol("m1")),
                b: Box::from(ACDCDim::Add {
                    a: Box::from(simple_symbol("m2")),
                    b: Box::from(simple_symbol("m3")),
                }),
            },
        },
        vec![
            ZXParam::new(simple_symbol("n1"), simple_symbol("m1"), "a"),
            ZXParam::new(simple_symbol("n2"), simple_symbol("m2"), "b"),
            ZXParam::new(simple_symbol("n3"), simple_symbol("m3"), "c"),
        ],
        false,
    )
}

pub fn compose_assoc<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "compose_assoc",
        &ACDCZX::Compose {
            a: Box::from(simple_var("a")),
            b: Box::from(ACDCZX::Compose {
                a: Box::from(simple_var("b")),
                b: Box::from(simple_var("c")),
            }),
        },
        &ACDCZX::Compose {
            a: Box::from(ACDCZX::Compose {
                a: Box::from(simple_var("a")),
                b: Box::from(simple_var("b")),
            }),
            b: Box::from(simple_var("c")),
        },
        vec![
            ZXParam::new(simple_symbol("n"), simple_symbol("m1"), "a"),
            ZXParam::new(simple_symbol("n2"), simple_symbol("m2"), "b"),
            ZXParam::new(simple_symbol("n3"), simple_symbol("m3"), "c"),
        ],
        true,
    )
}

fn nwire_l<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "nwire_removal_l",
        &ACDCZX::Compose {
            a: Box::from(ACDCZX::NWire {
                n: simple_symbol("n"),
            }),
            b: Box::from(simple_var("zx")),
        },
        &simple_var("zx"),
        vec![ZXParam::new(simple_symbol("n"), simple_symbol("m"), "zx")],
        false,
    )
}

fn nwire_r<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "nwire_removal_r",
        &ACDCZX::Compose {
            a: Box::from(simple_var("zx")),
            b: Box::from(ACDCZX::NWire {
                n: simple_symbol("m"),
            }),
        },
        &simple_var("zx"),
        vec![ZXParam::new(simple_symbol("n"), simple_symbol("m"), "zx")],
        false,
    )
}

fn nwire_add<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "nwire_add",
        &ACDCZX::Stack {
            a: Box::from(ACDCZX::NWire {
                n: simple_symbol("n"),
            }),
            b: Box::from(ACDCZX::NWire {
                n: simple_symbol("m"),
            }),
        },
        &ACDCZX::NWire {
            n: ACDCDim::Add {
                a: Box::from(simple_symbol("n")),
                b: Box::from(simple_symbol("m")),
            },
        },
        vec![],
        false,
    )
}

fn wire_to_nwire<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone+Debug + 'static,
{
    let rw = generate_rw(
        "wire_to_n_wire",
        &ACDCZX::Val {
            val: String::from("Wire"),
            n: Some(simple_lit(1)),
            m: Some(simple_lit(1)),
        },
        &ACDCZX::NWire { n: simple_lit(1) },
        vec![],
        true,
    );
    rw
}

fn empty_to_n_wire<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "empty_to_nwire",
        &ACDCZX::Val {
            val: String::from("Empty"),
            n: Some(simple_lit(0)),
            m: Some(simple_lit(0)),
        },
        &ACDCZX::NWire { n: simple_lit(0) },
        vec![],
        true,
    )
}

fn stack_empty_top<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "empty_stack_top",
        &ACDCZX::Stack {
            a: Box::from(simple_var("zx")),
            b: Box::from(ACDCZX::Val {
                val: String::from("Empty"),
                n: Some(simple_lit(0)),
                m: Some(simple_lit(0)),
            }),
        },
        &simple_var("zx"),
        vec![ZXParam::new(simple_symbol("n"), simple_symbol("m"), "zx")],
        false,
    )
}

fn stack_empty_bot<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone+Debug + 'static,
{
    generate_rw(
        "empty_stack_bot",
        &ACDCZX::Stack {
            a: Box::from(ACDCZX::Val {
                val: String::from("Empty"),
                n: Some(simple_lit(0)),
                m: Some(simple_lit(0)),
            }),
            b: Box::from(simple_var("zx")),
        },
        &ACDCZX::Cast {
            zx: Box::from(simple_var("zx")),
            n: ACDCDim::Add {
                a: Box::from(ACDCDim::Dep1 {
                    zx: Box::from(simple_var("zx")),
                }),
                b: Box::from(simple_lit(0)),
            },
            m: ACDCDim::Add {
                a: Box::from(ACDCDim::Dep2 {
                    zx: Box::from(simple_var("zx")),
                }),
                b: Box::from(simple_lit(0)),
            },
        },
        vec![ZXParam::new(simple_symbol("n"), simple_symbol("m"), "zx")],
        false,
    )
}

fn cast_id<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "cast_id",
        &ACDCZX::Cast {
            zx: Box::from(simple_var("zx")),
            n: simple_symbol("n"),
            m: simple_symbol("m"),
        },
        &simple_var("zx"),
        vec![ZXParam::new(simple_symbol("n"), simple_symbol("m"), "zx")],
        false,
    )
}

fn cast_contract<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "cast_contract",
        &ACDCZX::Cast {
            zx: Box::from(ACDCZX::Cast {
                n: simple_symbol("n2"),
                m: simple_symbol("m2"),
                zx: Box::new(simple_var("zx")),
            }),
            n: simple_symbol("n1"),
            m: simple_symbol("m1"),
        },
        &ACDCZX::Cast {
            zx: Box::new(simple_var("zx")),
            n: simple_symbol("n1"),
            m: simple_symbol("m1"),
        },
        vec![ZXParam::new(simple_symbol("n"), simple_symbol("m"), "zx")],
        false,
    )
}

fn stack_compose_dist<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "stack_compose_distr",
        &ACDCZX::Stack {
            a: Box::from(ACDCZX::Compose {
                a: Box::from(simple_var("a")),
                b: Box::from(simple_var("b")),
            }),
            b: Box::from(ACDCZX::Compose {
                a: Box::from(simple_var("c")),
                b: Box::from(simple_var("d")),
            }),
        },
        &ACDCZX::Compose {
            a: Box::from(ACDCZX::Stack {
                a: Box::from(simple_var("a")),
                b: Box::from(simple_var("c")),
            }),
            b: Box::from(ACDCZX::Stack {
                a: Box::from(simple_var("b")),
                b: Box::from(simple_var("d")),
            }),
        },
        vec![
            ZXParam::new(simple_symbol("n1"), simple_symbol("m1"), "a"),
            ZXParam::new(simple_symbol("m1"), simple_symbol("o1"), "b"),
            ZXParam::new(simple_symbol("n2"), simple_symbol("m2"), "c"),
            ZXParam::new(simple_symbol("m2"), simple_symbol("o2"), "d"),
        ],
        true,
    )
}

/* Lemma stack_nwire_distribute_l : forall {n m o p} (zx0 : ZX n m) (zx1 : ZX m o),
n_wire p ↕ (zx0 ⟷ zx1) ∝= (n_wire p ↕ zx0) ⟷ (n_wire p ↕ zx1). */
fn stack_nwire_distribute_l<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "stack_nwire_distribute_l",
        &ACDCZX::Stack {
            a: Box::from(ACDCZX::NWire {
                n: simple_symbol("p"),
            }),
            b: Box::from(ACDCZX::Compose {
                a: Box::from(simple_var("zx0")),
                b: Box::from(simple_var("zx1")),
            }),
        },
        &ACDCZX::Compose {
            a: Box::from(ACDCZX::Stack {
                a: Box::from(ACDCZX::NWire {
                    n: simple_symbol("p"),
                }),
                b: Box::from(simple_var("zx0")),
            }),
            b: Box::from(ACDCZX::Stack {
                a: Box::from(ACDCZX::NWire {
                    n: simple_symbol("p"),
                }),
                b: Box::from(simple_var("zx1")),
            }),
        },
        vec![
            ZXParam::new(simple_symbol("n"), simple_symbol("m"), "zx0"),
            ZXParam::new(simple_symbol("m"), simple_symbol("o"), "zx1"),
        ],
        true,
    )
}
/* Lemma stack_nwire_distribute_r : forall {n m o p} (zx0 : ZX n m) (zx1 : ZX m o),
(zx0 ⟷ zx1) ↕ n_wire p ∝= (zx0 ↕ n_wire p) ⟷ (zx1 ↕ n_wire p). */
fn stack_nwire_distribute_r<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "stack_nwire_distribute_r",
        &ACDCZX::Compose {
            a: Box::from(ACDCZX::Compose {
                a: Box::from(simple_var("zx0")),
                b: Box::from(simple_var("zx1")),
            }),
            b: Box::from(ACDCZX::NWire {
                n: simple_symbol("p"),
            }),
        },
        &ACDCZX::Compose {
            a: Box::from(ACDCZX::Stack {
                b: Box::from(ACDCZX::NWire {
                    n: simple_symbol("p"),
                }),
                a: Box::from(simple_var("zx0")),
            }),
            b: Box::from(ACDCZX::Stack {
                b: Box::from(ACDCZX::NWire {
                    n: simple_symbol("p"),
                }),
                a: Box::from(simple_var("zx1")),
            }),
        },
        vec![
            ZXParam::new(simple_symbol("n"), simple_symbol("m"), "zx0"),
            ZXParam::new(simple_symbol("m"), simple_symbol("o"), "zx1"),
        ],
        true,
    )
}

// Lemma cast_stack_l : forall {nTop nTop' mTop mTop' nBot mBot} prfnTop prfmTop prfn prfm
//                           (zxTop : ZX nTop mTop) (zxBot : ZX nBot mBot),
//   (cast nTop' mTop' prfnTop prfmTop zxTop) ↕ zxBot ∝
//   cast (nTop' + nBot) (mTop' + mBot) prfn prfm (zxTop ↕ zxBot).
fn cast_stack_l<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "cast_stack_l",
        &ACDCZX::Stack {
            a: Box::from(ACDCZX::Cast {
                zx: Box::from(simple_var("zxTop")),
                n: simple_symbol("nTop1"),
                m: simple_symbol("mTop1"),
            }),
            b: Box::from(simple_var("zxBot")),
        },
        &ACDCZX::Cast {
            zx: Box::from(ACDCZX::Stack {
                a: Box::from(simple_var("zxTop")),
                b: Box::from(simple_var("zxBot")),
            }),
            n: ACDCDim::Add {
                a: Box::from(simple_symbol("nTop1")),
                b: Box::from(simple_symbol("nBot")),
            },
            m: ACDCDim::Add {
                a: Box::from(simple_symbol("mTop1")),
                b: Box::from(simple_symbol("mBot")),
            },
        },
        vec![
            ZXParam::new(simple_symbol("nTop"), simple_symbol("mTop"), "zxTop"),
            ZXParam::new(simple_symbol("nBot"), simple_symbol("mBot"), "zxBot"),
        ],
        true,
    )
}
// Lemma cast_stack_r : forall {nTop mTop nBot nBot' mBot mBot'} prfnBot prfmBot prfn prfm
//                           (zxTop : ZX nTop mTop) (zxBot : ZX nBot mBot),
//   zxTop ↕ (cast nBot' mBot' prfnBot prfmBot zxBot) ∝=
//   cast (nTop + nBot') (mTop + mBot') prfn prfm (zxTop ↕ zxBot).
fn cast_stack_r<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "cast_stack_r",
        &ACDCZX::Stack {
            a: Box::from(simple_var("zxTop")),
            b: Box::from(ACDCZX::Cast {
                zx: Box::from(simple_var("zxBot")),
                n: simple_symbol("nBot1"),
                m: simple_symbol("mBot1"),
            }),
        },
        &ACDCZX::Cast {
            zx: Box::from(ACDCZX::Stack {
                a: Box::from(simple_var("zxTop")),
                b: Box::from(simple_var("zxBot")),
            }),
            n: ACDCDim::Add {
                a: Box::from(simple_symbol("nTop")),
                b: Box::from(simple_symbol("nBot1")),
            },
            m: ACDCDim::Add {
                a: Box::from(simple_symbol("mTop")),
                b: Box::from(simple_symbol("mBot1")),
            },
        },
        vec![
            ZXParam::new(simple_symbol("nTop"), simple_symbol("mTop"), "zxTop"),
            ZXParam::new(simple_symbol("nBot"), simple_symbol("mBot"), "zxBot"),
        ],
        true,
    )
}

// Lemma cast_contract_l : forall {n m n0 m0 n1 m1} prfn0 prfm0 prfn1 prfm1 prfn prfm
//                                        (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
//   cast n m prfn0 prfm0 zx0 ∝ cast n m prfn1 prfm1 zx1 <->
//   cast n1 m1 prfn prfm zx0
//     ∝ zx1.
// Proof.
//   intros.
//   now subst; rewrite !cast_id_eq.
// Qed.
// TODO: Support

// Lemma cast_Z :
//   forall {n n' m m'} prfn prfm α,
//   cast n' m' prfn prfm (Z n m α) = Z n' m' α.
// Proof.
//   intros.
//   now subst; rewrite !cast_id_eq.
// Qed.
fn cast_Z<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "cast_Z",
        &ACDCZX::Cast {
            n: simple_symbol("n1"),
            m: simple_symbol("m1"),
            zx: Box::from(ACDCZX::Z {
                n: simple_symbol("n"),
                m: simple_symbol("m"),
                alpha: simple_symbol("a"),
            }),
        },
        &ACDCZX::Z {
            n: simple_symbol("n1"),
            m: simple_symbol("m1"),
            alpha: simple_symbol("a"),
        },
        vec![],
        false,
    )
}

// Lemma cast_X :
//   forall {n n' m m'} prfn prfm α,
//   cast n' m' prfn prfm (X n m α) = X n' m' α.
// Proof.
//   intros.
//   now subst; rewrite !cast_id_eq.
// Qed.

fn cast_X<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone+Debug + 'static,
{
    generate_rw(
        "cast_X",
        &ACDCZX::Cast {
            n: simple_symbol("n1"),
            m: simple_symbol("m1"),
            zx: Box::from(ACDCZX::X {
                n: simple_symbol("n"),
                m: simple_symbol("m"),
                alpha: simple_symbol("a"),
            }),
        },
        &ACDCZX::X {
            n: simple_symbol("n1"),
            m: simple_symbol("m1"),
            alpha: simple_symbol("a"),
        },
        vec![],
        false,
    )
}

// Lemma cast_n_stack1 : forall {n n'} prfn prfm (zx : ZX 1 1),
//   cast n' n' prfn prfm (n ↑ zx) = n' ↑ zx.
// Proof.
//   intros.
//   now subst; rewrite !cast_id_eq.
// Qed.
//
// Lemma cast_n_wire : forall {n n'} prfn prfm,
//   cast n' n' prfn prfm (n_wire n) = n_wire n'.
// Proof.
//   intros.
//   apply cast_n_stack1.
// Qed.
fn cast_n_wire<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone+Debug + 'static,
{
    generate_rw(
        "cast_n_wire",
        &ACDCZX::Cast {
            n: simple_symbol("n1"),
            m: simple_symbol("n1"),
            zx: Box::from(ACDCZX::NWire {
                n: simple_symbol("n"),
            }),
        },
        &ACDCZX::NWire {
            n: simple_symbol("n1"),
        },
        vec![],
        false,
    )
}
// Lemma cast_n_box : forall {n n'} prfn prfm,
//   cast n' n' prfn prfm (n_box n) = n_box n'.
// Proof.
//   intros.
//   apply cast_n_stack1.
// Qed.

fn z_0_wire<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone+Debug + 'static,
{
    generate_rw(
        "Z_0_is_wire",
        &ACDCZX::Z {
            n: simple_lit(1),
            m: simple_lit(1),
            alpha: simple_lit(0),
        },
        &ACDCZX::Val {
            val: String::from("wire"),
            n: Some(simple_lit(1)),
            m: Some(simple_lit(1)),
        },
        vec![],
        true,
    )
}

fn x_0_wire<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone+Debug + 'static,
{
    generate_rw(
        "X_0_is_wire",
        &ACDCZX::X {
            n: simple_lit(1),
            m: simple_lit(1),
            alpha: simple_lit(0),
        },
        &ACDCZX::Val {
            val: String::from("wire"),
            n: Some(simple_lit(1)),
            m: Some(simple_lit(1)),
        },
        vec![],
        true,
    )
}
fn Z_abs_fusion<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone+Debug + 'static,
{
    generate_rw(
        "Z_abs_fusion",
        &ACDCZX::Compose {
            a: Box::from(ACDCZX::Z {
                n: simple_symbol("n"),
                m: simple_symbol("m"),
                alpha: simple_symbol("a"),
            }),
            b: Box::from(ACDCZX::Z {
                alpha: simple_symbol("b"),
                n: simple_symbol("m"),
                m: simple_symbol("o"),
            }),
        },
        &ACDCZX::Z {
            n: simple_symbol("n"),
            m: simple_symbol("o"),
            alpha: ACDCDim::Add {
                a: Box::from(simple_symbol("a")),
                b: Box::from(simple_symbol("b")),
            },
        },
        vec![],
        false,
    )
}

fn X_abs_fusion<T>() -> Lemma<T>
where
    T: Analysis<ACDC> + Clone +Debug+ 'static,
{
    generate_rw(
        "Z_abs_fusion",
        &ACDCZX::Compose {
            a: Box::from(ACDCZX::X {
                n: simple_symbol("n"),
                m: simple_symbol("m"),
                alpha: simple_symbol("a"),
            }),
            b: Box::from(ACDCZX::X {
                alpha: simple_symbol("b"),
                n: simple_symbol("m"),
                m: simple_symbol("o"),
            }),
        },
        &ACDCZX::X {
            n: simple_symbol("n"),
            m: simple_symbol("o"),
            alpha: ACDCDim::Add {
                a: Box::from(simple_symbol("a")),
                b: Box::from(simple_symbol("b")),
            },
        },
        vec![],
        false,
    )
}
