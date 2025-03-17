use crate::vyzxlemma::{ZXParam, generate_rw};
use crate::{ACDC, ACDCDim, ACDCZX, simple_lit, simple_symbol, simple_var};
use egg::{Analysis, Rewrite};

pub fn vyzx_rules<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    let rws = vec![
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
    ];
    rws.into_iter().flatten().collect()
}

fn stack_assoc<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    generate_rw(
        "stack-assoc",
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
                    a: Box::from(ACDCDim::Dep1 {zx : Box::from(simple_var("a"))}),
                    b: Box::from(ACDCDim::Dep1 { zx: Box::from(simple_var("b")) }),
                }),
                b: Box::from(ACDCDim::Dep1 { zx: Box::from(simple_var("c")) }),
            },
            m: ACDCDim::Add {
                a: Box::from(ACDCDim::Add {
                    a: Box::from(ACDCDim::Dep2 { zx: Box::from(simple_var("a")) }),
                    b: Box::from(ACDCDim::Dep2 { zx: Box::from(simple_var("b")) }),
                }),
                b: Box::from(ACDCDim::Dep2 { zx: Box::from(simple_var("c")) }),
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

fn stack_assoc_back<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    generate_rw(
        "stack-assoc-back",
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
                a: Box::from(ACDCDim::Dep1 {zx : Box::from(simple_var("a"))}),
                b: Box::from(ACDCDim::Add {
                    a: Box::from(ACDCDim::Dep1 {zx : Box::from(simple_var("b"))}),
                    b: Box::from(ACDCDim::Dep1 {zx : Box::from(simple_var("c"))}),
                }),
            },
            m: ACDCDim::Add {
                a: Box::from(ACDCDim::Dep2 {zx : Box::from(simple_var("a"))}),
                b: Box::from(ACDCDim::Add {
                    a: Box::from(ACDCDim::Dep2 {zx : Box::from(simple_var("b"))}),
                    b: Box::from(ACDCDim::Dep2 {zx : Box::from(simple_var("c"))}),
                }),
            }
        },
        vec![
            ZXParam::new(simple_symbol("n1"), simple_symbol("m1"), "a"),
            ZXParam::new(simple_symbol("n2"), simple_symbol("m2"), "b"),
            ZXParam::new(simple_symbol("n3"), simple_symbol("m3"), "c"),
        ],
        false,
    )
}

fn compose_assoc<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    generate_rw(
        "stack-assoc-back",
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
            ZXParam::new(simple_symbol("m1"), simple_symbol("m2"), "b"),
            ZXParam::new(simple_symbol("m2"), simple_symbol("o"), "c"),
        ],
        true,
    )
}

fn nwire_l<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    generate_rw(
        "n_wire_l",
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

fn nwire_r<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    generate_rw(
        "n_wire_r",
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

fn nwire_add<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
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
        true,
    )
}

fn stack_empty_top<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    generate_rw(
        "empty_stack",
        &ACDCZX::Stack {
            a: Box::from(simple_var("zx")),
            b: Box::from(ACDCZX::Val {
                val: String::from("empty"),
                n: Some(simple_lit(0)),
                m: Some(simple_lit(0)),
            }),
        },
        &simple_var("zx"),
        vec![ZXParam::new(simple_symbol("n"), simple_symbol("m"), "zx")],
        false,
    )
}

fn stack_empty_bot<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    generate_rw(
        "empty_stack",
        &ACDCZX::Stack {
            a: Box::from(ACDCZX::Val {
                val: String::from("empty"),
                n: Some(simple_lit(0)),
                m: Some(simple_lit(0)),
            }),
            b: Box::from(simple_var("zx")),
        },
        &ACDCZX::Cast {
            zx: Box::from(simple_var("zx")),
            n: ACDCDim::Add {
                a: Box::from(ACDCDim::Dep1 {zx: Box::from(simple_var("zx")) }),
                b: Box::from(simple_lit(0)),
            },
            m: ACDCDim::Add {
                a: Box::from(ACDCDim::Dep2 {zx: Box::from(simple_var("zx")) }),
                b: Box::from(simple_lit(0)),
            },
        },
        vec![ZXParam::new(simple_symbol("n"), simple_symbol("m"), "zx")],
        false,
    )
}

fn cast_id<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    generate_rw(
        "cast_id",
        &ACDCZX::Cast {
            zx: Box::from(simple_var("zx")),
            n: ACDCDim::Dep1 {
                zx: Box::from(simple_var("zx")),
            },
            m: ACDCDim::Dep2 {
                zx: Box::from(simple_var("zx")),
            },
        },
        &simple_var("zx"),
        vec![ZXParam::new(simple_symbol("n"), simple_symbol("m"), "zx")],
        false,
    )
}

fn cast_contract<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
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

fn stack_compose_dist<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    generate_rw(
        "stack-compose-dist",
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
