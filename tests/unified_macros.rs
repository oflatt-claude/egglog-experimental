use egglog::ast::*;
use egglog::constraint::{SimpleTypeConstraint, TypeConstraint};
use egglog::macros::*;
use egglog::*;
use egglog_experimental::new_experimental_egraph;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

#[test]
fn fresh_and_effectful_share_later_head_constraints() {
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(
        None,
        "
        (datatype A (A0)) (datatype B (B0))
        (relation SeenA (A)) (relation SeenB (B))
        (rule () ((let a (unstable-fresh! :cost 3))
                  (set-effectful a)
                  (let b (unstable-fresh! :cost 7 :unextractable))
                  (set-effectful b)
                  (SeenB b) (SeenA a)))
        (run 2)
        (check (SeenA a) (effsafe_effectful_A a) (SeenB b) (effsafe_effectful_B b))
    ",
    )
    .unwrap();
    assert_eq!(eg.get_size("SeenA"), 1);
    assert_eq!(eg.get_size("SeenB"), 1);
}

#[test]
fn fresh_keys_use_all_query_bindings_and_distinguish_occurrences() {
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(
        None,
        "
        (datatype A (A0)) (relation Input (i64)) (relation Seen (i64 A A))
        (Input 1) (Input 2)
        (rule ((Input x)) ((Seen x (unstable-fresh!) (unstable-fresh!))))
        (run 3)
        (check (Seen 1 a b) (!= a b))
        (check (Seen 1 a b) (Seen 2 c d) (!= a c))
    ",
    )
    .unwrap();
    assert_eq!(eg.get_size("Seen"), 2);
}

#[test]
fn ambiguous_fresh_and_invalid_options_have_expansion_errors() {
    for source in [
        "(rule () ((set-effectful (unstable-fresh!))))",
        "(rule () ((unstable-fresh! :cost -1)))",
        "(rule () ((unstable-fresh! :cost)))",
        "(rule () ((unstable-fresh! :surprise)))",
    ] {
        let mut eg = new_experimental_egraph();
        eg.parse_and_run_program(None, "(datatype A (A0)) (datatype B (B0))")
            .unwrap();
        assert!(eg.parse_and_run_program(None, source).is_err(), "{source}");
    }
}

#[derive(Clone)]
struct Constant {
    name: &'static str,
    sort: ArcSort,
    value: Value,
    count: Arc<AtomicUsize>,
}
impl Primitive for Constant {
    fn name(&self) -> &str {
        self.name
    }
    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(self.name, vec![self.sort.clone()], span.clone()).into_box()
    }
}
impl PurePrim for Constant {
    fn apply<'a, 'db>(&self, _: PureState<'a, 'db>, _: &[Value]) -> Option<Value> {
        Some(self.value)
    }
}
impl WritePrim for Constant {
    fn apply<'a, 'db>(&self, _: WriteState<'a, 'db>, _: &[Value]) -> Option<Value> {
        self.count.fetch_add(1, Ordering::SeqCst);
        Some(self.value)
    }
}

#[test]
fn effectful_predicate_prunes_base_sort_overloads_before_solving() {
    for in_rule in [false, true] {
        let mut eg = new_experimental_egraph();
        eg.parse_and_run_program(None, "(datatype A (A0)) (datatype B (B0))")
            .unwrap();
        for text in ["(A0)", "0"] {
            let expr = eg.parser.get_expr_from_string(None, text).unwrap();
            let (sort, value) = eg.eval_expr(&expr).unwrap();
            eg.add_pure_primitive(
                Constant {
                    name: "choose",
                    sort,
                    value,
                    count: Arc::default(),
                },
                None,
            );
        }
        let source = if in_rule {
            "(rule () ((let x (choose)) (set-effectful x))) (run 1)"
        } else {
            "(set-effectful (choose))"
        };
        eg.parse_and_run_program(None, source).unwrap();
        eg.parse_and_run_program(None, "(check (effsafe_effectful_A (A0)))")
            .unwrap();
    }
}

#[test]
fn nested_deferred_operands_are_evaluated_once() {
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(None, "(datatype A (A0) (Pair A A))")
        .unwrap();
    let expr = eg.parser.get_expr_from_string(None, "(A0)").unwrap();
    let (sort, value) = eg.eval_expr(&expr).unwrap();
    let count = Arc::new(AtomicUsize::new(0));
    eg.add_write_primitive(
        Constant {
            name: "tick!",
            sort,
            value,
            count: count.clone(),
        },
        None,
    );
    eg.parser.macros().register(
        Space::Expr,
        "twice!",
        Arc::new(|input: &Syntax, cx: &mut MacroContext<'_>| {
            let (_, args, _) = input.expect_call("twice!")?;
            let operand = cx.parser().parse_expr(&args[0])?;
            Ok(Expansion::Deferred(Deferred {
                operands: vec![operand],
                constraints: vec![SortConstraint::Same(0, 1)],
                finish: Arc::new(|cx, args, _| {
                    Ok(Completion::Expr(
                        cx.call("Pair", vec![args[0].clone(), args[0].clone()])?,
                    ))
                }),
            }))
        }),
    );
    eg.parse_and_run_program(None, "(set-effectful (twice! (tick!)))")
        .unwrap();
    assert_eq!(count.load(Ordering::SeqCst), 1);
    eg.parse_and_run_program(None, "(check (effsafe_effectful_A (Pair (A0) (A0))))")
        .unwrap();
}

#[test]
fn primitive_declarations_work_during_resolve_only_and_replay() {
    let source =
        "(primitive twice (i64) i64 (+ _0 _0)) (relation R (i64)) (rule () ((R (twice 3))))";
    let resolve = || {
        new_experimental_egraph()
            .resolve_program(None, source)
            .unwrap()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n")
    };
    let program = resolve();
    assert_eq!(program, resolve());
    let mut eg = new_experimental_egraph();
    eg.parser.ensure_no_reserved_symbols = false;
    eg.parse_and_run_program(None, &program).unwrap();
    eg.parse_and_run_program(None, "(run 1) (check (R 6))")
        .unwrap();
}

#[test]
fn dynamic_cost_preserves_partial_expansion_of_datatype_headers() {
    let mut eg = new_experimental_egraph();
    let constructor = eg.parser.macros().lookup(Space::Command, "constructor");
    eg.parser.macros().register(
        Space::Command,
        "constructor",
        Arc::new(move |input: &Syntax, cx: &mut MacroContext<'_>| {
            assert!(cx.types()?.get_sort_by_name("Trees").is_some());
            constructor.apply(input, cx)
        }),
    );
    eg.parse_and_run_program(None, "
        (with-dynamic-cost (datatype* (Tree (Leaf i64) (Node Trees :regions (0))) (sort Trees (Vec Tree))))
        (set-cost (Leaf 3) 9)
        (check (= (cost_table_Leaf 3) 9))
    ").unwrap();
}

#[test]
fn for_and_with_ruleset_compose_with_inferred_fresh() {
    let mut eg = new_experimental_egraph();
    eg.parse_and_run_program(
        None,
        "
        (datatype A (A0)) (relation Input (i64)) (relation Seen (A))
        (Input 1)
        (for ((Input x)) ((let a (unstable-fresh!)) (set-effectful a) (Seen a)))
        (check (Seen a) (effsafe_effectful_A a))
        (ruleset more)
        (with-ruleset more (rule ((Seen a)) ((let b (unstable-fresh!)) (Seen b))))
        (run more 1)
    ",
    )
    .unwrap();
}
