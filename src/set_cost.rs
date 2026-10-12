//! Runtime-configurable extraction costs.
//!
//! Wrap datatype or constructor declarations in `with-dynamic-cost` to create
//! a cost table for each extractable constructor. `set-cost` updates a node's
//! cost, and the replacement `extract` command reads those costs:
//!
//! ```text
//! (with-dynamic-cost
//!   (datatype Math (Num i64) (Add Math Math)))
//! (set-cost (Num 1) 100)
//! (extract (Num 1))
//! ```
//!
//! Nodes without an assigned dynamic cost retain their normal tree-additive
//! cost. Costs must be non-negative.

use crate::{
    Error,
    effsafe_extract::Roots,
    greedy_dag_extract::{
        Extractor, extract_best_greedy_dag, extract_variants_greedy_dag, split_trailing_extractor,
    },
};
use egglog::macros::{Expansion, Fragment, Macro, MacroContext, Space, Syntax};
use egglog::{
    ArcSort, CommandOutput, EGraph, Enode, RawValues, Read, TermId, UserDefinedCommand, Value,
    ast::*,
    extract::{DEFAULT_COST_MODEL, DagCostModel, DefaultCost, TreeCostModelFromDag},
    span,
    util::FreshGen,
};
use egglog_ast::span::Span;
use std::sync::Arc;

/// Registers `with-dynamic-cost`, `set-cost`, and the dynamic-cost `extract`
/// command on an e-graph.
///
/// [`new_experimental_egraph`](crate::new_experimental_egraph) calls this
/// automatically.
pub fn add_set_cost(egraph: &mut EGraph) {
    egraph.parser.macros().register(
        Space::Command,
        "with-dynamic-cost",
        Arc::new(SetCostDeclarations),
    );
    egraph
        .parser
        .macros()
        .register(Space::Action, "set-cost", Arc::new(SetCost));
    egraph
        .add_command("extract".into(), Arc::new(CustomExtract))
        .unwrap();
}

struct SetCost;

impl Macro for SetCost {
    fn expand(&self, input: &Syntax, cx: &mut MacroContext<'_>) -> Result<Expansion, ParseError> {
        let (_, args, span) = input.expect_call("macro call")?;
        Ok(Fragment::Actions(self.parse(args, span, cx.parser())?).into())
    }
}

impl SetCost {
    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Action>, ParseError> {
        match args {
            [call, value] => {
                let (func, args, call_span) = call.expect_call("table lookup")?;
                let cost_table_name = get_cost_table_name(&func);
                let args = map_fallible(args, parser, Parser::parse_expr)?;
                let value = parser.parse_expr(value)?;

                let vs = (0..args.len())
                    .map(|_| parser.symbol_gen.fresh("set_cost_var"))
                    .collect::<Vec<_>>();
                let (args, mut actions): (Vec<Expr>, Vec<Action>) = vs
                    .into_iter()
                    .zip(args)
                    .map(|(v, e)| {
                        let span = e.span().clone();
                        (Expr::Var(span.clone(), v.clone()), Action::Let(span, v, e))
                    })
                    .unzip();

                // We don't create costs for nodes that don't exist.
                actions.push(Action::Expr(
                    span.clone(),
                    Expr::Call(call_span.clone(), func, args.clone()),
                ));
                actions.push(Action::Set(span, cost_table_name, args, value));
                Ok(actions)
            }
            _ => Err(ParseError(
                span,
                "usage: (set-cost (<table name> <expr>*) <expr>)".to_string(),
            )),
        }
    }
}

struct SetCostDeclarations;

impl Macro for SetCostDeclarations {
    fn expand(&self, input: &Syntax, _cx: &mut MacroContext<'_>) -> Result<Expansion, ParseError> {
        let (_, declarations, _) = input.expect_call("with-dynamic-cost")?;
        let mapper = Arc::new(|command: Command, _: &mut MacroContext<'_>| {
            let costs = match &command {
                Command::Datatype { variants, .. } => {
                    generate_cost_table_commands_from_variants(variants)
                }
                Command::Datatypes { datatypes, .. } => datatypes
                    .iter()
                    .flat_map(|(_, _, datatype)| match datatype {
                        Subdatatypes::Variants(variants) => {
                            generate_cost_table_commands_from_variants(variants)
                        }
                        Subdatatypes::NewSort(..) => vec![],
                    })
                    .collect(),
                Command::Constructor {
                    name,
                    schema,
                    span,
                    unextractable: false,
                    ..
                } => vec![Command::Function {
                    span: span.clone(),
                    name: get_cost_table_name(name),
                    schema: Schema::new(schema.input.clone(), "i64".into()),
                    merge: None,
                    hidden: false,
                    let_binding: false,
                    term_constructor: None,
                    unextractable: false,
                }],
                _ => vec![],
            };
            Ok(std::iter::once(command).chain(costs).collect())
        });
        let mut result = Vec::new();
        for declaration in declarations {
            // Keep each child unevaluated until preceding generated declarations
            // have been installed. This composes with datatype* and :regions.
            let declaration = declaration.clone();
            let mapper = mapper.clone();
            let wrapper = egglog::macros::MacroBinding::new(
                Space::Command,
                Arc::new(move |input: &Syntax, cx: &mut MacroContext<'_>| {
                    let expanded = cx.expand(Space::Command, input)?;
                    if let Expansion::Parsed(Fragment::Commands(commands)) = &expanded
                        && !commands.iter().any(|command| {
                            matches!(
                                command,
                                Command::Datatype { .. }
                                    | Command::Datatypes { .. }
                                    | Command::Constructor { .. }
                            )
                        })
                    {
                        return Err(ParseError(
                            input.span(),
                            "expected a datatype or constructor declaration".into(),
                        ));
                    }
                    expanded.map_commands(cx, input.span(), mapper.clone())
                }),
            );
            result.push(wrapper.bind(declaration));
        }
        Ok(Expansion::Sequence(result))
    }
}

fn generate_cost_table_commands_from_variants(variants: &[Variant]) -> Vec<Command> {
    variants
        .iter()
        .map(|v| {
            let cost_table_name = get_cost_table_name(&v.name);
            let cost_table_schema = Schema::new(v.types.clone(), "i64".into());

            Command::Function {
                span: v.span.clone(),
                name: cost_table_name,
                schema: cost_table_schema,
                merge: None,
                hidden: false,
                let_binding: false,
                term_constructor: None,
                unextractable: false,
            }
        })
        .collect::<Vec<_>>()
}

fn get_cost_table_name(name: &str) -> String {
    format!("cost_table_{name}")
}

fn map_fallible<T>(
    slice: &[Sexp],
    parser: &mut Parser,
    func: impl Fn(&mut Parser, &Sexp) -> Result<T, ParseError>,
) -> Result<Vec<T>, ParseError> {
    slice
        .iter()
        .map(|sexp| func(parser, sexp))
        .collect::<Result<_, _>>()
}

/// An extraction cost model that reads costs assigned by `set-cost`.
///
/// It falls back to the marginal costs used by [`DEFAULT_COST_MODEL`] for
/// constructors without an assigned dynamic cost. Use this model for custom
/// extractors that should agree with this crate's replacement `extract`
/// command.
#[derive(Clone)]
pub struct DynamicCostModel;

impl DagCostModel<DefaultCost> for DynamicCostModel {
    fn base_value_cost(&self, egraph: &EGraph, sort: &ArcSort, value: Value) -> DefaultCost {
        DagCostModel::base_value_cost(&DEFAULT_COST_MODEL.0, egraph, sort, value)
    }

    fn enode_cost(
        &self,
        egraph: &EGraph,
        func: &egglog::Function,
        enode: &Enode<'_>,
    ) -> DefaultCost {
        let default_cost = || DagCostModel::enode_cost(&DEFAULT_COST_MODEL.0, egraph, func, enode);
        let name = get_cost_table_name(func.name());
        if egraph.get_function(&name).is_some() {
            egraph
                .read(|state| state.lookup(&name, RawValues(enode.children.to_vec())))
                .ok()
                .flatten()
                .map(|c| {
                    let cost = egraph.value_to_base::<i64>(c);
                    assert!(cost >= 0);
                    cost as DefaultCost
                })
                .unwrap_or_else(default_cost)
        } else {
            default_cost()
        }
    }
}

struct CustomExtract;

impl UserDefinedCommand for CustomExtract {
    fn update(
        &self,
        egraph: &mut EGraph,
        args: &[Expr],
    ) -> Result<Vec<CommandOutput>, egglog::Error> {
        let (args, include_subsumed) = crate::effsafe_extract::split_include_subsumed(args);
        let (args, extractor) = split_trailing_extractor(args)?;
        let use_greedy_dag = extractor == Extractor::GreedyDag;
        if include_subsumed && extractor != Extractor::Effsafe {
            return Err(Error::ParseError(ParseError(
                span!(),
                ":include-subsumed is only supported with :extractor effsafe".into(),
            )));
        }
        let (expr, variants) = match args {
            [] => {
                return Err(Error::ParseError(ParseError(
                    span!(),
                    "extract expects an expression and optional variant count".into(),
                )));
            }
            [expr] => (expr, None),
            [expr, variants] => (expr, Some(variants)),
            [_, _, extra, ..] => {
                return Err(Error::ParseError(ParseError(
                    extra.span(),
                    "extract expects an expression, optional variant count, and optional :extractor"
                        .into(),
                )));
            }
        };

        let (sort, value) = egraph.eval_expr(expr)?;
        let n = variants.map(|arg| egraph.eval_expr(arg)).transpose()?;
        let n = if let Some(nv) = n {
            // TODO: egglog does not yet support u64
            if nv.0.name() != "i64" {
                let i64sort = egraph.get_arcsort_by(|s| s.name() == "i64");
                return Err(egglog::Error::TypeError(egglog::TypeError::Mismatch {
                    expr: variants.unwrap().clone(),
                    expected: i64sort,
                    actual: nv.0,
                }));
            }
            egraph.value_to_base::<i64>(nv.1)
        } else {
            0
        };

        if n < 0 {
            return Err(Error::ParseError(ParseError(
                variants.unwrap().span(),
                "Cannot extract negative number of variants".into(),
            )));
        }

        let roots = vec![(sort, value)];

        if extractor == Extractor::Effsafe {
            if n != 0 {
                return Err(Error::ParseError(ParseError(
                    variants.unwrap().span(),
                    "effect-safe extraction does not support variants".into(),
                )));
            }
            let output = crate::effsafe_extract::extract_with_options(
                egraph,
                include_subsumed,
                &Roots::Values(roots),
                None,
            )?;
            let term = output.terms[0];
            let cost = output.costs[0];
            log::info!(
                "extracted effect-safely with cost {cost}: {}",
                output.termdag.to_string(term)
            );
            return Ok(vec![CommandOutput::ExtractBest(output.termdag, cost, term)]);
        }

        // Omitted or zero variant count means best extraction.
        if n == 0 {
            let extracted = if use_greedy_dag {
                extract_best_greedy_dag(egraph, roots, DynamicCostModel)?
            } else {
                egraph
                    .extract_best_with_cost_model(roots, TreeCostModelFromDag(DynamicCostModel))?
            };
            let root = extracted
                .terms
                .into_iter()
                .next()
                .expect("one root was requested")
                .ok_or_else(|| {
                    Error::ExtractError("Unable to find any valid extraction".to_string())
                })?;
            log::info!(
                "extracted with cost {}: {}",
                root.cost,
                extracted.termdag.to_string(root.term)
            );
            Ok(vec![CommandOutput::ExtractBest(
                extracted.termdag,
                root.cost,
                root.term,
            )])
        } else {
            let extracted = if use_greedy_dag {
                extract_variants_greedy_dag(egraph, roots, n as usize, DynamicCostModel)?
            } else {
                egraph.extract_variants_with_cost_model(
                    roots,
                    n as usize,
                    TreeCostModelFromDag(DynamicCostModel),
                )?
            };
            let terms: Vec<TermId> = extracted
                .variants
                .into_iter()
                .next()
                .expect("one root was requested")
                .into_iter()
                .map(|variant| variant.term)
                .collect();
            Ok(vec![CommandOutput::ExtractVariants(
                extracted.termdag,
                terms,
            )])
        }
    }
}
