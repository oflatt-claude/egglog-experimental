//! `(set-effectful e)` marks an inferred equality-sort value. The explicit
//! `(set-effectful Sort e)` annotation is useful when the rule is ambiguous.

use egglog::ast::{Command, ParseError, ResolvedAction, ResolvedActions, ResolvedExprExt};
use egglog::macros::{
    Completion, Deferred, Expansion, Macro, MacroContext, SortConstraint, Syntax,
};
use std::sync::Arc;

/// The macro's name in programs.
pub const SET_EFFECTFUL: &str = "set-effectful";
const RELATION_PREFIX: &str = "effsafe_effectful_";

/// The generated relation holding the effectful e-classes of `sort`.
pub fn effectful_relation(sort: &str) -> String {
    format!("{RELATION_PREFIX}{sort}")
}

/// Recover the equality sort associated with a generated mark relation.
pub fn effectful_relation_sort(relation: &str) -> Option<&str> {
    relation.strip_prefix(RELATION_PREFIX)
}

/// Mark an effectful value after the enclosing inference region has been solved.
pub struct SetEffectful;
impl Macro for SetEffectful {
    fn expand(&self, input: &Syntax, cx: &mut MacroContext<'_>) -> Result<Expansion, ParseError> {
        let (_, args, span) = input.expect_call("set-effectful")?;
        let mut constraints = vec![SortConstraint::EqSort(0)];
        let expr = match args {
            [expr] => expr,
            [sort, expr] => {
                let name = sort.expect_atom("sort annotation")?;
                let sort = cx
                    .types()?
                    .get_sort_by_name(&name)
                    .ok_or_else(|| ParseError(sort.span(), format!("unknown sort {name}")))?
                    .clone();
                if !sort.is_eq_sort() {
                    return Err(ParseError(
                        span.clone(),
                        format!("{name} is not an eq sort"),
                    ));
                }
                constraints.push(SortConstraint::Is(0, sort));
                expr
            }
            _ => {
                return Err(ParseError(
                    span,
                    "usage: (set-effectful [Sort] expr)".into(),
                ));
            }
        };
        let operand = cx.parser().parse_expr(expr)?;
        Ok(Expansion::Deferred(Deferred {
            operands: vec![operand],
            constraints,
            finish: Arc::new(move |cx, operands, _| {
                let sort = operands[0].output_type();
                let relation = effectful_relation(sort.name());
                if cx.types().get_func_type(&relation).is_none() {
                    cx.declare(Command::Relation {
                        span: span.clone(),
                        name: relation.clone(),
                        inputs: vec![sort.name().to_owned()],
                    })?;
                }
                let call = cx.call(&relation, operands.to_vec())?;
                Ok(Completion::Actions(ResolvedActions::new(vec![
                    ResolvedAction::Expr(span.clone(), call),
                ])))
            }),
        }))
    }
}
