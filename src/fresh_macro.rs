use std::sync::Arc;

use egglog::ast::{Command, Literal, ParseError, ResolvedExpr, Schema, Sexp};
use egglog::macros::{
    Completion, Deferred, Expansion, Macro, MacroContext, SortConstraint, Syntax,
};

/// Create a value for each query match and syntactic occurrence. Its equality
/// sort can be inferred from uses anywhere in the enclosing rule.
pub struct FreshMacro;

impl Macro for FreshMacro {
    fn expand(&self, input: &Syntax, cx: &mut MacroContext<'_>) -> Result<Expansion, ParseError> {
        let (_, mut args, span) = input.expect_call("unstable-fresh!")?;
        let mut constraints = vec![SortConstraint::EqSort(0)];
        if let Some(Sexp::Atom(name, sort_span)) = args.first()
            && !name.starts_with(':')
        {
            let sort = cx
                .types()?
                .get_sort_by_name(name)
                .ok_or_else(|| ParseError(sort_span.clone(), format!("unknown sort {name}")))?
                .clone();
            constraints.push(SortConstraint::Is(0, sort));
            args = &args[1..];
        }
        let mut cost = Some(1);
        let mut unextractable = false;
        while let Some(option) = args.first() {
            match option.expect_atom("fresh option")?.as_str() {
                ":cost" => {
                    let Some(value) = args.get(1) else {
                        return Err(ParseError(
                            option.span(),
                            ":cost requires a nonnegative integer".into(),
                        ));
                    };
                    cost = Some(value.expect_uint("cost")?);
                    args = &args[2..];
                }
                ":unextractable" => {
                    unextractable = true;
                    args = &args[1..];
                }
                unknown => {
                    return Err(ParseError(
                        option.span(),
                        format!("unknown unstable-fresh! option {unknown}"),
                    ));
                }
            }
        }
        // A separate constructor per occurrence also separates differing output
        // sorts and extraction options. The full query binding tuple is its key.
        let constructor = cx.fresh("GeneratedFreshTable");
        Ok(Expansion::Deferred(Deferred {
            operands: vec![],
            constraints,
            finish: Arc::new(move |cx, _, sort| {
                let mut inputs: Vec<_> = cx
                    .query_bindings
                    .iter()
                    .map(|var| var.sort.name().to_owned())
                    .collect();
                inputs.push("i64".into());
                cx.declare(Command::Constructor {
                    span: span.clone(),
                    name: constructor.clone(),
                    schema: Schema {
                        input: inputs,
                        output: sort.name().to_owned(),
                    },
                    cost,
                    unextractable,
                    hidden: false,
                    let_binding: false,
                    term_constructor: None,
                })?;
                let mut args: Vec<_> = cx
                    .query_bindings
                    .iter()
                    .map(|var| ResolvedExpr::Var(span.clone(), var.clone()))
                    .collect();
                // The constructor identity distinguishes occurrences; this column
                // retains the explicit occurrence component of a fresh key.
                args.push(ResolvedExpr::Lit(span.clone(), Literal::Int(0)));
                Ok(Completion::Expr(cx.call(&constructor, args)?))
            }),
        }))
    }
}
