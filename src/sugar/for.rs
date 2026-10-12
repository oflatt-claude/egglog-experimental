use egglog::macros::{Expansion, Fragment, Macro, MacroContext, Syntax};
use egglog::{ast::*, util::FreshGen};
use egglog_ast::generic_ast::RuleEvalMode;
use egglog_ast::span::Span;

/// Parse-time macro for applying actions once to all current query matches.
///
/// ```text
/// (for ((source x))
///      ((destination x)))
/// ```
///
/// The macro creates a temporary ruleset containing one rule and runs that
/// ruleset for one iteration.
pub struct For;

impl Macro for For {
    fn expand(&self, input: &Syntax, cx: &mut MacroContext<'_>) -> Result<Expansion, ParseError> {
        let (_, args, span) = input.expect_call("macro call")?;
        Ok(Fragment::Commands(self.parse(args, span, cx.parser())?).into())
    }
}

impl For {
    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        if args.len() != 2 {
            return Err(ParseError(
                span,
                "expected (for <query> <action>)".to_string(),
            ));
        }

        let ruleset = parser.symbol_gen.fresh("for_ruleset");
        let rulename = parser.symbol_gen.fresh("for_rule");
        let query = args[0]
            .expect_list("query")?
            .iter()
            .map(|s| parser.parse_fact(s))
            .collect::<Result<Vec<_>, _>>()?;
        let action = args[1]
            .expect_list("action")?
            .iter()
            .map(|s| parser.parse_action(s))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        let rule = Rule {
            span: span.clone(),
            head: Actions::new(action),
            body: query,
            name: rulename,
            ruleset: ruleset.clone(),
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        };

        Ok(vec![
            Command::AddRuleset(span.clone(), ruleset.clone()),
            Command::Rule { rule },
            Command::RunSchedule(Schedule::Run(
                span.clone(),
                RunConfig {
                    ruleset,
                    until: None,
                },
            )),
        ])
    }
}
