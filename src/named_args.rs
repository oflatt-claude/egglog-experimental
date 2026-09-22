//! Named arguments for constructors, functions, relations, and datatypes.
//!
//! This module lets declarations name their fields:
//!
//! ```text
//! (constructor MyCar (:color Color :numwheel i64) Vehicle)
//! (function foo (:a i64 :b i64) i64 :no-merge)
//! (relation edge (:from Node :to Node))
//! (datatype Vehicle (MyCar :color Color :numwheel i64))
//! ```
//!
//! Once a name is declared with named fields, call sites may pass arguments by
//! name in any order, mix leading positional arguments with trailing named
//! ones, and use a trailing `...` to bind every unspecified field to a fresh
//! variable:
//!
//! ```text
//! (rule ((MyCar :color c ...))        ((Use c)))   ; :numwheel bound to a fresh var
//! (rule ((MyCar c ...))               ((Use c)))   ; c is :color, :numwheel fresh
//! (rule ((MyCar :numwheel w :color c)) ((Use c)))  ; any order
//! ```
//!
//! # Implementation strategy
//!
//! The declaration commands (`constructor`, `function`, `relation`, `datatype`,
//! `datatype*`) are registered as parser command macros that shadow the
//! built-ins. A declaration emits the ordinary positional command *and*
//! registers a per-name expression macro on the parser: [`NamedCall`] when it
//! named its fields, [`PositionalCall`] when it did not. Because facts and
//! actions both flow through [`Parser::parse_expr`], that one expression macro
//! rewrites named and `...` call syntax in queries, actions, user-defined
//! command arguments, and nested positions alike.
//!
//! Field names live on the [`Parser`], which is the right place for them to
//! live: the parser is part of the e-graph, so it is cloned with an
//! [`EGraph`](egglog::EGraph) and snapshotted and restored by `push`/`pop`.
//! Two e-graphs can therefore give the same name different fields without
//! interfering.
//!
//! Two details make source order match declaration scope, which is what the
//! parser has to rely on:
//!
//! * `(include ...)` is expanded here rather than left for egglog to read after
//!   parsing, so an included declaration is registered before the calls that
//!   follow it are parsed.
//! * A positional declaration registers [`PositionalCall`], which shadows any
//!   field names registered for that name earlier. egglog rejects redeclaring a
//!   bound name, so the only way one name is declared twice is
//!   `(push)`/declare/`(pop)`/declare, where the later declaration in the source
//!   is exactly the one that is live afterwards.

use egglog::ast::*;
use egglog::util::FreshGen;
use std::sync::Arc;

/// True for the tokens that act as markers in a call: the `...` ellipsis and
/// any `:name` keyword. Such tokens can never be a plain argument value.
fn is_marker(sexp: &Sexp) -> bool {
    matches!(sexp, Sexp::Atom(a, _) if a == "..." || a.starts_with(':'))
}

/// Add named-argument support to a parser: the declaration command macros
/// (`constructor`, `function`, `relation`, `datatype`, `datatype*`), the
/// `set`/`delete`/`subsume` action macros, and `include`. Use this to add named
/// arguments to a plain `egglog` parser without pulling in the rest of
/// egglog-experimental (e.g. `egraph.parser` on a bare `egglog::EGraph`).
pub fn register_named_args(parser: &mut Parser) {
    parser.add_command_macro(Arc::new(Include));
    parser.add_command_macro(Arc::new(NamedConstructor));
    parser.add_command_macro(Arc::new(NamedFunction));
    parser.add_command_macro(Arc::new(NamedRelation));
    parser.add_command_macro(Arc::new(NamedDatatype));
    parser.add_command_macro(Arc::new(NamedDatatypes));
    parser.add_action_macro(Arc::new(NamedSet));
    parser.add_action_macro(Arc::new(NamedChange::delete()));
    parser.add_action_macro(Arc::new(NamedChange::subsume()));
}

/// Expression macro registered for each constructor/function/relation/variant
/// declared with named fields. Rewrites a call using named args, leading
/// positional args, and an optional trailing `...` into a positional
/// `Expr::Call`.
struct NamedCall {
    /// The declared name (constructor/function/relation/variant).
    name: String,
    /// Field names in declaration order.
    arg_names: Vec<String>,
}

impl Macro<Expr> for NamedCall {
    fn name(&self) -> &str {
        &self.name
    }

    fn parse(&self, args: &[Sexp], span: Span, parser: &mut Parser) -> Result<Expr, ParseError> {
        let arity = self.arg_names.len();
        let mut slots: Vec<Option<Expr>> = (0..arity).map(|_| None).collect();
        let mut has_ellipsis = false;
        let mut seen_named = false;
        let mut next_positional = 0usize;

        let mut i = 0;
        while i < args.len() {
            if has_ellipsis {
                return error(args[i].span(), "`...` must be the last argument");
            }
            match &args[i] {
                Sexp::Atom(a, _) if a == "..." => {
                    has_ellipsis = true;
                    i += 1;
                }
                Sexp::Atom(a, key_span) if a.starts_with(':') => {
                    seen_named = true;
                    let key = &a[1..];
                    let pos = self
                        .arg_names
                        .iter()
                        .position(|p| p == key)
                        .ok_or_else(|| {
                            ParseError(
                                key_span.clone(),
                                format!("`{}` has no argument named `{key}`", self.name),
                            )
                        })?;
                    if slots[pos].is_some() {
                        return error(
                            key_span.clone(),
                            &format!(
                                "argument `{key}` of `{}` specified more than once",
                                self.name
                            ),
                        );
                    }
                    i += 1;
                    let Some(value_sexp) = args.get(i) else {
                        return error(key_span.clone(), &format!("`:{key}` requires a value"));
                    };
                    if is_marker(value_sexp) {
                        return error(value_sexp.span(), &format!("expected a value for `:{key}`"));
                    }
                    slots[pos] = Some(parser.parse_expr(value_sexp)?);
                    i += 1;
                }
                other => {
                    if seen_named {
                        return error(
                            other.span(),
                            "positional arguments must come before named arguments",
                        );
                    }
                    if next_positional >= arity {
                        return error(
                            other.span(),
                            &format!(
                                "`{}` takes {arity} argument(s) but was given more",
                                self.name
                            ),
                        );
                    }
                    slots[next_positional] = Some(parser.parse_expr(other)?);
                    next_positional += 1;
                    i += 1;
                }
            }
        }

        let mut final_args = Vec::with_capacity(arity);
        let mut missing = Vec::new();
        for (idx, slot) in slots.into_iter().enumerate() {
            match slot {
                Some(expr) => final_args.push(expr),
                // A fixed hint, as wildcard parsing uses: hints taken from the
                // field names can collide with each other, since "x" at count 1
                // and "x1" at count 0 both mint "x1".
                None if has_ellipsis => {
                    let fresh = parser.symbol_gen.fresh("_");
                    final_args.push(Expr::Var(span.clone(), fresh));
                }
                None => missing.push(self.arg_names[idx].clone()),
            }
        }

        if !missing.is_empty() {
            return error(
                span,
                &format!(
                    "`{}` is missing argument(s): {} (add `...` to bind the rest to fresh variables)",
                    self.name,
                    missing.join(", ")
                ),
            );
        }

        Ok(Expr::Call(span, self.name.clone(), final_args))
    }
}

fn error<T>(span: Span, message: &str) -> Result<T, ParseError> {
    Err(ParseError(span, message.to_string()))
}

/// Parse a table-lookup call through `parse_expr` (so named-argument expression
/// macros fire) and destructure it into `(function, args)`. This is what lets
/// `set`/`delete`/`subsume` accept named arguments; the built-ins split the
/// head and arguments by hand and would otherwise bypass the macro.
fn parse_table_call(parser: &mut Parser, sexp: &Sexp) -> Result<(String, Vec<Expr>), ParseError> {
    match parser.parse_expr(sexp)? {
        Expr::Call(_, func, args) => Ok((func, args)),
        other => error(
            other.span(),
            "expected a table lookup of the form (<table> <args>*)",
        ),
    }
}

/// Record how a declaration spells its arguments.
///
/// A positional declaration registers [`PositionalCall`] rather than nothing at
/// all, so that it shadows field names registered for the same name earlier.
fn register_call(parser: &mut Parser, name: &str, arg_names: Option<Vec<String>>) {
    match arg_names {
        Some(arg_names) => parser.add_expr_macro(Arc::new(NamedCall {
            name: name.to_string(),
            arg_names,
        })),
        None => parser.add_expr_macro(Arc::new(PositionalCall {
            name: name.to_string(),
        })),
    }
}

/// Expression macro registered for each declaration that does *not* name its
/// fields. It parses exactly as the built-in call syntax does, and exists only
/// to shadow field names registered for this name before a `(push)`/`(pop)`.
struct PositionalCall {
    name: String,
}

impl Macro<Expr> for PositionalCall {
    fn name(&self) -> &str {
        &self.name
    }

    fn parse(&self, args: &[Sexp], span: Span, parser: &mut Parser) -> Result<Expr, ParseError> {
        let args = args
            .iter()
            .map(|arg| parser.parse_expr(arg))
            .collect::<Result<_, _>>()?;
        Ok(Expr::Call(span, self.name.clone(), args))
    }
}

/// `(include <file>)`, expanded while parsing.
///
/// egglog otherwise keeps `Command::Include` and reads the file after the whole
/// program has been parsed, which is too late for a declaration in that file to
/// be registered before the calls that follow the include are parsed.
struct Include;

impl Macro<Vec<Command>> for Include {
    fn name(&self) -> &str {
        "include"
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let [file] = args else {
            return error(span, "usage: (include <file name>)");
        };
        let file = file.expect_string("file name")?;
        let contents = std::fs::read_to_string(&file)
            .map_err(|e| ParseError(span.clone(), format!("could not read {file}: {e}")))?;
        parser.get_program_from_string(Some(file), &contents)
    }
}

/// Read the `:name Sort` pair starting at `items[i]`, validating it against the
/// names collected so far. Schema lists and datatype variants spell the same
/// pair in different surroundings, so they share this.
fn read_named_field(
    items: &[Sexp],
    i: usize,
    seen: &[String],
) -> Result<(String, String), ParseError> {
    let key_span = items[i].span();
    let name = items[i].expect_atom("argument name")?[1..].to_string();
    let Some(sort_sexp) = items.get(i + 1) else {
        return error(key_span, &format!("argument `{name}` is missing its sort"));
    };
    let sort = sort_sexp.expect_atom("argument sort")?;
    if sort.starts_with(':') {
        return error(
            sort_sexp.span(),
            &format!("expected a sort for `{name}` but found `{sort}`"),
        );
    }
    if seen.contains(&name) {
        return error(key_span, &format!("duplicate argument name `{name}`"));
    }
    Ok((name, sort))
}

/// Split a schema input list into optional field names and the list of sort
/// names. Returns `Some(names)` when the schema is named (`(:a T :b U)`), or
/// `None` when it is positional (`(T U)`). Declarations must name either all
/// fields or none.
fn parse_schema_list(input: &Sexp) -> Result<(Option<Vec<String>>, Vec<String>), ParseError> {
    let items = input.expect_list("input sorts")?;

    let named = matches!(items.first(), Some(Sexp::Atom(a, _)) if a.starts_with(':'));
    if !named {
        let mut sorts = Vec::with_capacity(items.len());
        for item in items {
            let sort = item.expect_atom("input sort")?;
            if sort.starts_with(':') {
                return error(
                    item.span(),
                    &format!("unexpected named argument `{sort}`; name either all fields or none"),
                );
            }
            sorts.push(sort);
        }
        return Ok((None, sorts));
    }

    let mut names = Vec::new();
    let mut sorts = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let key = items[i].expect_atom("argument name")?;
        if !key.starts_with(':') {
            return error(
                items[i].span(),
                &format!("expected `:name` but found `{key}`; name either all fields or none"),
            );
        }
        let (name, sort) = read_named_field(items, i, &names)?;
        names.push(name);
        sorts.push(sort);
        i += 2;
    }
    Ok((Some(names), sorts))
}

/// Parse a single datatype variant, registering a `NamedCall` when the
/// variant names its fields. Positional variants are delegated to the built-in
/// parser. Because `:cost` and `:unextractable` share the variant's flat
/// argument list, they are always treated as options, so those two words cannot
/// be used as field names in a variant.
fn process_variant(parser: &mut Parser, sexp: &Sexp) -> Result<Variant, ParseError> {
    let (head, tail, span) = sexp.expect_call("datatype variant")?;

    let is_named = matches!(
        tail.first(),
        Some(Sexp::Atom(a, _)) if a.starts_with(':') && a != ":cost" && a != ":unextractable"
    );
    if !is_named {
        let variant = parser.variant(sexp)?;
        register_call(parser, &variant.name, None);
        return Ok(variant);
    }

    let mut names = Vec::new();
    let mut types = Vec::new();
    let mut cost = None;
    let mut unextractable = false;

    let mut i = 0;
    while i < tail.len() {
        let key = tail[i].expect_atom("argument name or option")?;
        match key.as_str() {
            ":unextractable" => {
                unextractable = true;
                i += 1;
            }
            ":cost" => {
                i += 1;
                let Some(c) = tail.get(i) else {
                    return error(span.clone(), ":cost requires a value");
                };
                cost = Some(c.expect_uint("cost")?);
                i += 1;
            }
            k if k.starts_with(':') => {
                let (name, sort) = read_named_field(tail, i, &names)?;
                names.push(name);
                types.push(sort);
                i += 2;
            }
            _ => {
                return error(
                    tail[i].span(),
                    &format!(
                        "expected `:name` or an option but found `{key}`; name either all fields or none"
                    ),
                );
            }
        }
    }

    register_call(parser, &head, Some(names));
    Ok(Variant {
        span,
        name: head,
        types,
        cost,
        unextractable,
    })
}

/// `(set (<table> <args>*) <expr>)` routed through `parse_expr` for named args.
struct NamedSet;

impl Macro<Vec<Action>> for NamedSet {
    fn name(&self) -> &str {
        "set"
    }

    fn parse(
        &self,
        tail: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Action>, ParseError> {
        let [call, value] = tail else {
            return error(span, "usage: (set (<table name> <expr>*) <expr>)");
        };
        let (func, args) = parse_table_call(parser, call)?;
        let value = parser.parse_expr(value)?;
        Ok(vec![Action::Set(span, func, args, value)])
    }
}

/// `(delete (<table> <args>*))` / `(subsume (<table> <args>*))` routed through
/// `parse_expr` for named args.
struct NamedChange {
    keyword: &'static str,
    change: Change,
}

impl NamedChange {
    /// The macro for `(delete (<table> <args>*))`.
    fn delete() -> Self {
        Self {
            keyword: "delete",
            change: Change::Delete,
        }
    }

    /// The macro for `(subsume (<table> <args>*))`.
    fn subsume() -> Self {
        Self {
            keyword: "subsume",
            change: Change::Subsume,
        }
    }
}

impl Macro<Vec<Action>> for NamedChange {
    fn name(&self) -> &str {
        self.keyword
    }

    fn parse(
        &self,
        tail: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Action>, ParseError> {
        let [call] = tail else {
            return error(span, "usage: (<change> (<table name> <expr>*))");
        };
        let (func, args) = parse_table_call(parser, call)?;
        Ok(vec![Action::Change(span, self.change, func, args)])
    }
}

/// `(constructor <name> (<schema>) <output> <options>*)` with named-field support.
struct NamedConstructor;

impl Macro<Vec<Command>> for NamedConstructor {
    fn name(&self) -> &str {
        "constructor"
    }

    fn parse(
        &self,
        tail: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let [name, inputs, output, rest @ ..] = tail else {
            return error(
                span,
                "usage: (constructor <name> (<input sort>*) <output sort> <options>*)",
            );
        };
        let name = name.expect_atom("constructor name")?;
        let (names_opt, input) = parse_schema_list(inputs)?;
        let output = output.expect_atom("output sort")?;

        let mut cost = None;
        let mut unextractable = false;
        let mut hidden = false;
        let mut let_binding = false;
        for (key, val) in parser.parse_options(rest)? {
            match (key, val) {
                (":unextractable", []) => unextractable = true,
                (":internal-hidden", []) => hidden = true,
                (":internal-let", []) => let_binding = true,
                (":cost", [c]) => cost = Some(c.expect_uint("cost")?),
                _ => return error(span.clone(), "could not parse constructor options"),
            }
        }

        register_call(parser, &name, names_opt);

        Ok(vec![Command::Constructor {
            span,
            name,
            schema: Schema { input, output },
            cost,
            unextractable,
            hidden,
            let_binding,
            term_constructor: None,
        }])
    }
}

/// `(function <name> (<schema>) <output> <options>*)` with named-field support.
struct NamedFunction;

impl Macro<Vec<Command>> for NamedFunction {
    fn name(&self) -> &str {
        "function"
    }

    fn parse(
        &self,
        tail: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let [name, inputs, output, rest @ ..] = tail else {
            return error(
                span,
                "usage: (function <name> (<input sort>*) <output sort> <options>*)",
            );
        };
        let name = name.expect_atom("function name")?;
        let (names_opt, input) = parse_schema_list(inputs)?;
        let output = output.expect_atom("output sort")?;

        let mut merge = None;
        let mut hidden = false;
        let mut let_binding = false;
        let mut term_constructor = None;
        let mut unextractable = false;
        for (key, val) in parser.parse_options(rest)? {
            match (key, val) {
                (":no-merge", []) => {
                    if merge.is_some() {
                        return error(span.clone(), "conflicting merge options");
                    }
                    merge = Some(None);
                }
                (":merge", [e]) => {
                    if merge.is_some() {
                        return error(span.clone(), "conflicting merge options");
                    }
                    merge = Some(Some(parser.parse_expr(e)?));
                }
                (":internal-hidden", []) => hidden = true,
                (":internal-let", []) => let_binding = true,
                (":unextractable", []) => unextractable = true,
                (":internal-term-constructor", [tc]) => {
                    term_constructor = Some(tc.expect_atom("term constructor name")?)
                }
                _ => return error(span.clone(), "could not parse function options"),
            }
        }
        let Some(merge) = merge else {
            return error(span, "functions are required to specify merge behaviour");
        };

        register_call(parser, &name, names_opt);

        Ok(vec![Command::Function {
            span,
            name,
            schema: Schema { input, output },
            merge,
            hidden,
            let_binding,
            term_constructor,
            unextractable,
        }])
    }
}

/// `(relation <name> (<schema>))` with named-field support.
struct NamedRelation;

impl Macro<Vec<Command>> for NamedRelation {
    fn name(&self) -> &str {
        "relation"
    }

    fn parse(
        &self,
        tail: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let [name, inputs] = tail else {
            return error(span, "usage: (relation <name> (<input sort>*))");
        };
        let name = name.expect_atom("relation name")?;
        let (names_opt, inputs) = parse_schema_list(inputs)?;

        register_call(parser, &name, names_opt);

        Ok(vec![Command::Relation { span, name, inputs }])
    }
}

/// `(datatype <name> <variant>*)` with named-field support per variant.
struct NamedDatatype;

impl Macro<Vec<Command>> for NamedDatatype {
    fn name(&self) -> &str {
        "datatype"
    }

    fn parse(
        &self,
        tail: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let [name, variants @ ..] = tail else {
            return error(span, "usage: (datatype <name> <variant>*)");
        };
        let name = name.expect_atom("sort name")?;
        let mut parsed = Vec::with_capacity(variants.len());
        for variant in variants {
            parsed.push(process_variant(parser, variant)?);
        }
        Ok(vec![Command::Datatype {
            span,
            name,
            variants: parsed,
        }])
    }
}

/// `(datatype* <datatype>*)` with named-field support per variant.
struct NamedDatatypes;

impl Macro<Vec<Command>> for NamedDatatypes {
    fn name(&self) -> &str {
        "datatype*"
    }

    fn parse(
        &self,
        tail: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let mut datatypes = Vec::with_capacity(tail.len());
        for sub in tail {
            let (head, subtail, sub_span) = sub.expect_call("datatype")?;
            if head == "sort" {
                // Container-sort declaration: reuse the built-in parser verbatim.
                datatypes.push(parser.rec_datatype(sub)?);
            } else {
                let mut variants = Vec::with_capacity(subtail.len());
                for variant in subtail {
                    variants.push(process_variant(parser, variant)?);
                }
                datatypes.push((sub_span, head, Subdatatypes::Variants(variants)));
            }
        }
        Ok(vec![Command::Datatypes { span, datatypes }])
    }
}
