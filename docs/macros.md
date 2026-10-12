# Macro branch

This branch ports the experimental macros to egglog's unified transformer API.
It is based on the effect-safe extraction work in PR #77. The egglog dependency
is pinned to [egglog commit 3ff59d90](https://github.com/oflatt-claude/egglog/commit/3ff59d9076da9a08885a038094ff4ec0948c0129)
on the companion `oflatt/unified-macros` branch.

`for`, `with-ruleset`, `with-dynamic-cost`, `set-cost`, the `:regions` constructor
extension, `unstable-fresh!`, and `set-effectful` all use one registration API.
`unstable-fresh!` and `set-effectful` return deferred results from that interface.
Their constraints join the actual rule inference problem; completion receives
resolved operands and body bindings.

```lisp
(datatype State (Initial))
(datatype Value (Constant i64))
(relation Input (i64))
(relation Seen (State))
(Input 5)

(rule ((Input key))
  ((let state (unstable-fresh! :cost 3))
   (set-effectful state)
   (Seen state)))
(run 1)
(check (Seen state) (effsafe_effectful_State state))
```

`Seen` supplies the result sort even though it appears after both macro calls.
An explicit `(unstable-fresh! State)` or `(set-effectful State expr)` annotation
is still accepted. Without enough information to choose a sort, expansion
reports an inference error instead of guessing.

Fresh values are keyed by the complete local body-binding tuple. Each syntactic
occurrence has its own constructor, so two occurrences can have different
inferred sorts, costs, and `:unextractable` settings. This deliberately removes
the old behavior where the first occurrence's options controlled all fresh
values in a rule. Repeated evaluation of the same match reuses its value.

Constructor annotations use a captured constructor binding. `datatype*` emits
all nominal headers and parameterized sorts before invoking constructor macros.
`with-dynamic-cost` maps the resulting commands lazily, preserving that order
and the `effsafe-regions` commands attached by the constructor extension:

```lisp
(with-dynamic-cost
  (datatype*
    (Tree (Leaf i64) (Node Trees :regions (0)))
    (sort Trees (Vec Tree))))
(set-cost (Leaf 3) 9)
(check (= (cost_table_Leaf 3) 9))
```

`(primitive ...)` now declares and checks its signature/body without accessing
the database. Runtime installation is separate. `resolve_program` therefore
knows about earlier primitive definitions, and its emitted program can be
replayed with the experimental runtime installed.

Deferred macros currently require a rule head or top-level action. Generate
new types needed to infer a rule before that rule, for example through an
explicit `(derive-record-view Packet)` command. The implementation does not
iterate arbitrary type-dependent declarations and inference to a fixed point.

See egglog's `docs/macros.md` for the author-facing API, and
`tests/unified_macros.rs` for composition, overload filtering, operand sharing,
partial declaration expansion, and deterministic resolve/replay tests. The
existing effect-safe review regressions also run against this implementation.
