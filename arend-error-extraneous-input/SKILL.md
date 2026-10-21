---
name: arend-error-extraneous-input
description: Diagnose Arend parser errors of the form `extraneous input '<tok>' expecting {...}`. Use when typechecking an .ard file surfaces this exact error class; covers known surface-syntax constructs that trigger it and the minimal fix for each. The token reported is almost never the bug — the real offender is a few tokens earlier.
user-invocable: true
---

# Arend parser error — `extraneous input '<tok>' expecting {...}`

The reported token is **where the parser gave up**, not where the mistake is. The real offender is usually a clause, binding or keyword a few tokens earlier.

**Read the expecting-set first.** If it lists only statement keywords — `{<EOF>, '\open', '\import', '\private', …, '\func', …, '\class', '\record', …}` — the parser abandoned the enclosing definition and resynchronized at top level. The error then sits on the next token it could not use as the start of a statement (often a `{`, `\with` or `(`), which can be lines away from the cause. Look inside the definition that *contains or precedes* that token, especially inside nested blocks. Follow-on typecheck errors on that definition (`Some clauses are missing`, `Cannot infer an expression`) are fallout.

Workflow:

1. Note the token and the expecting-set, then look at the **preceding** construct.
2. Match it against the catalogue below and apply the fix.
3. If nothing matches, delete the suspect clause or binding and see whether the error moves.
4. Once you've found the cause, add it to this catalogue.

---

## Known triggers

### Anonymous `\have` clause: `\have | : T => v`

```arend
\func f (n : Nat) : n = n =>
  \have | : 0 = 0 => idp
  \in idp
```

**Error**, at the binding:

    extraneous input ':' expecting {'{', '(', NUMBER, NEGATIVE_NUMBER, '_', ID, INFIX, POSTFIX}
    mismatched input '=' expecting {'=>', ':'}

The CLI may then crash with `java.lang.NullPointerException` thrown from `BuildVisitor.visitLetClause`. That crash is fallout of the same syntax error, not a cache problem.

Nested in a block, for example a `\case … \with { | 0 => \have | : 0 = 0 => idp \in n … }`, the report moves away from the binding to the enclosing `\with`:

    extraneous input '\with' expecting {<EOF>, '\open', '\import', '\private', …}
    Some clauses are missing
      In: \case n \with {}

**Fix:** name the binding, even if the name is unused: `\have | e : 0 = 0 => idp`.

**Why:** the `|`-clause form of `\have` requires a name before the `:`. The no-`|` form `\have x : T => v` requires one too.

### Identifier starting with a digit

```arend
\func g (n : Nat) (p : 0 = n) : Nat =>
  \have | 0=n : 0 = n => p
  \in n
```

**Error**, at the binding site. The quoted token is the identifier with its leading digit cut off:

    extraneous input '=n' expecting {'=>', ':'}

**Fix:** start the name with a letter, leading with the subject: `n=0`, `n>0`, `x0<eps`, `half>0`.

**Why:** identifiers may contain `+ - < > / = *` freely but may not *begin* with a digit, so `0=n` lexes as the numeral `0` followed by the identifier `=n`. The same bad token appears at the definition and at every use, so fix the name at the definition even if the error is reported at a use site.

### Pre-1.12 universe syntax

Arend 1.12 removed `\Type`'s second (homotopy) level argument, together with `\lp`, `\lh` and `\oo-Type`:

| Pre-1.12 | 1.12 |
|---|---|
| `\Type p h` | `\h-Type p` (`\Type 0 1` → `\1-Type 0`, `\Type 5 7` → `\7-Type 5`) |
| `\Type p 0` | `\Set p` |
| `\oo-Type p` | `\Type p` |
| `\Type \lp \lh` | declare a level parameter and use it: `\func f.{l} … => … \Type l …` |

At top level the leftover level token is blamed directly:

    \func T => \Type 0 1
    -- extraneous input '1' expecting {<EOF>, '\open', '\import', '\private', …}

Inside a block-argument meta the error moves to the `{` that opens the block, and the follow-on errors make the meta look like the culprit:

    \func T => run { \Type 0 1 }
    -- extraneous input '{' expecting {<EOF>, '\open', '\import', '\private', …}
    -- Expected 1 implicit argument
    --   In: run
    -- Cannot infer an expression
    --   In: _

Nothing in these messages mentions universes or levels. A statement-keyword expecting-set at a meta block's `{` means the definition failed to parse, so look *inside* the block for removed syntax. A sibling that differs only in the universe form parses fine.

---

## Extending this skill

When you fix an `extraneous input` error whose cause isn't listed above, add a `### <short tag>` entry under **Known triggers**. Include a minimal repro, the misleading error text, the fix, and a one-line why.
