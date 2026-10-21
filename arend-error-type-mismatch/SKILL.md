---
name: arend-error-type-mismatch
description: Diagnose misleading Arend `Type mismatch: Expected X, Actual Y` errors where the printed types look wrong, unrelated, or contain metavariables. Use whenever an .ard typecheck error of this shape doesn't make sense — the literal types are downstream effects of an upstream name-resolution, implicit-inference or parsing failure. Catalogue of known causes with minimal repros and fixes, plus an index of misleading mismatches documented in the other Arend skills.
user-invocable: true
---

# Arend typechecker error — `Type mismatch: Expected X, Actual Y`

`Type mismatch` prints the types the elaborator computed *after* elaboration. When `Expected` / `Actual` don't make sense for the code you wrote — unrelated types, metavariables on one side, a value where an equation belongs — the real failure happened earlier:

- a name resolved to the **wrong** definition (Arend rarely says "unresolved" when another definition of that name is visible);
- an implicit argument (often a class instance) **failed to infer** and was solved to something else;
- the parser read the expression differently than you did (a stripped parenthesis);
- a coercion was inserted, or `\peval` reduced, differently than you assumed because of one of the above.

Workflow:

1. Look at `Expected`. If it mentions `I` (the interval), `Path`, `?a = ?a'`, or any shape your code didn't ask for, the elaborator inserted or inferred something — find what.
2. Look at `Actual`. If it is the type of the thing you intended, in the wrong slot, suspect resolution or inference before your mathematics.
3. Check that every name points where you think: qualify it.
4. Check that every implicit (especially instance) argument can be inferred at the call site: pass it explicitly to test.
5. Match against the catalogue and the index below.

---

## Known causes

### Mis-resolved `\protected` member of a `\where`

A `\protected` definition inside `Foo \where` is not in scope unqualified outside `Foo`. If another definition with the same short name *is* in scope, the unqualified use silently resolves to that one, and the error is about its type:

```arend
\func foo {n : Nat} : n = n => idp
\func Bar : Nat => 0 \where {
  \protected \func foo (x : Nat) : Nat => x
}
\func use : Nat => foo 3          -- meant Bar.foo
```

    [ERROR] Type mismatch
      Expected type: I
        Actual type: Nat
      In: 3

`Expected type: I` appears because the definition that won takes only implicits and returns a path: applying a path to an argument means applying it to an interval point.

**Fix:** qualify — `Bar.foo 3`.

**Diagnostic:** an `Expected` containing `I` or a path shape where you wrote no path-valued expression means mis-resolution. Qualify every cited lemma as the first debugging step, before chasing the types.

### `\peval f …` with an uninferrable implicit

`\peval f a` (for an `\sfunc f`) builds the equation `f a = <body>`, and it needs `f`'s implicits like any other call. With an instance that the arguments don't determine (a numeral argument, say) and no expected type to pin it, it fails outright:

```arend
\sfunc twice {A : AddMonoid} (x : A) : A => x + x
\func pe => \peval twice 1
```

    [ERROR] Cannot infer an instance of class 'AddMonoid'
      In: twice

`\peval` also extends as far right as it can: `\peval twice 1 *> q` is rejected with `Expected a function (defined as \sfunc) applied to arguments` / `In: twice 1 *> q`. Parenthesize: `(\peval twice 1) *> q`.

**Diagnostic:** `Cannot infer an instance` on a `\peval` call → pass the instance explicitly (`\peval twice {NatSemiring} 1`) or give the call an expected type.

### Stripped parentheses around an infix operator

Removing parentheses that look like noise changes the parse, silently at parse time. Two shapes.

**1. An operator passed as an argument.** `pmap2 (+) p q` → `pmap2 + p q` is no longer an application of `pmap2` but the infix expression `pmap2 + (p q)`. What you get depends on what is now on the right of the operator:

```arend
\func pm (p : 1 = 2) (q : 3 = 4) : 1 + 3 = 2 + 4 => pmap2 + p q          -- was pmap2 (+) p q
```

    [ERROR] Type mismatch
      Expected type: I
        Actual type: 3 = 4
      In: q

(`p q` applies the path `p` to `q`, so `q` lands in an interval slot.) If the new right operand starts with a non-function — `h + x y` for `h (+) x y` with `x : Nat` — the report is `Expression is applied to an argument, but does not have a function type` / `Argument: y` / `In: x`. If the operator lands between a partial application and the rest — `g 1 + 2` for `g 1 (+) 2` — instance search for `+` is run on the partial application: `Cannot solve equation` / `1st expression: (Nat -> Nat -> Nat) -> Nat -> Nat` / `2nd expression: E` / `In: (+)`. In a structure literal (`\new C X op proof …` with `op` unparenthesized), every following argument shifts one slot left: the report names the class being built, prints a partially implemented class as the actual type, and has `Expected type: I` where a proof landed in a path's interval argument. The leading-operator case (`+ 3 4`) is a right section — see **arend-quirks**, *Syntax*.

**2. Precedence.** `a * (b * c)` → `a * b * c` re-associates (same priority, `\infixl`), and `a * (b + c)` → `a * b + c` changes the tree (`+` binds weaker). The statement usually still typechecks; the failure shows up in the body or at the first consumer, with two sides equal up to bracketing:

    [ERROR] Type mismatch
      Expected type: a * b * c = 0
        Actual type: a * (b * c) = 0

(or `Cannot solve equation` with the same two shapes).

**Fix:** restore the parentheses. `git diff` is faster than reading the errors: scan for hunks whose only change is removed `(` / `)` around an operator.

**Blast radius:** a stripped parenthesis inside a coercion or a class definition breaks everything downstream, including modules you never touched — a hundred errors across a dozen files. Sort the errors by module and fix the topmost one in dependency order; never start at the module you were asked about.

**Diagnostic:** an `Expected type: I`, a `\new` / class body printed as `Actual`, or two sides differing only in bracketing — check `git diff` for removed brackets before believing the types. Errors in files an uncommitted refactor never touched point the same way.

---

## Other misleading mismatches

Documented with their fixes in the other skills:

| Message shape | Cause | Where |
|---|---|---|
| `Expected type: a class` / `Actual type: <a non-class type>` | dot access on a non-record, a `\private` `\where` member, a `\coerce` payload, `Nat.<=` | **arend-quirks**, *"Expected type: a class" — causes* |
| `Cannot solve equation` pairing `\Set0` with `E` (or `TruncP` with `contains`), then e.g. `in~ {w} w` vs `in~ {\Sigma …} (\Sigma …)` | a class member's receiver is a computed value that nothing solves | **arend-quirks**, *Instance search* |
| `Cannot solve equation` / mismatch with sides differing only in bracketing | stripped parentheses | *Stripped parentheses around an infix operator* above |

---

## Extending

When you root-cause a new misleading `Type mismatch`, add an entry under *Known causes*: a minimal repro, the misleading `Expected` / `Actual`, the fix, the why, and a one-line **Diagnostic** describing the message shape that should trigger this entry next time.
