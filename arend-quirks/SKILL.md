---
name: arend-quirks
description: Survival notes for actually formalizing things in Arend. Use when writing .ard files, reviewing Arend proofs, explaining why Arend syntax/semantics differ from Coq/Agda/Lean, or debugging an Arend typecheck failure. Written as "things that surprised me after reading the tutorial and language reference".
user-invocable: true
---

# Arend quirks — what the docs say vs. what I'd naively expect

This is a personal cheat-sheet of places where Arend deviates from the Coq/Agda/Lean-shaped picture I carry around by default. Not a reference manual — the Arend language reference is. These are the paper-cuts I want to remember before writing a proof.

Sources referenced below live in the **website** repo, `/home/sergey/Documents/site/` — not in the Arend or arend-lib tree: `src/documentation/tutorial/PartI/*.md`, `src/documentation/tutorial/PartII/*.md`, `src/documentation/language-reference/*`, and `src/documentation/standard-tactics/*.md`. (Other checkouts of the same docs exist at `/home/sergey/Documents/Site/documentation/` and `/home/sergey/Documents/arend-lang.github.io/documentation/`; the `src/documentation/…` paths quoted below match the `site/` layout.)

Library citations of the form `Module/File.ard:NNN` are relative to `/home/sergey/Documents/Arend/arend-lib/src/` and were re-verified against branch `staging` on 2026-07-28.

Companion skills:
- **arend-formalize** — procedural workflow for going from an informal math statement to a typechecking `.ard` file (which CLI tools to use, in what order).
- **arend-prove** — catalog of metas (`rewrite`, `ext`, `simplify`, `linarith`, …) for closing equality and algebra goals.

---

## 1. Equality is not an inductive family

What I'd expect: `Id A a b` / `Eq A a b` / `a = b` is an inductive with one constructor `refl`, eliminator `J`.

What Arend actually has (`language-reference/prelude.md`, `tutorial/PartI/idtype.md`):

- `Path (A : I -> \Type) (a : A left) (a' : A right)` is the primitive. Terms are functions `f : \Pi (i : I) -> A i` that **additionally** satisfy the definitional side-conditions `f left => a` and `f right => a'`. These boundary conditions are enforced by the typechecker when you write `path (\lam i => ...)` — a boundary mismatch gives a dedicated error.
- `a = b` is defined notation for `Path (\lam _ => A) a b`.
- Reflexivity is `idp := path (\lam _ => a)`. There is no `refl` constructor; `idp` is treated as a constructor for pattern matching only (it has no real body).
- `J` is not primitive; it's derived from `coe` (the interval eliminator). Practically you use `transport`, `pmap`, or pattern-match on `idp`.
- There is a definitional eta rule `path (\lam i => p @ i) == p`, but only for the built-in `@`.
- Implicit coercion between paths and `\Pi (i : I) -> A i` fires automatically (`path` / `@` inserted).

Consequence: when a goal contains `p @ left` or `p @ right`, it *reduces* to the endpoint. Use this aggressively — it's not propositional, it's definitional.

## 2. Pattern-matching on `idp` has a subtle restriction

What I'd expect: match `p : a = b` with `idp`, done.

What the docs spell out (`prelude.md`, `tutorial/PartI/equalityex.md`, `tutorial/PartI/case.md`):

- When you match `p : e = e'` with `idp`, at least **one** of `e`, `e'` must be a variable that does **not** occur in the other. "Matching on `idp`" is really matching on the `Σ`-pair `(a', p)` which has one inhabitant.
- The replaced variable's free variables must all be bound at each of its occurrences (substitutability condition).
- In `\case`, you must additionally bind the endpoint with `\elim` or put the equality arg in a position where the variable comes from the case scrutinee. A common trick is `\case expr \as x, idp : x = expr \with { ... }` to reconnect the matched value with the original expression.
- `J` via pattern matching:
  ```arend
  \func J {A : \Type} {a : A} (B : \Pi (a' : A) -> a = a' -> \Type) (b : B a idp)
          {a' : A} (p : a = a') : B a' p \elim p | idp => b
  ```

If you get "cannot match on idp here", the first thing to check is whether both sides of the equality are non-variables or share variables.

## 3. `\case` vs `\elim` vs `\with` is not just taste

What I'd expect: these are interchangeable styles.

What actually differs (`tutorial/PartI/case.md`, `tutorial/PartI/synndef.md`, `language-reference/definitions/functions.md`):

- `\func f x \elim x | ... => ... | ...` — `f n` **reduces** to the matched body. Normal forms look nice.
- `\func f x => \case x \with { | ... => ... }` — `f n` stays as a `\case`-expression in normal form. Worse UX downstream.
- Prefer top-level `\elim`/`\with` whenever possible; reach for `\case` only for scrutinizing *expressions* that aren't parameters.
- Termination checker **only tracks eliminations at the top level** (`\elim`, `\with`). A decreasing `\case` inside the body does not count — you'll get a termination error even when obvious. Factor out a helper with `\elim` in that case.
- In `\case`, use `\case \elim x \with { ... }` to re-substitute `x` in the return type per clause. Without `\elim`, `x` stays as `x` in the return type and you'll often need `\return ... \with { }` plus a `\as`-binder.
- `\case e \as b \return T[b] \with { ... }` is the standard dependent-case idiom.
- `\scase` is a strict variant (parallel to `\sfunc`).

**Reducing `\elim`-defined functions in lemmas: eliminate the dependent variable that the *constructor*'s recursive arg lives in.** When a function `f` is defined via multi-pattern `\elim k, x` over a data type with implicit indices, `f (C … rest)` (where `C` is a constructor and `rest` is its recursive sub-component) does NOT reduce in a downstream lemma unless the lemma `\elim`s **`rest`** (in addition to `k`).

Intended Arend behavior, not a bug.

```arend
\data D (n k : Nat) : \Set \elim k   -- two indices, only k matched
  | 1 => base
  | suc k' => stepD Nat (D n k')

\func f {n k : Nat} (x : D n k) : Nat \elim k, x
  | 1, base => n
  | suc k, stepD r rest => r Nat.+ f rest

-- WORKS: \elim k, rest exposes the function's clause.
\lemma f-step {n k : Nat} (r : Nat) (rest : D n k)
  : f (stepD r rest) = r Nat.+ f rest \elim k, rest
  | 1, base => idp
  | suc k, stepD r' rest => idp
```

**Subtler case — proving a property by induction on the parameter itself.** When the lemma is `f lambda = something` and you `\elim k, lambda`, the destructured `lambda` becomes `stepD r rest`, but **`f (stepD r rest)` still does NOT reduce inside this clause's body** — even though it looks like it should. The reducer needs `rest` to be the eliminated variable, not a sub-component of an eliminated variable.

```arend
-- FAILS: \elim k, lambda destructures lambda, but rest (sub-component) is
-- still a bound variable to Arend's reducer, not an eliminated one.
\lemma g=n-bad {n k : Nat} (lambda : D n k) : f lambda = n
  \elim k, lambda
  | 1, base => idp
  | suc k, stepD r rest =>
    pmap (r Nat.+) (g=n-bad rest) *> ...  -- Type mismatch: f (stepD ...) unreduced
```

The fix is to **factor the reduction step into a separate lemma** that `\elim`s the recursive arg, then chain through it:

```arend
\lemma g=n-good {n k : Nat} (lambda : D n k) : f lambda = n
  \elim k, lambda
  | 1, base => idp
  | suc k, stepD r rest =>
    f-step r rest                   -- f (stepD r rest) = r + f rest  (computation rule)
    *> pmap (r Nat.+) (g=n-good rest)  -- r + f rest = r + something
    *> ...                              -- chain to n
```

The pattern: **the reduction equation lives in a helper lemma whose proof eliminates the recursive arg as a parameter**. The induction proof then composes through this helper.

For data types whose constructors carry path-equality arguments (e.g. `compPart … (n = r1 + r2) …`), the helper's `\elim` may need to additionally destructure the path via `\case \elim path \with { idp => … }` to make the dependent indices rigid.

The same applies to `\sfunc` + `\peval`: `\peval f (C …)` fails with "Expression does not evaluate" if the call's recursive arg isn't an eliminated variable.

## 4. Records, classes, and fields

What I'd expect: records are dumb tuples, classes/typeclasses are a separate mechanism with resolution.

What Arend does (`tutorial/PartI/records.md`, `language-reference/definitions/records.md`, `classes.md`):

- `\record` and `\class` are the **same construct**; `\class` additionally enables instance inference for implicit arguments of that type.
- **Parameters are fields.** `\record Pair (A B : \Type) | fst : A | snd : B` — `A`, `B` show up as fields just like `fst`/`snd`. Anything in the parameter list is a field. You can `\extends` and implement them as you would any field.
- **Definitional eta** for records/classes: `\new R { | f => r.f | g => r.g }` is definitionally equal to `r`. Data types don't get this unless you opt in.
- **Classifying field**: the first explicit parameter of a `\class` is the classifying field (can mark others with `\classifying`, or disable with `\noclassifying`). An instance coerces automatically to this field's value. So `s : Semigroup` used where a `\Set` is expected becomes `s.E`; `m : Monoid Nat` used where a `Nat` expression is expected applies `m`'s operation only if the carrier field coerces to a function — more commonly this is what lets `Monoid Nat` match instance searches for `Nat`-carried structures.
- **Instance search**: implicit parameters typed by a class get filled by searching declared `\instance`s whose classifying field matches. No goal-directed unification cascade like Coq canonical structures — it's first-match-on-classifier.
- **A second `\instance` whose classifying expression has the *same shape* as an existing one
  breaks instance search in unrelated modules, and the diagnostic names your new instance.**
  Declaring `\instance FunctorCartesianPrecat (J : Precat) (C : CartesianPrecat) : CartesianPrecat
  (Functor J C)` alongside the library's existing `FunctorPrecat` / `FunctorCat` (both classified
  by `Functor J C`) made every later `Precat` search over a functor category ambiguous — the first
  failure surfaced in `Category/Ind.ard`, a module that mentions no functor category, as

      [ERROR] Cannot infer an instance of class 'Precat'
        Candidate is: FunctorCartesianPrecat ?J ?C
        Since types of the candidates are not less than or equal to the expected type

  Rigidity (previous bullet) is necessary, not sufficient: ask also whether the classifier is
  *already taken*. When it is, declare a **`\func … \cowith`** and pass it explicitly. Same call
  for `IndPrecat` / `ProPrecat` (`Ob = \Sigma (P : Presheaf C) (IsIndObject P)` is rigid, but the
  two would classify identically and differ only in `Hom`). Verified 2026-09-15.
- **Consequence: composition in a `\func`-defined category needs the instance *and all three
  object implicits* pinned.** `const.Func g ∘ ofLevel f` for `ProPrecat C` a `\func` does not
  merely fail to find the instance — the operands' types reduce to homs of a category that *is*
  an instance (here `PresheafCat`), so search silently picks that one and composes in the
  **opposite** order. Write `Precat.o {ProPrecat C} {A} {B} {D} g f`; with only `{ProPrecat C}`
  pinned you get `Cannot infer parameter 'X' / 'Y' / 'Z' of definition 'o'`.
- **An index-category parameter declared as bare `Precat` drags bare `Hom` to the infinite level.**
  In `\func homDiagram.{u} {C : Precat.{u,u}} {J : Precat} (c : C) (D : Functor J C) : Functor J
  SetCat.{u}`, the clause `| F j => Hom c (D j)` is rejected with `Expected type: \Set u / Actual
  type: \Set`, plus a spray of `Cannot infer parameter 'X' of definition 'o'`: bare `Hom`
  resolved its instance to `J`, not `C`. Two fixes, apply both — give every index category finite
  levels (`{J : Precat.{u,u}}`) and qualify the operations you mean (`C.Hom`, `C.∘`, `C.id-left`,
  `C.o-assoc`), which is what `HomLeft` in `Category/Yoneda.ard` already does. Verified
  2026-09-15.
- **`SubSet`'s classifying field is `contains`, so an implicit `{R : SubSet X}` is instance-searched.**
  `\class SubSet (S : BaseSet) (\classifying contains : S -> \Prop)` (arend-lib `Set/SubSet.ard`). A
  `\where` member that inherits `{R : SubSet (FreeGroup S)}` from its parent `\func` — e.g.
  `PresentedGroup.rel` — gets it by instance search on the argument's predicate, not by
  unification, and fails with `Cannot infer an instance of class 'SubSet' with classifying
  expression: StRel …` plus a bogus `Cannot infer parameter …` on the constructor passed in. Pin
  it: `PresentedGroup.rel {Gen I R} {relSet Phi R} (r1 …)`. Verified 2026-10-12. Relatedly,
  `S ⊆ T` binds its point *implicitly* (`normalClosure.superset R r`, not `… R w r`), and a
  function `h : \Pi (w) -> R w -> …` is passed as `\lam {w} => h w`: Arend does not
  eta-insert the implicit binder, so `(h _)` fails.
- **An `\instance`'s classifying expression must be *rigid*: a universe, a sigma type, a record, or a partially applied data/constructor.** A field access does not qualify, so `\instance DirectedFiltered (J : DirectedSet) : FilteredPrecat J` is rejected with `Classifying field must be either a universe, a sigma type, a record, or a partially applied data or constructor` — `J` elaborates to `J.E`. Same for `| Ob => S.Total` (a `\func` result). The message lists the admissible shapes but never says which subterm failed or what to do; the fix is to declare a **`\func … : C \cowith`** instead, which costs nothing when the value is always passed explicitly (index categories, carrier wrappers). Contrast the cases that *are* accepted: `FunctorPrecat (C D : Precat) : Precat (Functor C D)` (a record), `SetCat : Cat (\Set u)` (a universe), `ProductDirectedSet (X Y : DirectedSet) : DirectedSet (\Sigma X Y)` (a sigma — note the sigma is rigid even though its *components* are field accesses). Verified 2026-09-15 on `Category/Filtered.ard`.
- `\this` is an implicit parameter of type `R` available inside every field/function of record `R`. Usable only in argument positions.
- `\cowith` gives copattern-style definition: `\func zeros : Pair Nat Nat \cowith | fst => 0 | snd => 0`. Equivalent to `\new`, but can be the body of a `\func`.
- **Properties**: `\property p : P` requires `P` to be a proposition. Fields whose type is provably in `\Prop` are auto-promoted to properties unless marked `\field`. Properties don't compute — important for proof UX and performance.
- **Diamond handling**: `\extends A, B` where both extend `C` deduplicates `C`'s fields. But if `A` and `B` each independently define a field with the same name, you get two distinct fields and need qualified access `A.f {r}` vs `B.f {r}`. The algebraic-hierarchy advice is: avoid `\extends AbGroup, Monoid` for rings — use `\extends AbGroup { | mulMonoid : Monoid A }` to keep `*` and `+` in separate fields.
- **A class's `\func` / `\lemma` members do not resolve bare from a subclass body — only its
  *fields* do.** Inside `\class SubAddMonoid \extends SubAddPointed` (`\override S : AddMonoid`),
  `contains_+ … : contains (x + y)` resolves `+` without help, because `+` is a *field* of
  `AddMonoid` and the field is reachable through `S`. A `\func` member is not: `contains (n *n x)`
  fails with `Cannot resolve reference '*n'`, and has to be written `contains (n AddMonoid.*n x)`.
  The neighbouring library code already does this everywhere once you look — `contains_BigSum`
  writes `AddMonoid.BigSum l`, `SubMonoid.contains_pow` writes `Monoid.pow x n` — so **copy the
  qualification style of the definition next door rather than the operator style of the field
  above it**. Qualified infix parses fine (`n AddMonoid.*n x`, and `x Arith.Int.IntRing.+ y` at
  `Algebra/Group.ard:263`). Verified 2026-09-14. See **arend-prove** for the bogus
  `Termination check failed` this produces inside a recursive lemma.

  **It is not only subclass bodies: a class `\func` member does not resolve bare from *anywhere*,
  even with the instance a parameter in scope.** For `{R : PseudoCRing} (a b : R)`, the integer
  multiple `n *i (a * b)` — `*i` being `\func \infixl 7 *i` inside `\class AddGroup` — is
  rejected with a plain `Cannot resolve reference '*i'`, although `*`, `+` and `negative` in the
  same expression resolve fine, because those are *fields*. Write `n R.*i (a * b)` (instance
  qualification, the Phase-4 style) or `n AddGroup.*i (a * b)`; both typecheck. Verified
  2026-09-18.

- **A numeral on one side of a comparison pins the instance before the variable does.** For
  `d : Int`, the natural-looking `0 <= d` is rejected with
  `Cannot solve equation: 1st expression: Nat, 2nd expression: E` — the literal `0` resolves at
  `Nat` and `<=` is then searched for a `Nat`-carried `Preorder`, with `d`'s type never getting a
  say. Pin the operator, not the numeral: `0 IntRing.<= d` (the idiom at `Arith/Rat.ard:327`,
  `Arith/Int.ard:279,283`). Verified 2026-09-14 on `Algebra/Ring/GradedCoeffs.ard`.

- **A numeric literal needs a *declared* instance, so `1` fails over a `\func`-computed group.** Instance search matches the classifying field against `\instance` declarations only. `NormalSubGroup.Quot` and `PresentedGroup S R` (`Algebra/Group/Presentation.ard`) are `\func`s returning a `Group`, so `quotHom x = 1` is rejected with `Cannot infer an instance of class 'Pointed' with classifying expression: Quotient {E {S}} (~)` — write `ide {Quot}` / `ide {PresentedGroup S R}`. The same statement with the group a *variable* (`\Pi (w : …) -> R w -> f w = 1` for `{G : Group}`, `f : GroupHom _ G`) needs no annotation, because the parameter pins the instance. Verified 2026-09-14.
  **The same holds for `*`, `inverse` and `ide` on elements of such a group, even when the
  element is a variable.** With `g : St C (LocRing (powers t))` (`St` a `\func` returning a
  presented group), `g * x * inverse g` fails with `Cannot infer an instance of class
  'Semigroup' with classifying expression: Quotient {Quotient {List (\Sigma (Gen …) Bool)} (~)} (~)`:
  the type of `g` is normalized to the presented group's carrier before instance search, so the
  `St C …` that would pin the instance is gone. Pin the group — `(*) {St C R} g x`,
  `ide {St C R}`, `conjugate {St C R} g x` — exactly where the operands are elements of the
  computed group; inside `GroupHom` application positions and in `StData` (group a variable)
  nothing is needed. Verified 2026-10-15 on the thesis repo's `src/Steinberg/Patching.ard`.

- **Arithmetic on a *concrete* record instance computes, and that breaks term-level tooling.** `ComplexField.*` is implemented by a formula on `re`/`im`, so `x * y` normalizes to `\new Complex (x.re * y.re - x.im * y.im) (…)`. Note the body has no pattern matching, so this reduction is **unconditional** — it fires for two *variable* operands too, not only when one is concrete. Verified 2026-08-11: `rewrite cabs_* idp` fails on `cabs (h * h * q) = cabs h * cabs h * cabs q` for `h q : Complex` parameters, because after normalization the goal contains no `*`-application for the pattern to match. The pretty-printer re-folds the record literal, so the error displays an expression that visibly contains the pattern it reports as missing — see **arend-prove** failure mode 18. Consequences (all verified 2026-07-29, on what is now `Arith/Complex/FTA/Kneser.ard`): `equation.cRing` cannot prove even `x * y = y * x` at `Complex`; `rewrite` cannot match a pattern containing a meta under a `*`/`+`; and unification cannot infer an implicit that occurs only under one. **Keep such algebra symbolic: state the step over an abstract `{C : CRing}` (or make the operands explicit parameters of a helper) and instantiate.** Abstract class parameters are what keep a term neutral — this is a general reason a helper lemma over `{M : AbMonoid}` succeeds where the same proof inlined at the concrete instance fails. See **arend-prove** failure modes 15–17 for the diagnostics.

- **In `SetCat` the composition `∘` *reduces*, so the `pmap (∘ _)` / `inv o-assoc` proof style
  breaks.** `SetCat`'s `o g f => \lam x => g (f x)` has no pattern matching, so a composite of two
  *variable* morphisms normalizes to a lambda and `id-left`, `id-right`, `o-assoc` are all literally
  `idp`. Consequences, all hit on 2026-09-17 while proving that limits of presheaves are pointwise:
  `pmap (∘ _)` cannot solve its `_` (the goal contains no `∘`-application to match), supplying the
  argument by hand does not help because the *other* side has eta-expanded to `\lam x => …`, and
  `inv o-assoc` reports `Cannot infer parameter 'g'` since its implicits are only recoverable from a
  neutral composite. The diagnostic prints the goal in pointwise form (`trans {L.coneMap j} Y (… x)
  = coneMap j ∘ ?_x`), which reads as a unification bug rather than a reduction problem.
  **Fix: state the lemma over an abstract target category** (`{D : Cat}` instead of `SetCat.{u}`) and
  instantiate. Same medicine as §4's "keep such algebra symbolic", same cause — a concrete instance
  whose operation is implemented by a formula is never neutral. Here it also *weakened* the
  hypothesis, since nothing about sets was used.

- **`\have x : T => \new R { | Parent => v | … }` leaves `x`'s non-parameter fields opaque, even
  when `T` pins the classifying field.** With `\have M : Limit (Comp G F) (G L.apex) => \new Limit {
  | Cone => Cone.map G L | isLimit => p }`, the ascription makes `M.apex` reduce (it is a parameter
  pinned by `T`), but `M.coneMap j` does **not** reduce to `G.Func (L.coneMap j)` — `coneMap` is an
  ordinary field, and the goal comes back mentioning an irreducible `M.coneMap j`. Dropping the
  ascription is not enough either; what is needed is that the receiver be a *reducing* term.
  **Fix: put the packaging in a `\func`** — `\func fromIsLimit (c : Cone G) (cl : IsLimitCone c) :
  Limit G c.apex \cowith | Cone => c | isLimit => cl` — and write `fromIsLimit c cl` at each use
  site. A `\func` application unfolds, so `(fromIsLimit c cl).coneMap j` reduces to `c.coneMap j`.
  Inlining the `\new` at every use site works too, and is what arend-lib does
  (`\new Limit { | Cone => c | isLimit => cl }` appears verbatim in `Category/Limit/Finite.ard` and
  `Set/SetCategory.ard`). Refines §7: the opacity is not only about unification of the bound
  *value*, it also blocks field projection through an implemented parent.

- **A field named like a constructor shadows it for the whole module.** A record field `| pos : R.I -> Nat`
  is exported to module scope, so a top-level `\elim x | pos 0 => … | Int.neg 1 => …` in the same file fails
  with `Cannot find a reference to constructor among provided patterns / In: pos 0`, which reads as a
  pattern-syntax error. Rename the field (`ord`). Same hazard for imported fields: import a module that
  declares a field `root` selectively (`\import M (Rec)`) when the importing file has its own `root`.
  Verified 2026-10-13 on `src/RootSystem/FrenkelKac.ard` in the thesis repo.
- **Explicit implicits on a record's own field or method start with `{this}`.** Inside the record (or on
  a method called bare), `reduced {al} {ga} {0} p` hands `al` to the hidden `{this}` and reports
  `Type mismatch / Expected type: <TheRecord> / Actual type: E {I}`. Write `reduced {_} {al} {ga} {0} p`.
  Verified 2026-10-13.

## 5. Universes, levels, and `\Prop`

What I'd expect: `Type i` with `i : Level`, cumulative or not depending on system.

What Arend has (`language-reference/expressions/universes.md`, `language-reference/definitions/level.md`, `tutorial/PartII/hom-levels.md`):

- **`\Type` has a single (predicative) level.** `\Type n` for a natural `n`; bare `\Type` is the *infinite* predicative level. Cumulative: `A : \Type n` ⟹ `A : \Type (suc n)`. There is **no second (homotopy) level argument** — `\Type \lp \lh` / `\Type p h` no longer exist (and `\lp`, `\lh`, `\oo`, `\oo-Type` are gone).
- **Homotopy levels are a separate family of universe keywords**, each carrying its own predicative level: `\Prop` (h-level -1, **impredicative** — no predicative level), `\Set n` = `\0-Type n` (h-level 0), `\n-Type m` (h-level n), and `\Type m` (untruncated). Homotopy cumulativity: `A : \Prop` ⟹ `A : \Set n` ⟹ … ⟹ `A : \Type n`. Placement: `\Prop : \Set 0`; `\k-Type p : \(k+1)-Type (p+1)`; `\Type p : \Type (p+1)`.
- **A truncated universe needs a *finite* predicative level.** Bare `\Set` / `\n-Type` errors with "Infinite level is not allowed here"; write `\Set 0` or use a level parameter. Only `\Type` may be bare. Consequently `\func x : \Type => \Type` is rejected (the infinite `\Type` isn't a member of itself — this is what blocks Girard-style paradoxes).
- **Level polymorphism is explicit and predicative-only.** No implicit `\lp`/`\lh`: a definition is polymorphic only if it declares named level parameters *after its name*: `\func id.{l} (A : \Type l) (a : A) => a`. Several params are comma-separated and independent: `\func f.{l1, l2} …`. A definition mentioning only bare `\Type` is **not** polymorphic (fixed at the infinite level). Homotopy level is not an abstractable axis.
- **A record declared without level parameters cannot be a `\Pi` binder inside a definition
  body, though it is fine as a parameter.** `\func T.{u} : \Prop => \Pi {I : DecSet.{u}}
  {Phi : DoublyLacedRootSystem I} … -> …` is rejected with `Infinite level is not allowed here /
  In: DoublyLacedRootSystem { | I => I }`, and `DoublyLacedRootSystem.{u} I` with `Too many level
  arguments`: the thesis's root-system records declare no levels, so they are fixed at the
  infinite level, and the codomain being `\Prop` does not help. The same types are accepted as
  parameters (`\func stDiagram.{u} {I : DecSet.{u}} {Phi : DoublyLacedRootSystem I} …`). Make
  them parameters of the statement and quantify only over level-polymorphic classes
  (`IntegralDomain.{u}`) inside the `\Pi`. Verified 2026-10-15.
- **Level arguments are passed with the same `.{…}` syntax**: `id.{2}`, `f.{\suc l}`, `f.{l1, l2}`. Usually inferred, so rarely written. The old `\levels p h` and positional-level forms are gone.
- **Level expressions**: atoms are non-negative numerals and named level parameters; operations `\suc l` and `\max l1 l2`.
- **Level of a data type** is the max over its **constructor-argument** type levels (a parameter not used by any constructor does not contribute). **Level of a record/class** is over its **unimplemented** fields. A definition that declares a level parameter `l` keeps that level: `\class C.{l} (A : \Type l) | …` gives `C.{l} X : \Type l`, even for a low-level `X` (e.g. `C.{5} Nat : \Type5`, not `\Type0`).
- Pi's homotopy level is the codomain's, not max; its predicative level is the max of domain and codomain.

## 6. `\use \level` — retroactively lowering the universe

This one has no Coq/Agda analogue I know of (`language-reference/definitions/level.md`, `data.md`, `functions.md`):

- If you prove a type has a lower homotopy level than was inferred, write a `\use \level <proof>` in its `\where` block. The type then *typechecks* as living in that lower universe (e.g., `Dec P : \Prop` even though it's declared with `| yes P | no (P -> Empty)` which is `\Set0` by default).
- The proof must target `ofHLevel (D p_1 ... p_k) n` for a constant `n`.
- For `\data`, this marks it **squashed**: pattern matching is only allowed when the result type lives in a universe ≤ the data's (or inside `\sfunc`, `\lemma`, `\use \level`, `\scase`).
- `\truncated \data ... : \Prop | ...` is the syntactic sugar for squashing into `\Prop`.
- Also: `\level T p` as a result-type annotation (`\lemma lem : \level A p => {?}`) convinces the checker `T` has the required level for the lemma/property/clause-omission.

## 7. `\func` / `\sfunc` / `\lemma` — evaluation semantics, not just typing

(`language-reference/definitions/functions.md`, `level.md`)

- `\func` — normal, reduces.
- `\sfunc` — never reduces; to force, use `\eval` at the call site. For performance on huge proofs whose computational content you don't want the typechecker to unfold.
- `\lemma` — result must be (provably) in `\Prop`; doesn't reduce; semantically a proof. Use for anything proof-ish where you don't want unfolding to bloat types.
- `\type` — a type alias that doesn't unfold (record-like transparency control).

Default to `\func`; switch to `\lemma` for proofs you'll cite many times and `\sfunc` when you hit typechecking slowness.

**`\have | x : T => v` can make `x` opaque to unification.** Inside a proof body, `\have` (or `\let`) with an explicit type annotation introduces `x` with type `T` whose value is `v`, but later goals that depend on `x` may *not* unfold to `v` — Arend can give errors like `Cannot solve equation: 1st expression: v, 2nd expression: x`. Two workarounds:

- Drop the type annotation: `\have | x => v`.
- Inline `v` directly at every use site (verbose but reliable).

The behavior is most painful when `v` is a long expression (e.g. `eps * RatField.finv (Ba + Bb + 1)`) that you want to abbreviate — but the abbreviation costs unification.

**It also applies to *unannotated* `\let`, and then it blocks implicit-argument inference.** A bound value is not unfolded when a lemma's implicit has to be read off it:

```arend
\let | w => ComplexField.negative (Complex.fromReal t * (b0 * conj bk))
     | cabs-w : cabs w = 1 => cabs_negative *> cabs_* *> …
```

fails with `Cannot infer parameter 'z' of definition 'cabs_negative'` — `cabs_negative {z} : cabs (negative z) = cabs z` cannot match `cabs w`. With a bound `pinv` the same opacity surfaces as a *type mismatch* between `zro < iS` and `zro < inv {pos#0 …}`, which reads like an instance-resolution problem instead.

The rule that follows: **never bind a value that a downstream lemma has to pattern-match against.** Three ways out, best first:

1. **Introduce it through an existential.** Have a helper lemma return `∃ (u : C) (P u) (Q u)` and destructure with `\case … \with { | inP (u, pu, qu) => … }`. `u` is then a genuine variable and every implicit downstream of it resolves.
2. **Make it an explicit parameter of a helper lemma** — `dir-cabs (b0 bk : Complex) (t : Real) (t>=0 : 0 <= t) : …`. Inside the helper everything is a variable; at the call site you pass the expression once.
3. **Write the expression out at each use site.** Always works, reads badly.

The same fix applies to `\Sigma`-returning helpers: building a tuple whose components each need an implicit inferred from a `cabs`/`pow` application tends to fail where two separate lemmas with explicit implicits succeed.

**Level metavariables defeat the comparison fast path, so transparent `\func`s unfold — the usual
cause of a multi-second definition with a tiny body.** A call to a level-polymorphic definition
without `.{…}` instantiates its levels with metavariables, solved only at the end of the
*enclosing* definition. Checking an argument of type `P.{u} a b` against a parameter of type
`P.{?u} a b` then cannot succeed argument by argument, and when `P` is a `\func` Arend unfolds both
sides and compares normal forms, although the two terms are otherwise syntactically identical.
Measured 2026-10-12 in the thesis repo (`Algebra/Ring/ProRingPresentation.ard`), passing
`hb : IsBalanced S (grpObj-ofDiagram GD) g` to a lemma taking exactly that type: 7.6s as written;
0.2s as `lemma.{u} …`; 1.3s with `IsBalanced` a `\type`; 0.2s with `IsBalanced` a `\type` *and*
`grpObj-ofDiagram` an `\sfunc`. The remedies, which took that library from 3m28s to 1m29s:
- Prop-valued notations (`IsBalanced`, `IsAdditive`): `\type`. Projections (`hb.4`), tuple
  construction and `transport` motives keep working. A `\type` is coerced only at the top of an
  expected type: `TruncP (\Sigma …)` against `TruncP (LevelSol …)` is a mismatch, so keep it
  out of positions under `TruncP` or a `\Pi`.
- Constructed structures (wrappers around `mapGroupObject …`): `\sfunc`, with the carrier pinned
  in the result type (`: GroupObject {D} (ofDiagram Gd)`) so that `.E` still computes. The few
  proofs that need the body bridge with `rewrite (\peval f x) proof`, or `{\eval f x}` in an
  implicit slot.
- Where unfolding is unavoidable, pin `.{o,u}` at the hot call sites (a 6.8s lemma became 3.0s).
- A `\func` of propositional type whose value nobody unfolds becomes a `\lemma` (Arend's
  `Function can be declared as a lemma` warning flags these).

Find hot spots with `arend --no-daemon -r --show-times [MODULE[:DEF]]` (see **arend-formalize**).

**A `\let` abbreviation compared against the expression it abbreviates used to cost minutes.**
In `\let | Lth => ofLevel … th | conjf => (conjAct …).f \in … *> pcomp-assoc … Lth conjf *> cp`,
where the hypothesis `cp` and the lemma statements spell those terms out in full, the comparison at
each `*>` step failed syntactically on `Lth` vs `ofLevel … th`, normalized both sides to WHNF
(unfolding every transparent `\func`) and compared records field by field (`compareClassInstances`,
dozens deep). Measured 2026-10-16 on the thesis repo's `strict-deep`: 3m5s as written, 3.2s with the
`\let`s substituted by hand. The local Arend build (`~/Documents/Arend`, `CompareVisitor.compare`,
uncommitted) now compares a `\let`-bound variable through its value before normalizing anything,
which gives 3.6s on the unchanged proof. On a CLI without that fix: do not `\let`-abbreviate a term
that hypotheses or cited lemmas state in full. `--show-unfolds` blamed the free group there (`++`
unfolded 2M times) — a symptom, found out with `--show-hot-spots` and `-Darend.unfold.trace`.

The same all-or-nothing comparison bit in two more spellings, and the local build takes the one
reduction for those as well: an **alias `\func`** against the head of its body (`StPro C S` vs
`grpObj-ofDiagram (stGD C S)` as the argument of a lemma stated with the latter: 21s → 48ms), and a
**field of a variable whose type implements it** (`io {d}` for `d : TData {… io => io {this} …}` vs
`io {this}`, inside a `\record`'s members: 18s → 4s). Without those changes, state such lemmas in
the spelling their callers use.

## 8. Pattern-matching data types with varying constructors

Not something Coq can express directly (`tutorial/PartI/datanproofs.md`, `language-reference/definitions/data.md`):

```arend
\data Vec (A : \Type) (n : Nat) \elim n
  | 0 => nil
  | suc n => cons A (Vec A n)
```

Constructor lists can **depend on how parameters pattern-match**. One clause can introduce multiple constructors. This also drives HITs: `| path-cons I-var => boundary-expr` clauses impose definitional equalities on a data type.

Strict positivity is enforced: the type cannot occur in a function-domain position nor inside `Path` endpoints.

`\cons f => body` defines a pattern-synonym-ish alias.

## 9. `Nat` / `Fin` / `Array` / `I` are subtly primitive

(`language-reference/prelude.md`)

- `Nat.+` and `Nat.-` reduce on **either side** (`n + 0 => n`, `0 + m => m`, `suc n + m => suc (n + m)`, `n + suc m => suc (n + m)`). You can't write these clauses in user code — pattern matching picks one direction. Prelude cheats.
- `Fin n` is a **subtype** of `Nat` (and of `Fin (suc n)`). `zero : Fin (suc n)`, `suc x : Fin (suc n)` when `x : Fin n`. No separate constructor names.
- `Array A` is a **record** with `len : Nat`, `A : \Type`, `at : Fin len -> A`; it also has `nil` and `::` constructors. You can pattern-match like a list *and* index like a function, simultaneously. `Array A n` is equivalent to a length-`n` vector. `DArray` generalizes to dependent fibres.
- `I` has constructors `left`, `right` and a hidden "connecting" constructor. **Pattern-matching on `I` is forbidden**. Use `coe`, `coe2`, `squeeze`, `squeezeR` instead. `coe (\lam x => A) a i => a` when `x` doesn't occur free in `A` (key reduction rule).
- `iso` implies univalence and is not definable in user syntax.
- `Path.inProp` postulates proof irrelevance and has no body.

## 10. Coercions

(`language-reference/definitions/coercion.md`, `records.md`)

- `\use \coerce toT (x : S) : T | ...` in a `\where` defines a coercion `S → T` (last param is source). For target-direction, the result type defines the target.
- `\coerce` annotation on a record field or data constructor promotes it to a coercion.
- A class's classifying field gives an automatic coercion to that field's type.
- Coercion into a function type partially applies.
- Because coercions fire silently, if typechecking reports a surprising type, check for an inserted coercion before blaming unification.
- **Never put `\coerce` on the payload field of a *wrapper* record that carries its own algebraic
  structure.** The coercion fires **in preference to instance search on the wrapper**, so the
  wrapper's operations become unreachable in infix notation. With
  `\record Homotope {R : CRing} (s : R) (\coerce val : R)` and `\instance HomotopeRing (s : R) :
  PseudoCRing (Homotope s)` implementing `* a b => \new Homotope s (a.val * s * b.val)`, the
  expression `a * b` for `a b : Homotope s` silently means the product **in `R`** — the tag `s`
  drops out, which is the one thing the wrapper existed to prevent. You cannot even state the
  intended law: `(a + b).val = a.val + b.val` is rejected with

      Type mismatch
        Expected type: a class
          Actual type: R.E
        In: a + b

  because `a` and `b` were coerced out of the record before `+` was resolved, so `.val` is being
  applied to an `R`-element. Verified 2026-09-14 on `Algebra/Ring/Homotope.ard`; dropping
  `\coerce` fixed both, and `.val` is short enough that nothing was lost. Note the asymmetry:
  operations that exist *only* on the wrapper are unaffected — `(r *c a).val` typechecks fine,
  because no coercion path makes `r *c a` an `R`-element. So the symptom appears exactly on the
  operations the wrapper *shares* with its payload type (`+`, `*`, `zro`), which are the ones
  you care about. Keep `\coerce` for genuine one-way embeddings (§10's `Real -> Complex`), not
  for a field you will also do arithmetic over.
- **Hoist explicit embeddings to `\use \coerce` when you'd otherwise repeat them.** If a `.ard` file inserts `fromReal x` / `wrap x` / `inj x` at every call site, define `\use \coerce fromReal (x : Real) : Complex => …` once inside the target record's `\where`, and the elaborator silently inserts it everywhere. The 2026-05-15 refactor moved the `Real → Complex` embedding to a `\use \coerce` inside `Complex \where`; downstream `I * fromReal x` instances throughout `Arith/Trig/Real.ard`, `Arith/Trig/Complex.ard`, `Arith/Complex/Euler.ard`, and `Arith/Complex/Norm.ard` collapsed to `i * x`. The coercion is at `Arith/Complex.ard:23`; the accompanying `\open Complex \using (iunit \as i)` appears at the top of each of those files.

## 11. Implicit arguments, `\meta`, and the tactic story

(`language-reference/definitions/metas.md`, `functions.md`, `standard-tactics/*`)

- Implicits: `{A : \Type}`. In call sites, curly-brace application; in patterns, either give `| {A}, x => ...` or omit implicit patterns.
- `_` in an argument = infer; `_` as a parameter name = "don't care" (repeatable).
- Inference *across constructor-injectivity* works: `{n m : Nat} (p : suc n = m)` → both can be inferred. `{n : Nat} (p : n + n = 3)` → cannot, since `+` is not a constructor.
- Goals: `{?}` is a hole.
- **An implicit that vanishes when the definition reduces can never be inferred — declare it explicit.**
  A `\func`-defined proposition is unfolded before its arguments are solved, so a parameter that the
  body's own reduction *erases* is unrecoverable from the expected type. `\func SurjMod {A : CRing}
  (B : SubRing A) (h : A) (k : Nat) : \Prop => \Pi (a : A) -> ∃ (a' b : A) (B b) (a = pow h k * a' + b)`
  looks like it determines `h` — but at `k = 0`, `pow h 0` reduces to `ide` and `h` is gone, so
  `\lemma surjMod_zro {h : A} : SurjMod B h 0` fails at every call site with `Cannot infer parameter
  'h' of definition 'surjMod_zro'`. `B` stays inferable, `h` does not. Write `(h : A)`. The tell is
  that the failing parameter is one the *reduced* goal never mentions — check by hand which arguments
  survive the definition's `\elim` before choosing the implicit/explicit split. Verified 2026-09-14 on
  `Algebra/Ring/Excision.ard`.

- **A lemma whose implicits come *before* its explicit arguments cannot be passed point-free.**
  `nonZero-left {x y : E} (x/=0 : x /= zro) (x*y=0 : x * y = zro) : y = zro` (`Algebra/Domain.ard:48`) looks like it
  should fill a `\Pi {x : E} -> r * x = zro -> x = zro` slot once its first argument is given, but `nonZero-left r/=0`
  solves `{y}` as a *metavariable* rather than leaving it to be bound later:

      Expected type: r /= zro -> \Pi {x : E} -> r * x = zro -> x = zro
        Actual type: r /= zro -> r * ?y = zro -> ?y = zro

  Write the binder out — `\lam r/=0 p => nonZero-left r/=0 p`. Arend inserts the implicit `\lam {x}` for you *there*,
  because the expected type is known at the lambda; it will not eta-expand a term that has already been applied.
  Verified 2026-09-14 on `IntegralDomain.regulars-char`. Same symptom class as the `Fin`/`Nat`-coercion eta-lambda note
  in **arend-prove**'s compaction list, different cause: not every `\lam x => f x` is removable.
- **An implicit that occurs only as `?J.op` (or under any other `\func`) is unsolvable, and the
  diagnostic blames instance search.** A signature like `\func prodDiagram {C : PrecatWithBprod}
  {J : Precat} (X Y : Functor J.op C)` determines `J` only by inverting `Precat.op`, which Arend
  will not do. At a call site where nothing else mentions `J`, the report is not "cannot infer J"
  but

      [ERROR] Cannot infer an instance of class 'Precat'
        Candidate is: PrecategoryOfElements.{?p1, ?p2, ?p3} {{?error}} ?P

  followed by half a screen of that candidate's field implementations. Pin the argument
  (`prodDiagram {C} {FilteredProduct A.2 B.2} X Y`). Rule of thumb: **whenever a parameter's type
  mentions the implicit only under a `\func` application, the implicit is not inferable** — either
  pin it at every call site or make it explicit. Verified 2026-09-17 across `Category/Pro/Limit.ard`.
- **Unification against a `\func`-defined construction picks a wrong solution instead of failing.**
  `proPair u v`, `ofDiagram X`, `toLevel X j`, `mapOfDiagram a` all unfold (to Yoneda transforms,
  Σ-tuples, quotient maps), so matching `proPair ?u ?v` or `mapOfDiagram {?X} {?Y} a` against a goal
  is higher-order; Arend commits to the first solution it can build, which is often the source
  where the target belongs (`?Y := X` for `mapOfDiagram`), and the mismatch then surfaces one chain
  step later with two printed types differing in a single subterm. Three habits that follow, all
  paid for in debugging rounds on 2026-09-17:
  * state such a lemma with the components **explicit** — `proPair.o (a b : …) (u v : …)`, not
    implicit, when the conclusion mentions `proPair u v`;
  * pin the *target* of a map-like construction (`mapOfDiagram {C} {J} {X} {V} a`, and give
    `toLevelOf.map` its target diagram as an explicit parameter);
  * pin a test object that is a compound term: `proPair {C} {ofDiagram X} u v`, because solving
    `?W.1.F ≡ indFunctor …` is a projection applied to a metavariable and is not solvable at all
    (the error is then `Cannot solve equation: NatTrans … (F {?W.1})` plus `Cannot infer parameter
    'W'`).
- **No tactic language in the core.** "Tactics" are `\meta`s — macros that expand into Arend expressions, type-checked post-expansion. Defined either in Arend (`\meta f x => e`, pure substitution) or in Java (the interesting ones, shipping as the standard library's `Meta` modules).

For the catalog of metas (`rewrite`, `ext`, `simplify`, `equation`, `cong`, `linarith`, `cases`, `mcases`, `unfold`, `assumption`, `in`, `at`, `run`, `$`, `#`, `repeat`, `using`, `defaultImpl`, …), their semantics, common failure modes, and a decision table, see the **arend-prove** skill.

## 12. Syntax quirks I keep forgetting

- All keywords start with `\`: `\func`, `\data`, `\class`, `\record`, `\let`, `\with`, `\elim`, `\case`, `\lam`, `\Pi`, `\Sigma`, `\new`, `\this`, `\where`, `\open`, `\import`, `\hiding`, `\using`, `\instance`, `\cowith`, `\scase`, `\sfunc`, `\lemma`, `\property`, `\field`, `\truncated`, `\coerce`, `\level`, `\eval`, `\extends`.
- Infix: `\infix`, `\infixl`, `\infixr` + priority 1–9. Backticks convert *between* fixities on an ordinary function: ``x `op` y`` makes a prefix function infix, and ``x `op y z`` makes it postfix (`` 3 Test.`f 1 2 `` ≡ `f 3 1 2`). Both work on qualified names — `` suc 4 Nat.`div` suc 1 `` typechecks.
- **A leading bare infix operator is a right *section*, not a prefix application — so `+ 3 4` is an error.** This is the rule that most often breaks code written from Haskell/Coq habits, and it is silent at parse time. Verified 2026-09-10 against branch `staging` (`src/test/java/org/arend/typechecking/InfixPostfixTest.java`):

  | Form | Meaning |
  |---|---|
  | `3 + 4` | ordinary infix application |
  | `(+) 3 4` | **prefix application — parenthesize the operator** |
  | `(+ e)` | right section `\lam x => x + e`; `(+ (suc 1)) 5` is `7` |
  | `+ 3 4` | **error** — parsed as a section, so the second argument is applied to a `Nat` |

  Everything after a leading operator is its *right operand*, so `(+ suc 1) 5` is `\lam x => x + suc 1` applied to `5`. Passing an implicit does not opt out: `+ {r} 0 1` errors while `(+ {r} f 3) 4` is a section and typechecks. Ordinary (non-`\infix`) functions are unaffected — `(f 5) 2` is fine — and field operators section identically: `r.+ 1` ≡ `\lam x => x r.+ 1`.

  **A *qualified* field operator behaves the same, and the message names the operands.**
  `Monoid.* {homGroup {C} (X j) G} f g` — an attempt to multiply with the instance pinned, since
  `homGroup` is a `\func` and instance search will not find it — parses as the section
  `\lam x => x Monoid.* …` and reports `Expression is applied to an argument, but does not have a
  function type / Argument: g / In: f`. Write `(*) {homGroup {C} (X j) G} f g`. Verified 2026-09-17.

  Practical consequence: **an infix operator passed as an argument always needs its parens.** `pmap2 (+) p q`, `\new AddGroup G.E G.ide (G.*) …`, `Big (∨) (l 0) (tail l)`. Dropping them is the compaction regression catalogued in **arend-error-type-mismatch** (*Stripped parentheses around an infix operator*); depending on whether operands surround the operator you get either that entry's bogus `Type mismatch` / `Expected type: I`, or — when the operator leads — `Expression is applied to an argument, but does not have a function type`.
- **A backticked reference with no operands is rejected outright.** `` \func test => Nat.`div` `` gives `Infix notation is not allowed here`, and `` Nat.`div `` gives `Postfix notation is not allowed here` (`base/src/main/java/org/arend/naming/resolving/visitor/ExpressionResolveNameVisitor.java:294` for plain references, `:336` for field calls). `` Test.`pair`.1 `` fails earlier still, at parse. Backticks are fixity *annotations on an application*, not a way to name an operator — to denote the operator itself, parenthesize: `(Nat.div)`.
- **A `\Pi` / `\Sigma` / `\lam` on the right of an infix operator needs parentheses**, and the
  parse error names the keyword rather than the operator: `A <-> \Pi (k : Nat) -> P k` is rejected
  with `no viable alternative at input '\Pi'`. Write `A <-> (\Pi (k : Nat) -> P k)`. Verified
  2026-09-14; same shape for `->`-chained statements handed to `&&`, `||`, `<->`.
- Comments: `-- line`, `{- nestable block -}`.
- `()` pattern — absurd case, RHS omitted. Often nested: `| fsuc (fsuc (fsuc ()))`.
- `\as x` binds an as-pattern; in `\case`, `\as x \return T[x]` is the dependent idiom.
- Dot notation: `x.f` needs `x`'s type to be a literal record/class name — but `x` does **not** have to be a
  *variable*. A parameterless `\func` whose result type is a class works too: with `\func regulars : SubMonoid \this`
  a member of `\class CRing`, both `regulars.contains_pow p` and the verbose `SubMonoid.contains_pow {regulars} p`
  typecheck, and `Domain.nonZeroMonoid` reaches into its sibling the same way (`subMonoid.Total`,
  `Algebra/Domain.ard:58,64`). It **chains**, too: from outside the class, with `A : CRing` a parameter,
  `A.regulars.contains_pow hr` typechecks — no need for `SubMonoid.contains_pow {A.regulars} hr`
  (verified 2026-09-14). And a `\func` member of a *record* is reachable on a genuinely applied
  expression: `(excisionHom B h).Kernel x` needs no pinning, because the receiver's type is a record
  name, not a class awaiting instance search. Verified 2026-09-14; an earlier revision of this line said "only if `x` is a
  variable", which pushes you to the verbose form for no reason. For a genuinely *applied* expression
  (`closure S`, `normalClosure R`) the pinned `Record.f {e}` form is still required — see **arend-prove** failure
  mode 21 for the diagnostic it gives when you forget.
  The one case that genuinely needs a type ascription is a binder whose type comes from a
  **class field** rather than from the expression: implementing `QEquiv`'s `ret` as
  `| ret a => a.val` fails, because `ret`'s domain is the field `B`, not a record name — even
  though `B` is already solved and the error prints the solved value, so it reads as
  self-contradictory:

      Type mismatch
        Expected type: a class
          Actual type: Homotope {R} s
        In: a

  Annotate the binder — `| ret (a : Homotope s) => a.val` — and it goes away. Verified
  2026-09-14 on `Homotope.embed-equiv`. Binders whose type comes from an *instance's* carrier are
  fine as-is: `| * a b => \new Homotope s (a.val * s * b.val)` in the same file needs no ascription.
- `__` (double underscore) — implicit lambda slot, enables sections like `__ + 1`.
- `\open M`, `\open M (f, g)`, `\open M \hiding (f)`, `\open M (f \as f')`, `\open M \using (f \as f')`. `\import` bundles visibility. **`\open M \using (Long \as short)` is the idiom for aliasing a hot identifier file-locally** — e.g. `\open Complex \using (iunit \as i)` at the top of `Arith/Trig/Real.ard:34` (and `Arith/Complex.ard:19`, `Arith/Trig/ArcTan.ard:49`, `Arith/Trig/Complex.ard:19`, `Arith/Complex/Euler.ard:14`, `Arith/Complex/Norm.ard:38`) lets the body write `i * x` everywhere instead of `Complex.iunit * fromReal x`. Reach for it whenever a long-named constant is used more than ~3 times.
- `\let` bindings are non-recursive and sequential (each sees the previous).
- `\where` is a module; `f.g` accesses it from outside. **But `\private \lemma helper` inside a `\where` block makes `helper` invisible outside**, and because Arend's name resolution then falls back to treating `f.helper` as field access on `f`-the-value, the error is misleading: `Type mismatch: Expected type: a class. Actual type: <f's body type>`. If you want sibling lemmas to share helpers, either drop `\private` (so the helper is reachable as `parent.helper`) or hoist to file-level `\private \lemma` at module scope — arend-lib usually does the latter.

- **`BigProd`/`BigSum` over a concrete array literal normalise away.** With `Shape.all = s11 :: … :: nil`,
  `G.BigProd (map f Shape.all)` reduces to the explicit seven-fold product, so `BigProd-ext` /
  `func-BigProd` cannot read their implicit arrays off the goal (`Cannot infer parameter 'l' of definition
  'BigProd-ext'`), and pinning them gives baffling family mismatches. State the lemma over a *variable*
  array (`(l : Array A) … : G.BigProd (map g l) = G.BigProd (map g' l)`, proved by `pmap … (ext p : g = g')`)
  and instantiate it at the literal. Verified 2026-10-13 on `src/Steinberg/Group.ard`.

## 13. Termination checker surprises

(`language-reference/term-checker.md`)

- Lex order on declared parameters; size-change for mutual recursion.
- **Only top-level `\elim` / `\with` eliminations count.** A decreasing `\case` in the body is invisible to the checker.
- If the checker rejects a legitimately decreasing call, factor the recursion out to a helper with `\elim`.

## 14. The "reasoning-about-types" payoff

Things that are axioms or advanced features in other systems but fall out naturally here:

- **Function extensionality** is provable (use paths through the interval).
- **Propositional univalence** (`A ↔ B ⟹ A = B` for `A B : \Prop`) is provable; **full univalence** comes from `iso`.
- **`\new R {...} ≡ r`** eta gives "record refactoring" for free definitionally.
- `path (\lam i => p @ i) ≡ p` eta for `@` is definitional.

For deciding which meta closes an equality goal, see the **arend-prove** skill.

## 15. ExUpperReal idiosyncrasies (and why generic Monoid/Semiring lemmas don't always apply)

`ExUpperReal` represents "real numbers possibly equal to +∞". Its arithmetic is fragile in three ways that catch out generic algebraic reasoning:

- **`ExUpperReal` is NOT a `PosetSemiring`**, despite having `+`, `*`, and `<=`. arend-lib instantiates `ExUpperRealAbMonoid : BiorderedLatticeAbMonoid` (for `+` with order) and `ExUpperRealSemigroup : CSemigroup` (for `*`) as *separate* class instances. There's no unified `PosetSemiring ExUpperReal`. **Consequence**: `PosetSemiring.pow_<=-degree`, `PosetSemiring.pow<=1`, and similar lemmas that need both `+` and `*` aligned don't apply. (Those live on `\class PosetSemiring` — `Algebra/Ordered.ard:236`, with `pow_<=-degree` at line 285 — and `ExUpperReal` is not an instance of it.) If you need such a lemma over ExUpperReal, prove the analog manually; as of 2026-07-28 the library has no ExUpperReal-specific `pow_<=-degree`, so there's nothing to copy.

- **`ExUpperRealSemigroup.ide-left`/`ide-right` are CONDITIONAL on `x >= 0`**. Unlike `Monoid.ide-right : x * ide = x` (unconditional), the ExUpperReal versions carry a non-negativity hypothesis:

  ```arend
  -- Arith/Real/UpperReal.ard:336, :341
  \protected \lemma ide-left  {x : ExUpperReal} (x>=0 : 0 <= x) : fromRat 1 * x = x
  \protected \lemma ide-right {x : ExUpperReal} (x>=0 : 0 <= x) : x * fromRat 1 = x
  ```

  Always supply the proof when calling them. `ExUpperRealSemigroup.pow_>=0` (`Arith/Real/UpperReal.ard:518`) is the usual source — see `Arith/Log.ard:77` and `Arith/Trig/ArcTan.ard:96` for the idiom `ExUpperRealSemigroup.ide-left ExUpperRealSemigroup.pow_>=0`.

- **`ExUpperRealSemigroup.pow` is a custom `\protected \func`, NOT `Monoid.pow`** (`Arith/Real/UpperReal.ard:506`). They're different functions of the same shape but with different definitional behaviour. So `Monoid.pow_+`, `Monoid.pow_ide`, `pow_*-comm`, etc. don't apply to `ExUpperRealSemigroup.pow`. The custom pow's definition `pow x (suc n) = pow x n * x` does reduce, so basic induction works fine. It ships with `rat-pow`, `pow_<=`, and `pow_>=0` (`Arith/Real/UpperReal.ard:510–518`); anything beyond those (`pow_+`, `pow_ide`) you prove yourself.

## 16. `RealNormed.norm` returns ExUpperReal but is defined as `abs : Real → Real`

`Topology/NormedAbGroup/Real.ard` defines `RealNormedAbGroup.norm := abs`, where `abs : Real → Real` is implicitly coerced (somehow — there's no explicit `Real → ExUpperReal` `\use \coerce`; the class field's type `ExUpperReal` is reached by a `join (Real.fromRat r) (negative (Real.fromRat r))` form). The practical consequence: when proving `RealValuedRing.norm (Real.fromRat r) <= ExUpperReal.fromRat c`, the goal unfolds to `join (fromRat r) (negative (fromRat r)) <= ExUpperReal.fromRat c` — comparing a Real value against an ExUpperReal value.

**The bridge** to use:
1. `LatticeAbGroup.abs-ofPos : 0 <= x -> abs x = x` — collapse the `join`/`negative` form to `x` when `x >= 0`.
2. `RealAbGroup.abs-rat : abs (Real.fromRat r) = Real.fromRat (RatField.abs r)` — push abs into Rat.
3. `Real.<=-upper : x <= y (in Real) <-> x <= y (in ExUpperReal)` — bridge the two `<=`.
4. `rat_real_<= : a <= b (in Rat) <-> Real.fromRat a <= Real.fromRat b (in Real)` — bridge to Rat.

(Locations: `abs-ofPos` on `LatticeAbGroup`, `abs-rat` at `Arith/Real.ard:302`, `Real.<=-upper` and `rat_real_<=` in `Arith/Real.ard`.)

Composing these turns any `RealValuedRing.norm (fromRat r) <= ExUpperReal.fromRat c` goal into a pure Rat inequality `RatField.abs r <= c`.

Worked instances in the current tree: `Arith/Log/Properties.ard:91` (`A.norm_fromRat <=∘ =_<= (pmap ExUpperReal.fromRat (RatField.abs-ofPos …))`) and `Topology/StoneCStarAlgebra.ard:251`. When the target is already an `ExUpperReal` bound, the shorter `norm_fromRat <=∘ ExUpperReal.<=-rat.1 …` form often replaces the full four-step chain — see `Arith/Trig/ArcTan.ard:95`.

## 17. `makeRat` doesn't reduce on `suc <var>` — case-split to expose

`ratio nom (suc m)` calls `makeRat nom (suc m) ...`, which eliminates its `denom` into two clauses (`Arith/Rat.ard:64`):

```arend
\func makeRat (nom : Int) (denom : Nat) (denom/=0 : denom /= 0) : Rat \elim denom
  | 1 => nom                                  -- literal return, no reduction
  | denom => makeRat' nom denom denom/=0      -- catch-all; computes via `reduce`
```

If `m` is a variable, `suc m` matches neither clause definitionally — the elaborator can't tell whether `suc m = 1`, so it can't commit to clause 1 or fall through to the catch-all. As a result, `ratNom (ratio 1 (suc m))` does NOT reduce to `pos 1`, even though it equals `pos 1` propositionally. `simplify` and `linarith` can't see through.

**Fixes, cheapest first:**

1. **`makeRat.simp`** (`Arith/Rat.ard:77`) — `makeRat nom denom denom/=0 = makeRat' nom denom denom/=0`, already proved for every `denom`. Rewriting with it discharges the split for you.
2. **`mcases {makeRat}`** — mirrors `makeRat`'s own clause structure; see `Arith/Rat.ard:99` (`signum_nom`) for a live use.
3. **`\elim m` / `\case \elim m`** — the manual version. In each branch `makeRat` reduces (clause 1 in the `m = 0` case, the catch-all otherwise), `ratNom`/`ratDenom` become concrete, and the residual goal is usually linarith-soluble.

## 18. `\private` inside `\where` hides the def from sibling lemmas — and the error message is misleading

`\where` IS a module, and `parent.helper` IS valid syntax for accessing nested definitions from outside the parent. What goes wrong is the combination `\private \lemma helper` *inside* a `\where`: `helper` becomes invisible outside the parent, AND because name resolution falls back to treating `parent.helper` as field access on `parent`-the-value, the error has nothing to do with privacy:

```
[ERROR] Type mismatch:
  Expected type: a class
  Actual type: <parent's equation type>
  In: parent
```

If two sibling lemmas need to share helpers nested in a `\where`, either:

- **(a) Drop `\private`** so the helpers are publicly accessible as `parent.helper`. Fine when the helpers genuinely belong to the parent's namespace.
- **(b) Hoist to file-level `\private \lemma`** at module scope. This is the more common arend-lib idiom.

(Cross-references from a sibling inside the same `\where` to another sibling at the *same* depth work fine without qualification — it's only the *outside-the-where* access that needs the public visibility or the hoist.)

## 19. Block comments `{- ... -}` nest — LaTeX in doc comments can swallow the whole file

Arend's block comment `{- ... -}` is **nestable**, so the parser counts opening and closing braces. Any `{-` inside a block comment opens a *new* nested comment that needs its own `-}`. In LaTeX-heavy doc comments this fires accidentally:

```arend
{- | Cauchy–Schwarz: $(\Re x \cdot \Re y)^2 \leq |x|^2 \cdot |y|^2$, where $x^{-1}$ denotes the inverse. -}
\lemma CS_<= ...
```

The `{-1}` inside `x^{-1}` opens a nested comment. The closing `-}` of the doc block then matches the inner nesting, leaving the *outer* block unclosed — so the entire rest of the file becomes one giant comment. Symptoms:

- Definitions below the comment "disappear" (typechecker reports them as unresolved from elsewhere in the project, or simply not present).
- The file "passes" with zero diagnostics on the definitions in it, because none of them were parsed.
- Wildly distant errors like "no such module" or "definition X not found" appear in *other* files that depended on the swallowed ones.
- **Within one file, the report is `Cannot resolve reference 'X'` at the *consumer*** — a line 20 lines below a definition of `X` that is plainly visible in the source. Nothing points at the comment.
- The swallowed range ends at the *next* `-}` in the file, not at EOF, so which definitions vanish looks arbitrary: three consecutive ones can disappear while a fourth further down survives.
- A forced recompile (`--no-daemon -r`) changes nothing, and neither does restarting the daemon — it is not a cache problem. Don't spend a rebuild on that guess.
- **Fastest confirmation: `arend -ss <name>` returns `No matches` for a definition that is on screen.** If the symbol index cannot see it, the parser never saw it either. (Contrast with the genuine index lag for brand-new *modules*, noted in **arend-prove**.)

A real instance: `{- | The Kneser factor $q = 1 - 3^{-2n^2 - n}$ … -}` — the `{-` in `^{-2` swallowed `kneser-q`, its two bound lemmas, and two more helpers.

**Remedy:** after editing any doc comment, run `grep -rn` for the three forms and inspect every hit inside a doc comment:

```bash
grep -rn '{-' arend-lib/src/
grep -rn -- '-}' arend-lib/src/
grep -rn '{-}' arend-lib/src/    # rarer: empty nested comment from `{-}` in math
```

Any occurrence of `{-`, `-}`, or `{-}` *inside* a doc comment (i.e. not the comment's own opening/closing delimiters) needs a space inserted to break the token: `{ -`, `- }`, `{ - }`. So `x^{-1}` becomes `x^{ -1}`, and `\{-1, 0, 1\}` becomes `\{ -1, 0, 1 \}`. Do this defensively after every doc-comment edit — the failure mode is silent and the diagnostic surfaces far from the cause.

(Line comments `-- | ...` do not nest and are immune. Prefer `-- |` for one-liners that don't contain LaTeX braces; reserve `{- | ... -}` for multi-line docs and accept the audit cost.)

**The same opener bites in code: `{-1}` as an implicit argument starts a comment.** `f {-2}` looks like
`f` applied to the implicit `-2`, but `{-` is lexed as a block-comment opener. The two front ends then
disagree, and the CLI is the misleading one:

- **CLI (ANTLR, `buildSrc/.../Arend.g4`):** `COMMENT : '{-' (COMMENT|.)*? '-}'` is a single token, and it
  only matches if some `-}` follows. With none later in the file, the lexer falls back to `{`,
  `NEGATIVE_NUMBER`, `}` and the code typechecks. Add any `{- … -}` comment further down and the CLI also
  swallows everything from `{-2}` to it. Verified 2026-10-13: the error was `Cannot infer parameter 'k'`.
- **IntelliJ plugin (JFlex, `intellij/.../ArendLexer.flex`):** `"{-"` enters `BLOCK_COMMENT_INNER` at once,
  with no lookahead, so the rest of the file is an unterminated comment.

Write `{ -2}`, with a space. A file that passes the CLI can still be broken in the plugin, so grep for
`{-[0-9]` before committing.

## 20. Extending records and closing inherited fields (`\extends` / `| F => v`)

> **Provenance.** The running example below (`RatAnalytic`, `BoundedDiskRatAnalytic`, `disk-open-aux`, `eval-IsSeriesSum`, `disk-incl`, `radius-loc`) came from `Analysis/RatAnalytic.ard`, which commit `8363cdac2` "Refactor RatAnalytic" **deleted** — the development was dissolved into plain functions in `Analysis/PowerSeries.ard` and `Analysis/PowerSeries/Derivative.ard`, with no `\record` surviving. Don't go looking for those names; they aren't in the tree. The *library types* the section cites are all still live: `CoverMap`, `SetHom` (with `\coerce func`, `Set/SetHom.ard:4`), `StronglyCauchyMap`, `PrecoverSpace.open-char`, `OpenCompleteCoverSpace`, `RegularPreuniformSpace`, `func-cover` / `func-weak-cauchy` / `func-cauchy`. The lessons are general `\extends` behaviour and still apply.

When making your record a descendant of another (e.g. `\record RatAnalytic ... \extends CoverMap`) and supplying defaults for the parent's fields, several non-obvious things hold:

- **A record body with no braces cannot hold methods at all, and the diagnostic blames `\this`.**
  `\record R (I : \Set)` followed by a `|`-field list and then a `\lemma` puts that `\lemma` at
  *top level*, not in the record: the brace-less form accepts fields only. Every field reference
  in the stray definition then needs an instance that nothing supplies, and the report is a spray
  of `Cannot infer parameter 'this' of definition '<field>'` — pointing at the fields, never at
  the missing brace — plus, for a `\lemma`, a bogus `The type of a lemma must be a proposition /
  Actual level: \Type0`. Wrap the whole body: `\record R (I : \Set) { | f : … \lemma m => … }`.
  Verified 2026-09-18 on `src/RootSystem/Basic.ard` in the thesis repo. (Arend's own
  `\class AddGroup \extends AddMonoid { … }` is the shape to copy.)

- **Field order is strict.** All `|`-fields (including assignments like `| InheritedField => value`) must come *before* any `\func` / `\lemma` methods in the record body. Mixing them yields confusing "field implementation cycle" or "cannot resolve reference" errors that never mention ordering. If you see `Cannot resolve reference 'foo'` for a method `foo` defined *below* in the same record, ordering is the first thing to check.

  The rule also governs *insertions* into an existing class, and there the diagnostic points nowhere near the edit:
  dropping a `\func` in above `\class Semiring`'s `| natCoef : Nat -> E` (`Algebra/Semiring.ard:38`) reports
  `Cannot resolve reference 'natCoef'` at `natCoef`'s *users* further down the class, followed by a spray of
  `Cannot infer parameter` errors in every importing module — which reads like a broken instance hierarchy. Verified
  2026-09-14. **When an insertion breaks names you never touched, check that you landed below the `|`-block**, and
  re-check the neighbouring modules only after that.

- **`| InheritedField => value` closes the parent's field.** This is the canonical pattern when extending: the child supplies a default value for what the parent left abstract.

  - `\override Field : NewType` is distinct — it changes the field's *type* (must be a subtype), not its value. Use it (e.g. `\override Dom : RegularPreuniformSpace`) when narrowing the inherited type; use `| Field => v` to supply a default.

- **Field-default expressions can't forward-reference methods of the same record.** A `| Dom => OpenCompleteCoverSpace disk-open` where `disk-open` is a `\lemma` defined later in the body fails with `Cannot resolve reference 'disk-open'`. Even reordering the lemma above the default may not help — the elaborator processes field defaults before method bodies are typechecked.

  **Workaround**: extract the helper to a top-level `\func` parameterized by what would have been the implicit `\this`-fields:
  ```arend
  \lemma disk-open-aux {A : RealBanachAlgebra} {r : ExUpperReal} : A.isOpen ... => ...

  \record RatAnalytic (A : RealBanachAlgebra) \extends CoverMap {
    | radius : ExUpperReal
    | Dom => OpenCompleteCoverSpace (disk-open-aux {A} {radius})
    ...
    \lemma disk-open : A.isOpen ... => disk-open-aux {A} {radius}   -- thin wrapper
  }
  ```

- **Implicit arguments are *not* inferred from field-default context.** Even though `A` and `radius` are record fields in scope at the default site, writing `| Dom => OpenCompleteCoverSpace disk-open-aux` fails with `Cannot infer parameter 'A'`. Must be explicit: `disk-open-aux {A} {radius}`. The default-site is not an ordinary call-site for purposes of metavariable resolution.

- **Don't redeclare the parent's class parameters in a descendant.** `\record Child (A : T) \extends Parent` where `Parent` already has `(A : T)` produces `Field 'A' is already defined in super class at Parent.A`. Just `\record Child \extends Parent { ... }` — `A` is inherited.

- **`\coerce` on a field propagates through `\extends`.** `\record SetHom (Dom Cod : BaseSet) | \coerce func : Dom -> Cod` makes any descendant of SetHom (transitively: ContMap, PrecoverMap, CoverMap) implicitly callable as a function. So `\record RatAnalytic \extends CoverMap` lets `(myAnalytic : RatAnalytic) s` desugar to `myAnalytic.func s` for free. Useful for "this record *is* a function with extra structure" — but it also means once you `\extends`, any field of the inherited `func` name is the coercion target. Existing `\func func` methods in the same record clash; rename them (e.g. `eval`).

- **"Field implementation cycle" can be a false positive from inherited default chains.** CoverMap has `func-weak-cauchy F => ...func-cover F...`, StronglyCauchyMap has `func-cauchy F => ...func-weak-cauchy F...`. Setting `func-cover` in a descendant from an externally-constructed CoverMap triggers `Field implementation cycle: func-cover - func-cauchy - func-weak-cauchy` even though the dependency is acyclic — the chain is `func-cauchy ← func-weak-cauchy ← func-cover`, all forward.

  **Workaround**: either extract the construction to top-level so it doesn't go through the descendant's `\this`, or close *all* the related defaults at once (`| func-cover => ...`, `| func-weak-cauchy => ...`, `| func-cauchy => ...`). The error message doesn't say which approach is needed; pick the smaller diff.

- **Vacuous-hypothesis discharges via empty-pattern `\case`.** For an inherited field whose hypothesis is provably empty in a specific instance (e.g. `radius.IsBounded` when `radius = top` — `top.U q` is `∃ over Fin 0`, empty), supply the field body with a pattern-match that ends in an empty case:
  ```arend
  | radius-loc => \lam rb _ _ => \case rb \with {
      | inP (B, top-U-B) => \case top-U-B \with { | inP (j, _) => absurd j }
    }
  ```
  The outer `inP (B, top-U-B)` destructures the truncation; the inner `\case top-U-B \with { | inP (j, _) => absurd j }` destructures the empty `∃` and absurd-eliminates `j : Fin 0`.

- **Total-Set domain replaces per-point-with-proof signatures.** When a record extends `CoverMap` with `Dom = Total S` for `S : Set X` a predicate, the inherited `func : Dom → Cod` is total on `Total S = \Sigma (x : X) (S x)`. Per-point access becomes `func (x, h)` (with the coercion: `myInstance (x, h)`). If you previously had a per-point `\func func {x} (h : S x) : Y`, rename it — both can't be `func`.

- **Methods invoked inside a class body need an explicit instance qualifier when the receiver is the same parent class.** Calling `PrecoverSpace.open-char.2` (a method of `PrecoverSpace`) inside a `BoundedDiskRatAnalytic` body whose `Dom` is a `PrecoverSpace` doesn't pick up `Dom` as the implicit receiver — instead the lambda parameter `s` in the callback ends up typed `E {?this}` where `?this` is unresolvable. The fix is to qualify with the actual instance value:
  ```arend
  -- doesn't work (lambda's s gets generic E {?this}):
  PrecoverSpace.open-char.2 \lam {s} Ufs => ... s.2 ...

  -- works (lambda's s now resolves to Total ...):
  (OpenCompleteCoverSpace (disk-open-aux {A} {radius})).open-char.2 \lam {s} Ufs => ... s.2 ...
  ```
  Same trick on the inner `open-char.1` if used inside the same proof. Without the qualifier, `s.1` / `s.2` projections fail with "Expected: sigma, Actual: E" — there's no hint that the fix is at the surrounding call.

- **`|`-style field defaults cannot reference class `\lemma` / `\func` methods, by any syntax.** Inside a `\record`'s `| Field => body`:
  - Bare names of class methods (`eval-IsSeriesSum`, `disk-incl`, …) **don't resolve** ("Cannot resolve reference"), even when those methods are defined earlier in the same record. By contrast, `\lemma` / `\func` bodies *can* reference other class methods by bare name.
  - `\this.method` and `ClassName.method {\this}` **resolve** but both trigger an immediate `Dependency cycle` through the class itself — arend's dependency tracker treats them as the field default depending on the class via `\this`.

  The workaround is to **inline the method body** in the field default. The only references that work cleanly from `|`-defaults are:
  - bare field names (`coef-Rat`, `ps-conv`, …) — fields are visible by bare name from defaults.
  - top-level helpers (e.g. `disk-incl-aux {A} {radius}` instead of `\this.disk-incl`).

  Concretely, the func-cont proof in `BoundedDiskRatAnalytic` needed:
  ```arend
  -- doesn't work — bare resolution fails for `eval-IsSeriesSum`:
  ... A.limit-unique limit-isLimit (eval-IsSeriesSum s.2) ...

  -- doesn't work either — \this triggers cycle through the class:
  ... A.limit-unique limit-isLimit (\this.eval-IsSeriesSum s.2) ...

  -- works — inline eval-IsSeriesSum's body, using only fields and externals:
  ... A.limit-unique limit-isLimit (seriesConv-sum (absConv-isConv (...ps-conv norm>=0 s.2...))) ...
  ```
  Same goes for `disk-incl` (replace with the top-level `disk-incl-aux {A} {radius}`).

- **A coclause that binds a field's implicits must bind *all* of them, including the ones its body
  never mentions.** Implementing `Functor`'s `Func-o {X Y Z : C} {g : Hom Y Z} {f : Hom X Y}` as
  `| Func-o {D} {D'} {D''} => exts \lam c => … D'' …` is rejected with a bare

      [ERROR] Type mismatch
        In: exts

  even though only `D''` occurs in the body; so is `| Func-o {_} {_} {D''} => …`. Writing all five,
  `| Func-o {D} {D'} {D''} {b} {a} => …`, fixes it — the two trailing binders stay unused. The
  diagnostic names `exts` and nothing else, so it reads as a failure of the proof rather than of
  the binder list. Same family as the "expected type is not ground" errors in **arend-formalize**:
  with the tail left unbound those implicits are still metavariables when `exts` elaborates.
  Verified 2026-09-15 on `Category/Ind.ard`'s `limFunctor` (`Func-id {D}`, with one implicit,
  needs no such padding — the rule bites only when you bind a *prefix* of several).

These pitfalls compound: a single naïve `| InheritedField => method-defined-later` line can trigger any of forward-reference-failure, implicit-arg-failure, *and* implementation-cycle errors, none of which name the underlying ordering/scoping issue. When debugging a record refactor, audit field-default expressions for: (a) only-fields-and-top-level-functions referenced, (b) all implicit args spelled out, (c) `|`-block ends before the first `\func`/`\lemma`, (d) sibling-class method calls (like `open-char`) are qualified with the receiver instance.

## 21. Quick decision table when stuck

| Symptom | First thing to try |
|---|---|
| Goal has `f x` where `f` was defined with `\case` | Rewrite `f` to use `\elim` |
| Termination error on obvious recursion | Move `\case` up to `\elim` in the signature |
| "Cannot match on `idp`" | Ensure one side of the equality is a variable bound in the match context and doesn't appear in the other side |
| Implicit arg not inferred from `p : f n = m` | `f` is not a constructor — provide it explicitly or restructure |
| Proof unfolds into a mess | Switch `\func` → `\lemma` |
| Typechecker is slow on a big proof | Switch `\func` → `\sfunc`, use `\eval` at call sites only as needed |
| Need the connection between a case scrutinee and its matched value | `\case e \as x, idp : e = x \with { ... }` (or see arend-prove for `cases`/`mcases`) |
| Data type inferred in too-high universe | `\use \level` with a level-proof in `\where` |
| Need to squash into `\Prop` | `\truncated \data ... : \Prop` |
| Want definitional equality for a derived def | `\type` instead of `\func` (or leave it as `\func`, which reduces) |
| Equality / algebra / arithmetic goal | See the **arend-prove** skill |

## 22. Subtyping between records is by *named* ancestors, not by field sets

Learned while splitting `Ideal` into rng-level and unital halves (`Algebra/Ring/Ideal.ard`,
2026-09-14). Three rules, in the order they bite:

- **A record is a subtype only of the classes it names in `\extends` (transitively).** Having
  every field of `C` is not enough. `\record TIdeal \extends LIdeal, RIdeal` — where `LIdeal
  \extends PseudoLIdeal` and `RIdeal \extends PseudoRIdeal` — has literally all of
  `PseudoTIdeal`'s fields and is still *not* a `PseudoTIdeal`, so it cannot be passed to
  anything expecting one. Name the ancestor: `\extends PseudoTIdeal, LIdeal, RIdeal`.

- **Naming it then fails if two superclasses `\override` a shared field to different types** —
  even when the types are comparable (`Ring <: PseudoRing`). Arend does not intersect them:

  ```
  [ERROR] The types of the field 'S' differ in super classes 'PseudoTIdeal' and 'LIdeal'
    In: TIdeal
  ```

  **The fix is to re-`\override` the field in the descendant**, which is checked *after* the
  superclass list and settles the conflict: `\record TIdeal \extends PseudoTIdeal, LIdeal,
  RIdeal { \override S : Ring }`. Same for `Ideal \extends PseudoIdeal, TIdeal { \override S :
  CRing }`.

- **Conflicting *default implementations* inherited from two parents are tolerated** (no error,
  no warning) — `PseudoLIdeal` deriving `contains_* _ c => ideal-left c` and `PseudoRIdeal`
  deriving it from `ideal-right` coexist in `PseudoTIdeal`. Only *types* of fields must agree.

A field implementation written after the `\extends` list without braces is rejected with
`Field 'f' does not belong to class 'C'` — implementations go inside `{ … }` (see §20 on field
order); `\record C \extends A, B | f => v` is parsed as a *declaration* site.

**Corollary: `\open M (names)` does not re-export — at file level either.** Opening inside a
definition's `\where` makes the names visible in that definition's own body, but `Parent.name`
still does not resolve from outside. The same holds for a *file-level* `\open`: `Algebra/Ring/Factor.ard`
opens `FactorPseudoRing (Type, inF, fequiv, fequiv0, unfequiv, unfequiv0)` at the top, and importers
still have to write `FactorPseudoRing.fequiv0` or repeat the `\open` themselves — which is what every
consumer in the tree does (`Algebra/Ring/Integral.ard:167`, `Algebra/Ring/Nakayama.ard:39`,
`Algebra/Ring/Excision.ard`). Verified 2026-09-14. So when a helper moves out of `M`'s `\where`, an `\open`
in the old place will not keep the old path alive — update the call sites. The error at those
call sites names the *parent's* parameters (`Parameter 'I' must be specified explicitly. In:
FactorRing`), never the missing member, because resolution falls back to field access on the
value; same read-as-nonsense shape as §18.

## Quirks met in the conjugation-action work (2026-10-16)

- **`^{-1}` inside a doc comment opens a nested comment.** `{- | … k^{-1} … -}` and `S^{-1}R` both
  contain `{-`, so the parser reports `Unclosed comment` at the *start* of the block. Write
  `k^{\,-1}` or `R_S`.
- **A record field of an imported record shadows a same-named lemma from another import.**
  `\import Steinberg.Patching` brings `LocalConj`'s field `rep-exists` into scope, and a lemma
  `rep-exists.{u}` imported from another module then resolves to the field. The symptoms are
  `Too many level arguments` and a type mismatch on the first argument. Rename the lemma.
- **`(X).*i` does not parse** for a non-variable instance `X`, and `AddGroup.*i {X} n a` in prefix
  position is read as a section. The forms that work are `(AddGroup.*i) {X} n a`, `n P.*i a` for a
  *bound variable* `P`, or infix `n AddGroup.*i a` when the instance is inferable from `a`.
- **`\cowith` is not allowed in a `\let`**; use `\new R { | f => … }`.
- **`\have` makes a term abbreviation opaque**, so `St.x g1 a1` with `a1` bound by `\have` does not
  match `deep J1 g1 ide`. Bind data with `\let` and keep `\have` for proofs.
