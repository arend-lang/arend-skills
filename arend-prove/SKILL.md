---
name: arend-prove
description: Procedural workflow for filling in `{?}` placeholders in an Arend file once the statement already typechecks, PLUS the catalog of metas (`rewrite`, `run`, `in`, `at`, `cases`, `mcases`, `simplify`, `equation`, `cong`, `ext`, `linarith`, `unfold`, `assumption`, `using`, `later`, `repeat`) with their failure modes. Use whenever an .ard file is at the "only GOAL errors remain" stage, or whenever it imports from `Paths.Meta` / `Meta` / `Algebra.Meta` / `Function.Meta` / `Logic.Meta`. Complement to **arend-formalize** (which gets you to "only GOAL" and owns the CLI tooling and lemma lookup). Covers the proof loop, decomposition, imports, meta semantics, a decision table, an error-to-first-move table, and proof style.
user-invocable: true
---

# Proving in Arend — proof loop and meta catalog

Picks up from **arend-formalize** ("statement typechecks, only `{?}` remain"). Language semantics that proofs trip over (records, instances, implicits, opacity) are in **arend-quirks**.

Typecheck in rounds against a daemon and look lemmas up before writing them: see **arend-formalize**, *0. Tooling: daemon, caches, where to run* and *1. Orient: look things up before writing*.

A meta is surface syntax that elaborates to ordinary terms (`transport`, `pmap`, …). Its failures look like ordinary type errors; the cause is usually a missing import, a `\lemma` whose type is not a proposition, or asking the meta for more than it does.

---

## The inner loop

For each `{?}`:

1. **Read the whole `[GOAL]` block** — the expected type *and* `Context:`, which is what tells you what is in scope inside `\have` / `\case` chains. Narrow the *scope*, not the output: `arend <Module>` lists every goal and error of a module, `arend <Module>:<def>` checks one definition. Do not `grep GOAL`: it cuts off the `Expected type:` / `Context:` lines.
2. **Prove or decompose** (below).
3. **Re-run, read the first error** or the remaining goal, iterate.
4. **Before stating a helper lemma, run `-ps "<its shape>"`.** A hit saves the lemma; `No matches` confirms you need it.
5. **When it typechecks, re-read it against the goal you meant.** Typechecking proves consistency, not faithfulness.

### Decompose

Don't write a 200-line proof as one expression. For any goal that takes more than one mathematical step:

- name each step as its own helper lemma with a clean type;
- replace the original `{?}` with the combination of the helpers;
- leave a hard helper as `{?}` — the structure now typechecks, the difficulty is isolated, and the rest of the file can use the helper as a black box (and the work can be split across sessions).

Heuristic: if you can't write the proof in one breath, name the next sub-statement as a helper and continue.

### Missing helpers

If a 1–5 line helper that should exist is missing, add it to the right module instead of working around it — the workaround is typically ten times longer and you will want the helper again. A missing library statement is not an issue to report.

---

## Imports

| Need | Import |
|---|---|
| `idp`, `pmap`, `pmap2`, `transport`, `transportInv`, `inv`, `*>`, `==<` / `>==` / `qed` | `Paths` (`=`, `Path`, `coe` are Prelude) |
| `rewrite`, `rewriteI`, `ext`, `exts`, `simp_coe` | `Paths.Meta` |
| `run`, `in`, `at`, `cases`, `mcases`, `unfold`, `unfold_let`, `unfolds`, `assumption`, `later`, `using`, `usingOnly`, `hiding`, `defaultImpl`, `<\|>` / `try` | `Meta` |
| `$`, `#'`, `repeat` | `Function.Meta` |
| `equation`, `cong`, `linarith`, `simplify`, `rewriteEq` | `Algebra.Meta` |
| `∃`, `contradiction` | `Logic.Meta` |
| `Empty`, `Not`, `\|\|`, `<->`, `propExt` | `Logic` |
| `Or`, `inl`, `inr` | `Data.Or` |
| `Quotient`, `in~`, `~-equiv`, `Equivalence` | `Relation.Equivalence` |
| `ide` / `*` / `+` / `inverse`, `negative` / `CRing`, `Ring`, `PseudoCRing` | `Algebra.Pointed` / `Algebra.Monoid` / `Algebra.Group` / `Algebra.Ring` |
| the operators `<=` / `<` | `Order.PartialOrder` / `Order.StrictOrder` |
| `LinearlyOrderedSemiring`, `OrderedRing` (what `linarith` dispatches on) | `Algebra.StrictlyOrdered` |
| the instances on `Nat` / `Rat` / `Real` (so `+`, `<=`, solvers work there) | `Arith.Nat` / `Arith.Rat` / `Arith.Real.Field` |

Operators and instances come from different modules: bare `+` or `<=` on `Nat` needs `Algebra.Monoid` / `Order.PartialOrder` *and* `Arith.Nat`. `Nat.+` and `Nat.*` (qualified, from the Prelude) work without either.

Boilerplate that covers most algebraic proofs:

```arend
\import Algebra.Group
\import Algebra.Meta
\import Algebra.Monoid
\import Algebra.Pointed
\import Algebra.Ring
\import Algebra.StrictlyOrdered
\import Arith.Nat
\import Function.Meta
\import Logic
\import Logic.Meta
\import Meta
\import Order.PartialOrder
\import Order.StrictOrder
\import Paths
\import Paths.Meta
```

`Meta`, `Paths.Meta`, `Algebra.Meta`, `Function.Meta`, `Logic.Meta` are provided by the library's Java extension: they import fine but are not files under `src/` — don't grep for them.

**Symptoms of a missing or shadowing import:**

- `Cannot resolve reference 'X'` — the module defining `X` is not imported (`Empty` → `Logic`, `negative` → `Algebra.Group`, `ide` → `Algebra.Pointed`, `<=` → `Order.PartialOrder`). A class's `\func` members (`pow`, `*n`, …) do not resolve bare even when imported: write `Monoid.pow` — see **arend-quirks**, *Records and classes*.
- `Cannot find a reference to constructor among provided patterns` / `In: inl a` — the type is visible but its constructors' module is not imported (`inl`/`inr` need `Data.Or`; `in~` needs `Relation.Equivalence`). Importing only the type, `\import Data.Or (Or)`, gives the same error. The message never says "import".
- `ext` reporting `Expected type: \Pi (i : I) -> ?A i` — see *ext* below; often the same missing `in~` import.
- `ambiguous reference`, or `linarith`/`equation` not finding an instance that is plainly there — a local definition with a library name (a tutorial-style `\class Monoid`, a local `\data Empty`) shadows the library's. Drop or rename the local one.

---

## Metas

### `rewrite` / `rewriteI` — rewrite in the goal

`rewrite (p : a = b) t : T` replaces the occurrences of `a` in `T` by a variable and returns `transportInv (\lam x => T[x/a]) p t`; `t` proves the rewritten goal. If the expected type is unknown, it rewrites in the type of `t` instead.

```arend
\func rw-ex (n m : Nat) (p : n = m) (q : m = 0) : n = 0 => rewrite p q
```

Variants:
- `rewriteI p t` ≡ `rewrite (inv p) t`.
- `rewrite {i_1, …} p t` — only the listed occurrences (1-indexed, counted after the previous replacements).
- `rewrite (p_1, …, p_n) t` ≡ `rewrite p_1 (… (rewrite p_n t))`. With a solver as `t` this is the workhorse: `rewrite (l1, l2) equation`.
- `p` may be a function: `rewrite p` is `rewrite (p _ … _)`. So **declare rewriting lemmas with implicit arguments** — `rewrite lemma` then works bare, instead of a motive plus spelled-out arguments.
- `rewriteEq p t` (`Algebra.Meta`) — matches subexpressions equal up to monoid/category laws (associativity, identities) when the parenthesization differs.

Pitfalls:

- **`rewrite p q` vs `rewrite p in q`.** `in` drops the expected type, so `rewrite` works on `q`'s type. If `rewrite p q` cannot find the LHS in the goal, try `rewrite p in q` (see *in / at*).
- **The search does not evaluate.** `rewrite` will not run a definition by pattern matching to expose the LHS; unification (a `*>` chain, an argument position) does. The diagnostic prints the *normalized* goal, so it reads as a contradiction:

  ```arend
  \func dbl (n : Nat) : Nat \elim n | 0 => 0 | suc n => suc (suc (dbl n))
  \func rd  (x : Nat) (p : suc (suc (dbl 0)) = x) : dbl 1 = x => rewrite p idp   -- fails
  \func rd' (x : Nat) (p : suc (suc (dbl 0)) = x) : dbl 1 = x => p               -- works
  ```

      [ERROR] Cannot find subexpression
        Subexpression: 2
           Expression: 2 = x
        In: rewrite

  When the pattern appears only after a reduction, write the step as a chain element instead of a `rewrite`.
- **`{?error}` inside `Subexpression:`** means the lemma's implicits were never solved, so the pattern was never built — read it as "cannot infer the implicits", not "the term is absent". Typical when the operands sit under an operation of a concrete instance that computes (see **arend-quirks**, *Concrete instances compute*). Spell the implicits (`rewrite (lemma {x} {y}) t`) or move the step into a helper whose operands are parameters.
- **`transport (\lam x => x.f …) p t` on a record fails with `Expected type: a class`**; `rewrite p t` does the same job without the projection lambda. Keep `transport` only where the expected type is not pinned (an argument of `linarith`, one side of a chain whose middle is free).

### `run { f_1, …, f_n, t }` — chain unary functions

`run { e_1, …, e_n }` ≡ `e_1 $ e_2 $ … $ e_n`. **The seed is last**: `run { rewrite p, rewrite q, idp }` is `rewrite p (rewrite q idp)`.

```arend
\func run-ex {A : \Type} (a b c d : A) (p : a = b) (q : b = c) (r : c = d) : a = d
  => run { rewrite p, rewrite q, rewrite r, idp }
```

- **Probe:** replace any entry (or the seed) with `{?}` to see the goal at that point.
- **`later $`:** an entry that fails with an unresolved-goal error while the same meta works on its own usually needs its invocation deferred: `run { later $ rewrite p, idp }`.
- **`\lam x,` opens a binder** and the rest of the block becomes its body:

  ```arend
  \func run-lam (f g : Nat -> Nat) (p : \Pi (n : Nat) -> f n = g n) : f = g
    => run { ext, \lam n, p n }
  ```
- **`\have` is an entry too**, scoping over the rest of the block:

  ```arend
  \func run-have (a b : Nat) (p : a = b) : b = a
    => run {
      \have | q : b = a => inv p,
      rewrite q,
      idp
    }
  ```

  Worth it when what follows the rewrite is short; otherwise `\have … \in rewrite q $ …` keeps the punchline on top.
- **Slot composers for inequality chains:** `` `<∘ q `` is `\lam h => h <∘ q` (likewise `` `<=∘ ``). Align with `rewrite`, compose through each known bound, close the slack with `linarith`: ``run { rewrite <align>, `<∘ <bound>, linarith }``.

  ```arend
  \lemma slot {a b c : Rat} (p : a < b) (q : b < c) : a < c => run { `<∘ q, p }
  ```

### `in` / `at`

`f in x` ≡ `\let r => f x \in r`: `x` is checked without the expected type, so a meta looks at `x`'s type instead of the goal. Invisible for most metas; observable for `rewrite`, `simplify`, `simp_coe`, `unfold`.

```arend
\func rw-in (x y : Nat) (p : 0 = x) (q : 0 = y) : x = y => rewrite p in q   -- rewrites 0 to x in q's type
```

`in` has loose precedence (right-associative, priority 1): `(simp_coe in t) b` differs from `simp_coe in t b`. `(f_1, …, f_n) in x` ≡ `f_1 in … f_n in x`.

`(f at h) body` replaces the binding `h` by `f h` for the rest of `body`; it works on parameters and on `\let` / `\have` bindings. Equivalent forms:

```arend
\func at-ex  (n m : Nat) (p : n = m) (q : n = 0) : m = 0 => rewrite p at q $ q
\func at-ex2 (n m : Nat) (p : n = m) (q : n = 0) : m = 0 => run { rewrite p at q, q }
```

`(f_1, f_2) at h` ≡ `f_1 (f_2 h)`.

### `cases` — multi-scrutinee `\case`

`cases (e_1, …, e_n) \with { … }` avoids `\case` boilerplate. `arg addPath` adds the equation between the scrutinee and the matched pattern — `cases (e arg addPath)` ≡ `cases (e arg (name = x), idp : e = x)` — and rewrites the dependent return type:

```arend
\func baz {A : \Type} (B : Bool -> \Type) (p : A -> Bool) (a : A) (pt : B true) (pf : B false) : B (p a)
  => cases (p a arg addPath) \with {
    | true, q => pt
    | false, q => pf
  }
```

(`Bool` is in `Data.Bool`.) Other `arg` parameters: `name`, `as`.

### `mcases` — split along a definition's clauses

`mcases {f}` finds the invocations of `f` in the goal and splits along `f`'s own clauses. `f` must be defined by pattern matching:

```arend
\func felim (n : Nat) : Nat \elim n | 0 => 5 | suc _ => 5
\func mcases-ex (n : Nat) : felim n = 5 => mcases {felim} \with { | 0 => idp | suc _ => idp }
```

For a function whose body is a `\case`, `mcases {f}` reports `Expected a function defined by pattern matching`. Plain `mcases \with { … }` matches `\case` expressions written literally in the goal — a call of a `\case`-bodied function is not one (`Cannot find matching subexpressions`). Variants: `mcases {(f, k)}` (only the k-th occurrence), `mcases {f, g}`. `mcases \with { … }` also replaces a hand-written `\case d \as d \return … \with { … }` motive.

### `simplify` — algebraic normalizer

Removes identity elements, double inverses and zeros using the instance of the goal (`Monoid`, `Group`, `Ring`, …). `simplify in h` works on a hypothesis.

```arend
\func simp-ex {M : Monoid} (x : M) : x = x * ide => simplify
\func simp-neg {R : Ring} (x : R) : negative (negative x) = x => simplify
```

It is **not a decision procedure**: no commutativity, no distribution. On `x * y = y * x` in a `CMonoid` it reports `Nothing to simplify` followed by `Expressions are not equal` / `Left: x M.* y` / `Right: y M.* x`; other failures say `Meta 'simplify' failed`. Don't retry — switch to `equation`, or one `rewrite` to align the sides and then `simplify`. For component identities of a concrete record (`0 * 0 + 0 * 0 = 0`, `0 + x = x` on a named instance) `simplify` is the right tool and reads better than a solver.

### `equation` — chained equality and the ring/group solvers

`equation a_1 … a_n` proves `a_0 = a_{n+1}` through the listed intermediate terms. A step's proof is found in the context, supplied in `{…}`, or left to the solver:

```arend
\func eq-ex {M : Monoid} (x y z : M) (p : x = y) (q : y = z) : x = z => equation x y z
```

Use `==<` / `>==` / `qed` (from `Paths`) instead when each step deserves to be read. A context equation is used only as a whole step, never inside one — with `p : g = h` in scope, `g * g = h * h` fails:

    Cannot solve equation
      Equation: g * g = h * h
      Reduced to: g * g = h * h
      In: group

**Solver choice.** Plain `equation` picks the solver from the structure it finds: over `{R : CRing}`, `Rat` or `Real` it proves `x * y = y * x` as is. `equation.cRing`, `equation.cMonoid`, `equation.monoid`, `equation.group` force one. `Ring solver failed` with two sides that differ only in factor order means the instance found is non-commutative:

    Ring solver failed
      Equation: v0 * v1 = v1 * v0
      where
        v0 = x
        v1 = y

— check the class the statement quantifies over (`{R : Ring}` here).

**There is no commutative-rng solver.** At `{R : PseudoCRing}` (no `ide`) plain `equation` falls back to the monoid solver and loses both commutativity and distribution — the tell is the solver's name, `Monoid solver failed`, on sides that differ by order or one distribution step. `equation.cRing` there gives `Cannot infer an instance of class 'CRing' with classifying expression: R.E`. Write the chain by hand (`pmap (* z) *-assoc *> *-assoc` and friends) or keep the unital hypothesis.

**What the solver treats as atoms.**
- `pow t (a + b)` with a variable exponent sum:

      Ring solver failed
        Equation: v0 = v1 * v2
        where
          v0 = pow {R} t (a + b)

  Split first: `rewrite Monoid.pow_+ equation`. Each tuple entry of `rewrite (Monoid.pow_+, Monoid.pow_+, …)` splits one distinct sum node (all its occurrences); too few leave compound atoms in the `where` list, too many report `Cannot find subexpression`.
- Operations of a concrete record that compute (a component formula): the solver normalizes into components and fails. State the step over an abstract class and instantiate — see **arend-quirks**, *Concrete instances compute*.

**`equation.group` and hypotheses.** The group solver decides every identity of the free group — so an *unconditional* group identity needs no lemma: call `equation.group` at the use site. For a *conditional* identity, the `{…}` entries are **proofs of chain steps**, each bridging two consecutive terms; the solver closes the gaps. With no intermediate terms there is a single step, so the one entry must bridge the whole goal. `pmap` the hypothesis into such a bridge:

```arend
\lemma grp-1 {E : Group} {g h : E} (p : commutator g h = ide) : conjugate g h = h => equation.group {pmap (* h) p}
\lemma grp-2 {E : Group} {g h : E} (p : commutator g h = ide) : g * h = h * g => equation.group {pmap (* (h * g)) p}
\lemma grp-3 {E : Group} {g h : E} (p : commutator g h = ide) : commutator h g = ide => equation.group {pmap inverse p}
```

Ask "what context turns `p`'s two sides into my two sides" and `pmap` that context. A raw `equation.group {p}` that does not bridge gets a misleading report — the *normalized* expected type next to a search for the hypothesis's side:

    Cannot find subexpression
      Expected type: g * h * g^-1 = h
      Subexpression: g * h * g^-1 * h^-1
      In: p

Read it as "my step does not span a chain position", never as "the term is absent". When no single step can bridge (the relation has to be applied at two interior positions), use a pivot: an unconditional `equation.group` restating one side so the hypothesis's side surfaces, then `rewrite`/`pmap` with the hypothesis, then a second solver call. Whether one step suffices is decidable in advance: compute `RHS⁻¹ · LHS` in the free group and test whether it is a conjugate of the hypothesis's word. A 20-line reduced-word checker (stack-based cancellation over `[(generator, sign)]`) decides pivots and checks that a stated identity is true at all — far cheaper than guessing against the typechecker; for conditional identities, evaluating in a small permutation group is a cheap sanity check. Name a flipped hypothesis (`commutator h g = ide` from `commutator g h = ide`) rather than re-deriving it inline.

### `cong` — congruence closure

Proves `f x_1 … x_n = f y_1 … y_n` from equalities `x_i = y_i` in scope (pass extra ones with `using (…)`). Multi-argument `pmap`. The goal usually lives in `\Type`, so use `\func`, not `\lemma`.

```arend
\func cong-ex {A B : \Type} (f : A -> A -> B) (x x' y y' : A) (p : x = x') (q : y = y') : f x y = f x' y' => cong
```

If it fails on something obvious, check the needed `x_i = y_i` is directly in the context (not inside a `\Sigma` or under another name).

### `ext` — extensionality

| Goal | Subgoal (the argument's type) |
|---|---|
| `f = g` for functions | `\Pi (x_1 : A_1) … -> f x_1 … = g x_1 …` |
| `t = s` for a `\Sigma` or a record | `\Sigma (p_1 : t.1 = s.1) …` (with `coe` corrections for dependent fields; `\Prop` fields omitted) |
| `A = B` for `A B : \Prop` | `\Sigma (A -> B) (B -> A)` |
| `A = B` for `A B : \Type` | `QEquiv {A} {B}` |
| `x = y` in a `\Prop` | none — `ext` closes it |

```arend
\func fun-eq (f g : Nat -> Nat) (h : \Pi (n : Nat) -> f n = g n) : f = g => ext h
\func sig-eq (p p' : \Sigma Nat Nat) (h1 : p.1 = p'.1) (h2 : p.2 = p'.2) : p = p' => ext (h1, h2)
\lemma prop-eq (A B : \Prop) (f : A -> B) (g : B -> A) : A = B => ext (f, g)
```

Record copattern form: `ext R { | f_1 => p_1 | … }`. `exts` also applies `ext`/`simp_coe` to fields. A subgoal full of `coe` means a dependent field — prove it directly or follow up with `simp_coe`.

**`Expected type: \Pi (i : I) -> ?A i` from `ext` is a lie.** `ext` knew the goal, but its *argument* failed to elaborate and it fell back to `path` with an unknown family. The tell: the printed actual type is exactly the statement you intended, and `ext \lam x => {?}` alone typechecks. A frequent cause is a missing import inside the argument — `ext \case \elim __ \with { | in~ _ => idp }` without `Relation.Equivalence` also reports `Cannot find a reference to constructor among provided patterns`. Don't spend rounds on `later $`, ascriptions or `\have`-binding the argument.

### `linarith` — linear arithmetic

Fourier–Motzkin over the goal's `LinearlyOrderedSemiring` / `OrderedRing` instance. Reads hypotheses from the context; you don't pass them.

```arend
\lemma lin-1 {a b : Nat} : 0 <= a + b => linarith
\lemma lin-2 {a b c : Nat} (p : a <= b) (q : b + c <= a) : c = 0 => linarith
\lemma lin-3 {R : LinearlyOrderedSemiring} {a b c : R} (p : a <= b) (q : b + c <= a) : c <= 0 => linarith
```

The instance comes with the carrier's module: `Arith.Nat` (plus `Order.PartialOrder` for `<=`), `Arith.Rat`, `Arith.Real.Field`; no `\open` is needed. `Cannot infer an instance of class 'LinearlyOrderedSemiring'` means that import is missing or a local class shadows the library's.

What it does not see:

- **Nonlinear terms are atoms, and a product with a sum factor is not expanded:**

      Cannot solve the equation
        Equation: a * b + a <= c
        Assumptions: a * (b + ide) <= c

  Restate such hypotheses in distributed form and bridge with `=_<= equation` (or `<∘l` / `=_<=` combinations when both sides need reshaping).
- **Factor order matters**: `a * b` and `b * a` are different atoms (`Equation: b * a <= c` / `Assumptions: a * b <= c` fails). Normalize the order by hand in every hypothesis and the goal; nothing in the output points at this.
- **A `\func` constant whose value does not compute to a literal is an atom.** Over `Real`, `\func third : Real => ratio 1 3` makes even `third > 0` fail (`Equation: zro < third` / `Assumptions:`). A `\meta` is substituted syntactically, so the solver sees the literal — ascribe its body, or it elaborates as a `Rat` wherever nothing else pins the type:

  ```arend
  \meta third => (ratio 1 3 : Real)
  \lemma third>0 : third > 0 => linarith
  ```

  A *parameterised* `\func` stays folded by design (its lemmas are its interface): restate the goal with the body spelled out and convert at the end with `=_<= equation`.
- **Too many hypotheses**: past ~20 it starts failing on goals it can do, and unrelated facts print with unresolved metas. `usingOnly (h_1, …, h_k) linarith` restricts the context and makes failures readable:

  ```arend
  \lemma lin-4 {a b c : Nat} (p : a <= b) (q : b + c <= a) (r : 5 <= 7) : c = 0 => usingOnly (p, q) linarith
  ```
- **Polynomial identities are `equation`'s job.** If `linarith` prints `Cannot solve the equation` with two algebraically equal sides (often differing by `natCoef 2` vs `2`, or by where a `negative` sits), switch to `equation`. `linarith` is for numeric (in)equalities; they don't substitute for each other.
Hints such as `linarith h` are unnecessary when `h` is in scope (only when it is hidden, e.g. shadowed in a `\let`); strip them on the final pass.

### `simp_coe` — push `coe` / `transport` through structure

For goals full of `coe`/`transport` over `\Pi`, `\Sigma` or records (common with HITs). Niche; reach for it only when the goal is `coe`-ridden.

### `unfold`, `unfold_let`, `unfolds`

`unfold (f_1, …, f_n) e` unfolds the listed functions/fields/variables in the expected type before checking `e` (in `e`'s type if the expected type is unknown); `unfold f e` for one. `unfold_let` expands `\let`s, `unfolds` unfolds top-level functions and fields recursively. A `\func` already reduces during unification, so `unfold` is needed only where the elaborator does not look through `f` — projections of `f`'s result, or matching for `rewrite`/`pmap`. Unfold minimally: drop each argument and see what fails.

### `assumption`

Fills the goal from the context, trying later bindings first. `assumption {n}` is the n-th variable counting from the end; `assumption {n} a_1 … a_k` applies it to arguments.

### `using` / `usingOnly` / `hiding`

- `using (e_1, …) e` — checks `e` with the `e_i` added to the context: a derived fact visible to search-based metas in one sub-term only.
- `usingOnly (e_1, …) e` — replaces the context by the `e_i`; use when irrelevant hypotheses confuse `linarith`, `assumption`, `cong`.
- `hiding (x_1, …) e` — hides the listed local variables.

### `$` / `#'` — application operators

From `Function.Meta`; they take part in implicit-argument inference. `f $ x` is right-associative, priority 0: `f $ g $ x` ≡ `f (g x)`. `f #' x` is the left-associative version: `f #' x #' y` ≡ `f x y`.

```arend
\func app-ex (f g : Nat -> Nat) (x : Nat) : f (g x) = (f $ g $ x) => idp
\func app2-ex (f : Nat -> Nat -> Nat) (x y : Nat) : f x y = (f #' x #' y) => idp
```

### `later`

`later meta args` defers the invocation until type inference has made more progress — the first thing to try when a meta inside a `run` chain fails with an unresolved expected type: `run { later $ rewrite p, idp }`.

### `repeat`

`repeat {n} f x` applies `f` exactly `n` times — it fails if any application fails, often as a spray of `Type mismatch` / `Expected type: a pi type`, so it is not "until no match". `repeat f x` applies `f` until it fails. For a known number of rewrites the tuple form `rewrite (p, p, p) t` is more predictable.

### `defaultImpl`

`defaultImpl C F E` is the default implementation of field `F` of class `C` applied to `E` (`E` may be omitted). Use it to refer to the default from an instance that overrides the field.

Other metas in `Meta`: `x <|> y` / `try` (try `x`, else `y`), `fails m` (succeeds iff `m` fails), `mkcon`.

---

## Decision table

| If the goal looks like… | Reach for |
|---|---|
| `f x_1 … x_n = f y_1 … y_n`, each `x_i = y_i` in scope | `cong` |
| Linear (in)equality: atoms times constants, summed, compared | `linarith` |
| Monoid/ring expression equal up to identities, inverses, zeros | `simplify` |
| Ring or field identity | `equation` (solver from the instance; `equation.cRing` to force) |
| Identity once a few lemmas are applied | `rewrite (l_1, l_2) equation` |
| Identity in a group (`*`, `inverse`, `ide`) | `equation.group` |
| …given an equational hypothesis `p` | `equation.group {pmap <context> p}` |
| …where no single step can bridge | pivot identity + `rewrite`/`pmap` + second `equation.group` |
| Identity over a commutative monoid (no `+`) | `equation.cMonoid` |
| Equality whose steps deserve names | `==<` / `>==` / `qed`, or `equation a_1 … a_n` |
| Substitute one term in the goal | `rewrite p t` (reversed: `rewriteI p t`; one occurrence: `rewrite {k} p t`) |
| Several substitutions, then trivial | `rewrite (p_1, …, p_n) idp` |
| Mixed chain (rewrite + pmap + sections) | `run { …, idp }` |
| Inequality chain (`<` / `<=`) | ``run { rewrite <align>, `<∘ <bound>, linarith }`` |
| Reshape a hypothesis before using it | `rewrite p at h $ body` |
| A meta should read a term's type, not the goal | `f in h` |
| `f = g` (functions), tuple or record equality | `ext h` |
| `F p = F p'` from `p.1 = p'.1` (proof irrelevance) | multi-`\elim` with `idp`, closing with `pmap2 … prop-pi prop-pi` |
| Goal mentions a function defined by pattern matching | `mcases {f}` |
| Goal contains a literal `\case` | `mcases \with { … }` |
| Remember the scrutinee's value while matching | `cases (e arg addPath)` |
| `coe` / `transport` chains in the goal | `simp_coe` |
| A definition in the goal must be unfolded | `unfold f body` |
| The witness is already in the context | `assumption` |
| A search-based meta drowns in hypotheses | `usingOnly (h_1, …) body` |
| One derived fact needed inside one expression | `using (h) body` |
| A meta in a `run` fails with an unresolved goal | prefix it with `later $` |
| Need to see an intermediate goal | replace an entry with `{?}` |

---

## Error → first move

| Message | Likely cause | First move |
|---|---|---|
| `Cannot resolve reference 'X'` | missing import, or a class `\func` member used bare | see *Imports* |
| `The type of a lemma must be a proposition` / `Actual level: \Type` | e.g. `f x = f y` for `f : A -> B`, `B : \Type` | `\func`; promote to `\lemma` only when the type is a proposition |
| `Type mismatch` / `Expected type: a class` / `Actual type: \Set0` / `In: Nat` | `a Nat.<= b`: `Nat` is a data type, not a class | bare `<=` with `Order.PartialOrder` + `Arith.Nat` (other causes: **arend-quirks**, *"Expected type: a class" — causes*) |
| `Nothing to simplify` / `Expressions are not equal`, or `Meta 'simplify' failed` | needs commutativity or distribution | `equation`, or one `rewrite` then `simplify` |
| `Ring solver failed`, sides differ only in order | instance found is non-commutative | check the class; `equation.cRing` |
| `Monoid solver failed` at a ring without `ide` | no rng solver | hand chain, or a unital class |
| `Ring solver failed` with `where` atoms like `pow {R} t (s + j)` | sums in exponents | split with `rewrite (Monoid.pow_+, …)` first |
| `Cannot solve the equation` from `linarith`, sides algebraically equal | polynomial identity | `equation` |
| `Cannot solve the equation` from `linarith`, assumptions look sufficient | sum-factor products, factor order, folded `\func` constant, too many hypotheses | see *linarith* |
| `Cannot find subexpression`, `{?error}` in the pattern | the rewrite lemma's implicits are unsolved | spell them; see **arend-quirks**, *Concrete instances compute* |
| `Cannot find subexpression`, the pattern visible in the printed goal | the pattern appears only after evaluation | write the step as a chain element |
| `Cannot find subexpression` naming a term in an `equation.group {…}` call | the step does not span a chain position | `pmap` the hypothesis into a whole-side bridge, or pivot |
| `Expected type: \Pi (i : I) -> ?A i` from `ext` | `ext`'s argument failed to elaborate | see *ext* |
| `Cannot solve equation` pairing `\Set0` with `E`, or `TruncP` with `contains`, then a mismatch printing a type where an element belongs | the receiver of a class member is a computed value, so nothing solves it | pin it: `C.member {receiver} …` — **arend-quirks**, *Instance search* |
| two `Cannot solve equation` lines naming two different index objects, unsolved `?a` next to a solved-looking functor/structure | an implicit with two valid readings, Arend picked the wrong one | pin the whole implicit prefix — **arend-quirks**, *Implicit arguments* |
| a meta in a `run` complains about an unresolved goal but works alone | expected type not pinned yet | `later $` |

---

## Style

Write in the target style from the first attempt — the typechecker tells you quickly when a compact form needs expanding. The end-of-task pass is **arend-formalize**, *4. Finish checklist* (dead code, naming, placement, hypotheses); its redundancy group is the *Compaction* list below.

### Choosing a surface form

- **Pure rewrites of the goal**: `rewrite (p, q, r) idp` — shorter than a `run` block. Merge consecutive rewrites: `rewrite (A, B) $ rewrite (C, D) t` → `rewrite (A, B, C, D) t`.
- **Rewrites + algebraic close**: `rewrite (p, q) equation`, one line.
- **Mixed chains** (rewrite, `pmap`, sections): `run { … }`; the vertical layout reads better than nesting.
- **One step on a hypothesis**: `f at h $ body`; several: `run { f_1 at h, f_2 at h, body }`.
- **Three or more steps worth naming**: `==<` / `>==` / `qed`. All steps trivial: `equation` with no intermediates.
- **Proof-irrelevance bridge** (`F p = F p'` from one component path): multi-`\elim` with the path in the same clause list, not a nested helper.
- **`run { {?} }` for step-by-step refinement** of goal manipulation (rewrites, transports, simplifications): wrap the goal in `run { {?} }`, replace the inner `{?}` by `rewrite <something>, {?}`, re-typecheck, repeat. Hybrid: set up induction with `\case \elim n`, prove the base, refine the step inside `run { {?} }`. Not when the difficulty is mathematical (if the step's bound is false, no chain helps), and not when assembling a value from named pieces — a `\have` chain is clearer there.

### Compaction

Apply while writing; then execute it item by item as the redundancy pass of the finish checklist, re-typechecking after each change.

- **Omit and re-typecheck**: every explicit implicit `{…}`, every type ascription `(e : T)`, every binder annotation `\lam (x : T) =>`. Restore only what the typechecker asks for. Within a chain, only the first ("anchor") step usually needs its implicits; later steps and the bodies of per-index lambdas recover theirs from their neighbours.
- **Qualify with the instance, not the class**: `inst.f args`, never `C.f {inst} args` (`R.pow x n`, not `pow {R} x n`). Don't qualify operators at all when the operands' types pin the instance; named lemmas outside the opened set still need qualification (a selective `\open M (f, g)` shortens them).
- **`\new Array A n (\lam i => e)` → `\lam i => e`.**
- **Sections instead of lambdas**: `\lam x => x + e` → `(+ e)`; slot composers `` `<∘ b `` and `$` instead of nested parentheses.
- **`transport (\lam x => P x) (inv p)` → `transportInv P p`**, and `transportInv (\lam x => C x) p t` → `rewrite p t` whenever the goal is what is being reshaped.
- **Replace hand-stepped `\have` chains** with `simplify` / `equation` / `linarith` when one of them closes the goal outright.
- **Hand-written `\case d \as d \return … \with {…}` motives → `mcases \with {…}`.**
- **Flatten existentials with `\let`.** `\case e \with { | inP (…) => body }` → `\let | (inP (…)) => e \in body`; `\let` bindings are sequential, so a cascade of truncated existentials becomes one flat block. Works whenever the result is a proposition; keep `\case` for genuinely multi-constructor scrutinees (`||`, `Or`, `Dec`).

  ```arend
  \lemma let-ex (h : ∃ (n : Nat) (n = 0)) (k : ∃ (m : Nat) (m = 1)) : ∃ (a b : Nat) (a + b = 1)
    => \let | (inP (n, p)) => h
            | (inP (m, q)) => k
       \in inP (n, m, rewrite (p, q) idp)
  ```
- **Interleave `\let` and `\have` at one indentation level** (`\let … \in \have … \in \let … \in body`, each `\in` at the same column) instead of nesting: `\have` for proofs, `\let` for values.
- **Inline single-use helpers and single-use `\have`s** — unless the `\have`'s ascription is what pins a lemma's implicits (see **arend-quirks**, *Opaque bindings: \have and \let*).
- **Pattern-match arrays with `::`** instead of rebuilding tails: with `\elim n, r` and clauses `| 0, nil` / `| suc n, a :: l`, the tail is the variable `l` rather than `\new Array A n (\lam i => r (suc i))` at every call.

  ```arend
  \func sumArr {n : Nat} (r : Array Nat n) : Nat \elim n, r
    | 0, nil => 0
    | suc n, a :: l => a + sumArr l
  ```

  The function then no longer reduces on a *variable* array, so convert the whole family of functions and lemmas over the same array together.
- **An eta-lambda that carries a coercion is not removable.** `\lam k => f k : Fin 3 -> Nat` for `f : Nat -> Nat` typechecks; plain `f` is `Type mismatch` / `Expected type: Fin 3 -> Nat` / `Actual type: Nat -> Nat`. Drop eta-lambdas only when the domains agree.
- **A compound constant repeated inside one proof** (a long bound appearing five times) is an opaque blob to the solvers and lengthens every line. Make it a parameter of a helper (`{C : R} (C>=0 : 0 <= C) (hC : … <= C)`) and pass the concrete value once at the call site; inside the helper `C` is a variable. A `\have C => <blob>` does not achieve this (see **arend-quirks**, *Opaque bindings: \have and \let*).
- **A case split needed inside a `\have`**: factor it into a separate `\private \lemma` rather than an embedded `\case \elim`.
- **Named constants**: use the library's named lemma for constant facts (`0 < 1` in a field, …) instead of re-deriving them — find it with `-ss`/`-ps`.
- **Repeated explicit embeddings** (`fromX x` at every call) → a `\use \coerce` (see **arend-quirks**, *Coercions*).
