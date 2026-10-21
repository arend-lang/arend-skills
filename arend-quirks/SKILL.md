---
name: arend-quirks
description: Survival notes for formalizing in Arend — where its syntax and semantics differ from Coq/Agda/Lean (paths, pattern matching, records and instance search, levels, opacity of \have, implicit arguments, comments) and the misleading errors those differences produce. Use when writing .ard files, reviewing Arend proofs, explaining Arend semantics, or debugging an Arend typecheck failure.
user-invocable: true
---

# Arend quirks

Where Arend departs from Coq/Agda/Lean habits, and the misleading diagnostics that follow. The tutorial and language reference at https://arend-lang.github.io/ are authoritative.

Companion skills: **arend-formalize** (workflow, CLI tools), **arend-prove** (metas: `rewrite`, `simplify`, `equation`, `linarith`, …), **arend-error-type-mismatch** and **arend-error-extraneous-input** (catalogues of misleading errors).

---

## Equality is a path type

- `Path (A : I -> \Type) (a : A left) (a' : A right)` is primitive: a function over the interval `I` with the definitional boundary conditions `f left => a`, `f right => a'`, checked when you write `path (\lam i => …)`.
- `a = b` is notation for `Path (\lam _ => A) a b`. Reflexivity is `idp` (`path (\lam _ => a)`); there is no `refl`, and `idp` acts as a constructor only in patterns.
- `J` is derived from `coe`; in practice use `transport`, `pmap`, or match on `idp`.
- Definitional eta: `path (\lam i => p @ i) == p`. Paths and `\Pi (i : I) -> A i` coerce into each other automatically.
- `p @ left` / `p @ right` reduce to the endpoints definitionally — use it.

## Matching on idp

- To match `p : e = e'` with `idp`, one of `e`, `e'` must be a variable that does not occur in the other (you are really matching the pair `(a', p)`), and its free variables must be bound at each of its occurrences. "Cannot match on idp here" means both sides are non-variables or share variables.
- In `\case`, bind the endpoint with `\elim`, or make it come from the scrutinee: `\case e \as x, idp : x = e \with { … }` reconnects the matched value with the expression.
- `J` by pattern matching:
  ```arend
  \func J {A : \Type} {a : A} (B : \Pi (a' : A) -> a = a' -> \Type) (b : B a idp)
          {a' : A} (p : a = a') : B a' p \elim p | idp => b
  ```

## \case, \elim, \with and termination

- `\func f x \elim x | …` makes `f n` **reduce** to the matching clause. `\func f x => \case x \with { … }` leaves a `\case` in normal forms, which is worse downstream. Eliminate parameters with top-level `\elim`/`\with`; use `\case` for expressions.
- The termination checker only sees **top-level** eliminations (`\elim`, `\with`): lexicographic order on parameters, size-change for mutual recursion. A decreasing call under a `\case` in the body is rejected — factor the recursion into a helper with `\elim`.
- `\case \elim x \with { … }` substitutes `x` in the return type per clause; for an expression use `\case e \as b \return T[b] \with { … }`. `\scase` is the strict variant (like `\sfunc`).
- **To reduce `f (C … rest)` in a lemma, eliminate `rest` itself.** For `f` defined by `\elim k, x` over a data type with indices, `f (stepD r rest)` reduces only when the lemma eliminates `rest` as a variable:

  ```arend
  \data D (n k : Nat) : \Set \elim k
    | 1 => base
    | suc k' => stepD Nat (D n k')

  \func f {n k : Nat} (x : D n k) : Nat \elim k, x
    | 1, base => n
    | suc k, stepD r rest => r Nat.+ f rest

  -- the computation rule, proved by eliminating rest:
  \lemma f-step {n k : Nat} (r : Nat) (rest : D n k)
    : f (stepD r rest) = r Nat.+ f rest \elim k, rest
    | 1, base => idp
    | suc k, stepD r' rest => idp
  ```

  Inside an induction proof that does `\elim k, lambda`, the destructured `stepD r rest` still does **not** reduce `f` — `rest` is a sub-component, not an eliminated variable. Chain through the helper instead: `f-step r rest *> pmap (r Nat.+) (IH rest) *> …`. If constructors carry path arguments, the helper may also need `\case \elim path \with { idp => … }` to make indices rigid. The same holds for `\sfunc` + `\peval`: `\peval f (C …)` fails with "Expression does not evaluate" unless the recursive argument is an eliminated variable.

## Data types

```arend
\data Vec (A : \Type) (n : Nat) \elim n
  | 0 => nil
  | suc n => cons A (Vec A n)
```

- The constructor list can depend on how parameters match; one clause can introduce several constructors. Clauses with an interval variable (`| seg I-var => …`) give higher inductive types with definitional boundary equations.
- Strict positivity: the type may not occur in a function domain or inside `Path` endpoints.
- `\cons f => body` defines a pattern-synonym-like constructor alias.

## Nat, Fin, Array, I

- `Nat.+` and `Nat.-` reduce on **either** side (`n + 0 => n`, `0 + m => m`, …) — not expressible in user code.
- `Fin n` is a **subtype** of `Nat` (and of `Fin (suc n)`); `zero`/`suc` are its constructors too.
- `Array A` is a record (`len`, `A`, `at : Fin len -> A`) with constructors `nil` and `::`: match it like a list, index it like a function. `Array A n` is a length-`n` vector; `DArray` is the dependent version.
- `I` has `left`, `right` and a hidden connecting constructor; **matching on `I` is forbidden** — use `coe`, `coe2`, `squeeze`, `squeezeR`. `coe (\lam x => A) a i => a` when `x` is not free in `A`.
- `iso` gives univalence and is not definable in user syntax; `Path.inProp` postulates proof irrelevance.

## Records and classes

- `\record` and `\class` are the same construct; `\class` additionally enables instance inference for implicit parameters of its type.
- **Parameters are fields**: `\record Pair (A B : \Type) | fst : A | snd : B` has four fields.
- **Fields are exported to the module scope; `\func`/`\lemma` members live in the class namespace** (`C.f`). This explains the next two items.
- Definitional eta: `\new R { | f => r.f | g => r.g }` ≡ `r`.
- The first explicit parameter of a `\class` is its **classifying field** (choose another with `\classifying`, disable with `\noclassifying`); an instance coerces to it, so `M : Monoid` used as a type means `M.E`.
- `\this` is an implicit parameter of type `R` in every member of `R`, usable only in argument positions.
- `\cowith` defines by copatterns — `\func zeros : Pair Nat Nat \cowith | fst => 0 | snd => 0` — and is equivalent to `\new`. It is not allowed in a `\let` (`mismatched input '\cowith'`); write `\new R { | f => … }` there.
- `\property p : P` needs `P : \Prop`; `\Prop`-valued fields are properties unless marked `\field`. Properties don't compute.
- Diamonds: `\extends A, B` with a common ancestor shares its fields, but same-named fields introduced separately in `A` and `B` are two fields (`A.f {r}`, `B.f {r}`). Keep `+` and `*` in separate structures rather than `\extends AbGroup, Monoid`.
- **A class's `\func` members don't resolve bare outside the class and its subclasses — only fields do**, even with the instance in scope. With

  ```arend
  \class Mg (E : \Set0) {
    | op : E -> E -> E
    \func twice (x : E) : E => op x x
    \func \infixl 7 *i (n : Nat) (x : E) : E => x
  }
  ```

  and `{M : Mg} (x : M)`:

  | Written | Result |
  |---|---|
  | `op x x` | fine (a field) |
  | `twice x` | `Cannot resolve reference 'twice'` |
  | `Mg.twice x`, `M.twice x` | fine |
  | `3 *i x` | `Cannot resolve reference '*i'` |
  | `3 Mg.*i x`, `3 M.*i x`, `(Mg.*i) {M} 3 x` | fine |
  | `Mg.*i {M} 3 x` | read as a section: `Expression is applied to an argument, but does not have a function type` |

  Inside a subclass of `Mg`, `twice` resolves bare. Members of a class reached only through a **field** do not: in a class whose carrier field is `S : AddMonoid`, write `n AddMonoid.*n x` — copy the qualification style of the neighbouring definitions.
- **Explicit implicits on a record's own method start with `{this}`.** Inside `\record Box (n : Nat) { \func get {m : Nat} (p : m = n) : Nat => m … }`, `get {0} p` hands `0` to the hidden `{this}`: `Type mismatch / Expected type: Box / Actual type: Nat / In: 0`. Write `get {_} {0} p`.
- **Dot notation**: `x.f` needs `x`'s type to be a record/class name, but `x` need not be a variable. A parameterless member `\func origin : Pt` of a class makes `X.origin.shift` work (it chains), and a record's `\func` member works on any expression of that record type. An *applied* expression whose type is a class awaiting instance search needs `C.f {e} …`.
- **A field named like a constructor shadows it module-wide.** With `\record HasPos | pos : Nat -> Nat` in the file, `\elim x | pos n => …` on an `Int` fails with `Cannot find a reference to constructor among provided patterns / In: pos n`. Rename the field, or import the record selectively (`\import M (Rec)`). An imported record's field can likewise shadow a same-named lemma from another import (symptoms: `Too many level arguments`, a mismatch on its first argument) — rename.

## Instance search

- Candidates are declared `\instance`s and instance parameters in scope; search matches the **classifying field**. There is no unification cascade like Coq's canonical structures.
- **The classifier of an `\instance` must be rigid** — a universe, a `\Sigma`, a record, or a partially applied data type or constructor. A field access (or `\func` result) is rejected:

  ```arend
  \class Carrier (E : \Set0) | c0 : E
  \record WrapS | W : \Set0 | w0 : W
  \instance badInst (w : WrapS) : Carrier w.W | c0 => w.w0
  -- Classifying field must be either a universe, a sigma type, a record, or a partially applied data or constructor
  --   In: Carrier (W {w})
  \func goodC (w : WrapS) : Carrier w.W \cowith | c0 => w.w0   -- pass it explicitly
  ```

- **Structures computed by a `\func` are invisible to search.** An element's type normalizes to the carrier, so search runs on the carrier: it finds nothing, or **silently picks another instance on the same carrier**:

  ```arend
  \func Opp (M : Monoid) : Monoid \cowith
    | E => M.E
    | ide => M.ide
    | * x y => y M.* x
    | ide-left => M.ide-right
    | ide-right => M.ide-left
    | *-assoc => inv M.*-assoc

  \func wrong {M : Monoid} (x y : Opp M) : x * y = y M.* x => idp
  -- Expressions are not equal / Left: x M.* y / Right: y M.* x   (x * y used M's product)
  \func pinned {M : Monoid} (x y : Opp M) : (*) {Opp M} x y = y M.* x => idp
  ```

  On a carrier with no instance (here `\Sigma`) you get `Cannot infer an instance of class 'Pointed' with classifying expression: \Sigma` for `ide`, `… 'Semigroup' …` for `*`. Pin the structure at every operation on its elements: `(*) {X} a b`, `ide {X}`, `inverse {X} a`, `C.member {X} …`. Other faces of the same cause:
  - a `C.member` call whose receiver is a computed value reports unrelated `Cannot solve equation` pairs — `\Set0` vs `E`, `TruncP` vs `contains` (the class's field types escaping into unification) — then a `Type mismatch` printing an argument's type where an element belongs. Read it as "the receiver is unsolved" and pin `{receiver}`;
  - composition in a `\func`-defined category: search picks the category the hom types reduce to and may compose in the opposite order. Pin the instance *and* the object implicits: `Precat.o {X} {A} {B} {D} g f`.
- **A class whose classifying field is a predicate is instance-searched on the predicate** (arend-lib's `SubSet` classifies by `contains`):

  ```arend
  \class Sub (S : \Set0) (\classifying has : S -> \Prop)
  \func memb {S : \Set0} {P : Sub S} {x : S} (h : P.has x) : Nat => 0
  \func evenP (n : Nat) : \Prop => n = n
  \func bad (n : Nat) (h : evenP n) : Nat => memb h
  -- Cannot infer an instance of class 'Sub' with classifying expression: n = n
  -- Cannot infer parameter 'x' of definition 'memb'
  \func good (n : Nat) (h : evenP n) : Nat => memb {Nat} {\new Sub Nat evenP} h
  ```


## Concrete instances compute

- A field implemented by a formula **without pattern matching reduces whenever the instance is concrete — for variable operands too.** arend-lib examples: `ComplexField.*` is `\new Complex (x.re * y.re - x.im * y.im) (…)`, `SetCat`'s composition is `\lam x => g (f x)`, and a sum or product over an array literal normalizes to the explicit expression.
- Consequences:
  - solvers see components, not the operation:
    ```arend
    \lemma bad {x y : Complex} : x * y = y * x => equation.cRing
    -- Cannot solve equation … where v0 = \new Complex (x.re * y.re - x.im * y.im) (x.re * y.im + x.im * y.re) …
    ```
  - `rewrite` with implicits left to unification fails, and the message shows an expression that visibly contains the pattern:
    ```arend
    \lemma bad (h q : Complex) : cabs (h * h * q) = cabs h * cabs h * cabs q
      => rewrite (cabs_*, cabs_*) idp
    -- Cannot find subexpression
    --   Subexpression: cabs ({?error} * {?error})
    --      Expression: cabs (h * h * q) = cabs h * cabs h * cabs q
    \lemma good (h q : Complex) : cabs (h * h * q) = cabs h * cabs h * cabs q
      => rewrite (cabs_* {h * h} {q}, cabs_* {h} {h}) idp
    ```
    `{?error}` in the subexpression means the implicits were never solved — not that the term is absent;
  - unification can't read implicits that occur only under such an operation (`pmap (∘ _)`, `o-assoc` in `SetCat` report `Cannot infer parameter`), and lemmas over a sum of an array literal can't read their arrays off the goal.
- **Fix: keep the term neutral.** State the step over an abstract class parameter and instantiate, or make the operands explicit parameters of a helper lemma, or state an array lemma over a variable array:

  ```arend
  \lemma comm {C : CRing} {x y : C} : x * y = y * x => equation.cRing
  \lemma comm-Complex {x y : Complex} : x * y = y * x => comm
  ```

  An abstract helper often weakens the hypotheses too.

## Coercions

- `\use \coerce toT (x : S) : T => …` in the `\where` of `S` or `T` defines a coercion (the last parameter is the source). `\coerce` on a record field or a constructor promotes it to a coercion; a classifying field gives one automatically; coercion into a function type partially applies.
- Coercions fire silently: when a type surprises you, check for an inserted coercion before blaming unification.
- Hoist an embedding written at every call site (`inj x`) into one `\use \coerce` in the target's `\where`; with `\open T \using (long \as short)` for constants, expressions shrink to `i * x`.
- **Don't put `\coerce` on the payload field of a wrapper whose operations differ from the payload's.** When the payload's structure is an instance in scope, the coercion fires before instance search on the wrapper:

  ```arend
  \record TaggedM {M : AddMonoid} (s : M) (\coerce val : M)
  \instance TM {M : AddMonoid} (s : M) : AddMonoid (TaggedM s)
    | zro => \new TaggedM s zro
    | + a b => \new TaggedM s (a.val + b.val)
    | zro-left => pmap (\lam x => \new TaggedM s x) zro-left
    | zro-right => pmap (\lam x => \new TaggedM s x) zro-right
    | +-assoc => pmap (\lam x => \new TaggedM s x) +-assoc

  \func sumM {M : AddMonoid} {s : M} (a b : TaggedM s) : M => a + b         -- typechecks: the sum in M
  \func sumT {M : AddMonoid} {s : M} (a b : TaggedM s) : M => (a + b).val
  -- Type mismatch / Expected type: a class / Actual type: M.E / In: a + b
  ```

  Operations only the wrapper has are unaffected. Keep `\coerce` for one-way embeddings you don't compute over.

## Extending records

- **A body with methods needs braces around the whole body.** The brace-less form accepts fields only, so a following `\func` lands at top level:

  ```arend
  \record R0 (I : \Set0)
    | f : I -> I
  \func m (x : I) : I => f x    -- Cannot infer parameter 'this' of definition 'f'

  \record R1 (I : \Set0) {
    | f : I -> I
    \func m (x : I) : I => f x
  }
  ```

  For a stray `\lemma` you also get a bogus `The type of a lemma must be a proposition`. Mixing forms (`\class C (E : \Set0) | op : … { \func … }`) is a parse error at the `|`.
- `| F => v` implements an inherited field; `\override F : T'` narrows its type to a subtype.
- **Field implementations cannot reference the record's own methods.** A bare name gives `Cannot resolve reference 'helper'`; `\this.helper` gives `Dependency cycle / C - C.helper`. Only fields and outside definitions work — use a top-level helper that takes what it needs explicitly, or inline the method body:

  ```arend
  \record P | val : Nat
  \func helperTop : Nat => 3
  \record C \extends P { | val => helperTop }
  ```

- Redeclaring a parent's parameter (`\record C4 (A : \Set0) \extends P3`, where `P3` has `(A : \Set0)`) warns `Field 'A' is already defined in super class at P3.A`; drop it — it is inherited.
- `\coerce` on a field propagates through `\extends`: with `\record Fn | \coerce ap : Nat -> Nat` and `\record Fn2 \extends Fn`, `f 3` works for `f : Fn2`. A descendant's own member with the coerced field's name clashes; rename it.
- A field whose hypothesis is empty is implemented by an empty `\case` (destructure truncations first): `\record V | never : Fin 0 -> Nat`, `\func vv : V \cowith | never j => \case j \with {}`.
- Audit for a record refactor: implementations reference only fields and top-level helpers; braces around any body with methods.

## Subtyping between records

- **A record is a subtype only of the classes it names in `\extends` (transitively)** — having all the fields is not enough:

  ```arend
  \record L | l : Nat
  \record R | r : Nat
  \record LR \extends L, R
  \record L' \extends L
  \record R' \extends R
  \record LR' \extends L', R'                 -- has all of LR's fields, but is not an LR
  \func needLR (x : LR) : Nat => x.l
  \func bad (y : LR') : Nat => needLR y      -- Type mismatch / Expected type: LR / Actual type: LR'
  ```

  Name the ancestor: `\record LR' \extends LR, L', R'`.
- Two superclasses that `\override` a shared field to different types conflict, even when the types are comparable: `The types of the field 'S' differ in super classes 'B1' and 'B2'`. Re-override in the descendant, which settles it: `\record B12 \extends B1, B2 { \override S : \Prop }`.
- Conflicting default implementations inherited from two parents are tolerated; only field types must agree.
- **`\open` does not re-export**, in a `\where` or at file level. After `\func N0 => 0 \where \open M0 (a0)`, `a0` is visible in `N0`'s body, but `N0.a0` elsewhere fails with `Type mismatch / Expected type: a class / Actual type: Nat / In: N0` (resolution falls back to field access on the value; for a definition with parameters the error may name those instead, e.g. `Parameter 'I' must be specified explicitly`). When a helper moves out of `M`'s `\where`, update the call sites.

## Universes and levels

- `\Type` has a **single predicative level**: `\Type n`; bare `\Type` is the infinite level. Cumulative: `A : \Type n` ⟹ `A : \Type (suc n)`. There is no second (homotopy) level argument: `\Type p h`, `\lp`, `\lh`, `\oo-Type` no longer exist.
- Homotopy levels are separate universe keywords, each with its own predicative level: `\Prop` (impredicative, no level), `\Set n` = `\0-Type n`, `\n-Type m`, `\Type m`. `\Prop : \Set 0`; `\k-Type p : \(k+1)-Type (p+1)`; `\Type p : \Type (p+1)`; `A : \Prop` ⟹ `A : \Set n` ⟹ … ⟹ `A : \Type n`.
- A truncated universe needs a finite level: bare `\Set` gives `Infinite level is not allowed here / In: \Set`; write `\Set 0` or use a level parameter. `\func x : \Type => \Type` is rejected (the infinite `\Type` is not a member of itself).
- Level polymorphism is explicit and predicative only: `\func id.{l} (A : \Type l) (a : A) => a`; several parameters `\func f.{l1, l2} …`; arguments `id.{2}`, `f.{\suc l}`; usually inferred. Level expressions: numerals, parameters, `\suc l`, `\max l1 l2`. Homotopy level is not abstractable.
- **Definitions written without level parameters.** A `\func` mentioning only bare `\Type` is fixed at the infinite level and takes no level arguments (`idT.{2}` → `Too many level arguments`). A `\record`/`\class` whose parameters use bare `\Type` is level-polymorphic, but written without level arguments inside a definition body it is taken at the infinite level:

  ```arend
  \record Gr (I : \Type) | rel : I -> I -> \Type
  \func bad.{u} : \Type => \Pi {I : \Type u} {G : Gr I} -> Nat
  -- Infinite level is not allowed here / In: Gr { | I => I }
  \func ok1.{u} : \Type => \Pi {I : \Type u} {G : Gr.{u} I} -> Nat
  \func ok2.{u} {I : \Type u} (G : Gr I) : Nat => 0          -- as a parameter it is fine
  ```

  A record whose parameters have fixed levels takes no level arguments (`Too many level arguments`): quantify over it only at finite levels, or make it a parameter of the statement. A class parameter written without levels (`{J : Precat}`) sits at the infinite level, and bare operations may resolve their instance to it — symptom `Expected type: \Set u / Actual type: \Set` plus `Cannot infer parameter` errors. Give it levels (`{J : Precat.{u,u}}`) and qualify the other structure's operations (`C.Hom`, `C.∘`).
- The level of a data type is the max over its constructor arguments (unused parameters don't count); of a record, over its unimplemented fields. A declared level parameter is kept: `\class C.{l} (A : \Type l)` gives `C.{5} Nat : \Type5`. A `\Pi`'s homotopy level is the codomain's; its predicative level is the max.

## \use \level

- Having proved a type has a lower homotopy level than inferred, write `\use \level <proof>` in its `\where`; the type then lives in the lower universe (e.g. `Dec P : \Prop` although `| yes P | no (P -> Empty)` is a `\Set0` by default). The proof must target `ofHLevel (D p_1 … p_k) n` for a constant `n`.
- For `\data` this means *squashed*: matching on it is allowed only into a universe ≤ its own, or inside `\sfunc`, `\lemma`, `\use \level`, `\scase`. `\truncated \data … : \Prop | …` is the sugar for squashing into `\Prop`.
- `\level T p` as a result type (`\lemma lem : \level A p => …`) tells the checker `T` has the required level.

## Function kinds: \func, \sfunc, \lemma, \type

- `\func` reduces. `\sfunc` never reduces; use `\eval f x` (its value) or `\peval f x` (the equation `f x = body`) at use sites. `\lemma`'s result must be a proposition, and it doesn't reduce. `\type` is a type alias that doesn't unfold.
- `\peval` works only on an `\sfunc` (or `\scase`); on a `\func` it fails with `Expected a function (defined as \sfunc) applied to arguments`.
- Default to `\func`; use `\lemma` for propositions you cite, so unfolding doesn't bloat types, and `\sfunc` when unfolding makes typechecking slow (see *Performance*).

## Opaque bindings: \have and \let

- **`\have` bindings never unfold; `\let` bindings do.** Use `\let` for data, `\have` for proofs.

  ```arend
  \lemma ok (n : Nat) : n = n => \let | x => n \in (idp : x = n)
  \lemma bad (n : Nat) : n = n => \have | x => n \in (idp : x = n)
  -- Expressions are not equal / Left: x / Right: n
  ```

- Opacity also blocks implicit inference:

  ```arend
  \data Tag (n : Nat) | tag
  \func tagSuc {n : Nat} : Tag (suc n) => tag
  \func okTag (k : Nat) : Nat => \let | w => suc k | t : Tag w => tagSuc \in 0
  \func badTag (k : Nat) : Nat => \have | w => suc k | t : Tag w => tagSuc \in 0
  -- Type mismatch / Expected type: Tag w / Actual type: Tag (suc ?n)
  ```

  Never `\have`-bind a value that a downstream lemma must see through. Ways out, best first: obtain it from an existential (`\let | (inP (u, pu)) => …`), so it is a genuine variable; make it an explicit parameter of a helper lemma; or write it out at each use. A `\Sigma`-returning helper whose components each need inference from a computed term tends to fail where separate lemmas succeed.
- **The mirror image: keep a single-use `\have` whose type ascription is the only statement of what its proof is about.** The ascription pins the implicits of the lemma that proves it; inlined, they come back unsolved — often as `Cannot solve equation` lines with one atom on both sides (`v0 * h * a = v0 * v0`), read as "an implicit defaulted to the wrong atom". A `\have` that only carries a proof can be inlined.
- A compound constant repeated through a proof (a bound appearing five times) should become a **parameter of a helper lemma**, not a `\have`: inside the helper it is a genuine variable that solvers and inference see through. Pass the concrete term once at the call site, and bind its *proof* (`\have C>=0 => …`) rather than its value.

## Implicit arguments

- `{A : \Type}`; pass with `f {a}`; in patterns write `| {A}, x => …` or omit; `_` as an argument means infer, as a parameter name "don't care"; `{?}` is a goal.
- Inference works through constructors: `{n m : Nat} (p : suc n = m)` infers both; `{n : Nat} (p : n + n = 3)` cannot, since `+` is not a constructor.
- When inference fails, pinning one or two implicits usually suffices; the error rarely says which.
- **An implicit that the definition's reduction erases can never be inferred — make it explicit:**

  ```arend
  \func Pk (h k : Nat) : \Set0 \elim k
    | 0 => Nat
    | suc _ => h = h
  \func pk0 {h : Nat} : Pk h 0 => 0
  \func use : Pk 7 0 => pk0     -- Cannot infer parameter 'h' of definition 'pk0'
  ```

  `Pk 7 0` reduces to `Nat` before `h` is solved. Check which arguments survive the definition's `\elim` before choosing the implicit/explicit split.
- **An implicit that occurs only under a `\func` application is not inferable** — Arend does not invert functions (`Tag` as in *Opaque bindings: \have and \let*):

  ```arend
  \func dup (n : Nat) : Nat => n Nat.+ n
  \func gd {n : Nat} (x : Tag (dup n)) : Nat => n
  \func use : Nat => gd (tag : Tag 4)   -- Cannot infer parameter 'n' of definition 'gd'
  ```

  For a class-typed implicit (`{J : Precat}` reachable only through `J.op`), the report blames instance search instead: `Cannot infer an instance of class 'Precat' / Candidate is: …` followed by a screen of the candidate's fields. Pin it at call sites or make it explicit.
- **A lemma whose implicits precede its explicit arguments can't be passed point-free** to a slot with an implicit binder: the implicit becomes a metavariable.

  ```arend
  \lemma LL {a b : Nat} (p : a = 0) (q : a = b) : b = 0 => inv q *> p
  \func needs (f : \Pi {b : Nat} -> 0 = b -> b = 0) : Nat => 0
  \func bad : Nat => needs (LL idp)
  -- Type mismatch / Expected type: \Pi {b : Nat} -> zro = b -> b = 0 / Actual type: 0 = ?b -> ?b = 0
  \func good : Nat => needs (\lam q => LL idp q)
  ```

  Arend inserts the implicit `\lam {b}` at a lambda whose expected type is known, but never eta-expands an applied term. Likewise pass `h : \Pi (n : Nat) -> n = n` for a `\Pi {n : Nat} -> n = n` slot as `\lam {n} => h n`; `h _` fails (`Expected type: \Pi {n : Nat} -> n = n / Actual type: I -> Nat`).
- **Unification against a `\func`-defined construction picks a wrong solution instead of failing.** Matching a construction that unfolds (to tuples, lambdas, quotient maps) is higher-order; Arend commits to the first solution it builds — often the source where the target belongs — and the mismatch surfaces a step later, with two types differing in one subterm. State such lemmas with explicit components, pin the target of map-like constructions, and pin compound test objects.
- **When two readings unify, Arend picks one.** An element of `G (F j)` matched against a lemma's `{H : Functor J SetCat} {j : J}` can be read as `H := Comp G F` or `H := G, j := F j`. The errors then name two index objects (`Cannot solve equation / 1st expression: K / 2nd expression: J`) next to a solved-looking `G.Func` and unsolved `?a`. Pin the whole implicit prefix; an ascription on the argument does not help.
- **`\where` members of a parameterised `\func` use its parameters as implicit parameters without declaring them:**

  ```arend
  \func outer {n : Nat} (p : n = n) : Nat => helper idp
    \where \func helper (q : n = n) : Nat => 0
  \func fromOutside : Nat => outer.helper {3} idp
  ```

  Inside the parent's body and between members they are passed for you; from outside, pass them explicitly as above.
- **There is no tactic language in the core.** Metas are macros that expand to Arend expressions, typechecked after expansion: defined in Arend (`\meta f x => e`, pure substitution) or in Java (the standard library's `Meta` modules). For the catalogue, see **arend-prove**, *Metas*.

## Performance

- **Level metavariables defeat the comparison fast path.** A call to a level-polymorphic definition without `.{…}` instantiates its levels with metavariables, solved only at the end of the enclosing definition. Checking `P.{u} a b` against `P.{?u} a b` then cannot succeed argument by argument; if `P` is a `\func`, both sides are unfolded and compared as normal forms. This is the usual cause of a multi-second definition with a tiny body. Remedies:
  - Prop-valued notations: make them `\type`s. Projections, tuples and `transport` motives keep working, but a `\type` is coerced only at the top of an expected type (`TruncP (\Sigma …)` against `TruncP (Alias …)` is a mismatch), so keep it out of positions under `TruncP` or a `\Pi`.
  - Constructed structures: `\sfunc`, with the carrier pinned in the result type so that `.E` still computes; bridge the few proofs that need the body with `rewrite (\peval f x) proof` or `{\eval f x}`.
  - Where unfolding is unavoidable, pin `.{…}` at the hot call sites.
  - A `\func` of propositional type nobody unfolds becomes a `\lemma` (the `Function can be declared as a lemma` warning flags these).
- **Don't abbreviate a term that hypotheses or cited lemmas spell out in full.** Each comparison of a `\let`-bound name against the full spelling can fail syntactically and fall back to normalizing both sides; the same holds for an alias `\func` compared with its body's head, and for a field of a variable whose type implements it. State lemmas in the spelling their callers use.
- **Inference dominates elaboration time; pinning turns minutes into seconds:**
  - lemma calls inside a `\cowith` implementation whose arguments are the record's own fields — pass every implicit explicitly;
  - equality chains in a structure computed by a `\func` (a quotient, a presented group) — give each step a `\have` with an explicit type;
  - a failed instance search on a quotient carrier is slow before it reports `Cannot infer an instance …` — pin every operation at the first such message;
  - prove a construction over an abstract `{K : Group}` and instantiate at the end.
- Find slow definitions with `--show-times` (see **arend-formalize**, *Quick reference*). Bisect a slow definition by replacing tails of its body with `{?}`; with a daemon, unchanged definitions are cached, so each probe re-checks only the edited one.

## Syntax

- All keywords start with `\`: `\func`, `\data`, `\class`, `\record`, `\let`, `\have`, `\with`, `\elim`, `\case`, `\lam`, `\Pi`, `\Sigma`, `\new`, `\this`, `\where`, `\open`, `\import`, `\hiding`, `\using`, `\instance`, `\cowith`, `\scase`, `\sfunc`, `\lemma`, `\property`, `\field`, `\truncated`, `\coerce`, `\level`, `\eval`, `\extends`.
- Fixity: `\infix`, `\infixl`, `\infixr` with priority 1–9. Backticks change fixity in an application: ``x `op` y`` uses a prefix function infix, ``x `op y z`` postfix (`` 3 `f 1 2 `` ≡ `f 3 1 2`), qualified names included. A backticked name with no operands is rejected (`Infix notation is not allowed here`, `Postfix notation is not allowed here`); to name an operator, parenthesize it: `(Nat.div)`.
- **A leading bare infix operator is a right section, not a prefix application:**

  | Form | Meaning |
  |---|---|
  | `3 + 4` | infix application |
  | `(+) 3 4` | prefix application — parenthesize the operator |
  | `(+ e)` | right section `\lam x => x + e`; `(+ (suc 1)) 5` is `7` |
  | `+ 3 4` | error: `Expression is applied to an argument, but does not have a function type / Argument: 4 / Type: Nat / In: 3` |

  Everything after a leading operator is its right operand. Passing an implicit doesn't opt out (`+ {r} 0 1` errors, `(+ {r} f 3) 4` is a section). Field operators section the same way (`r.+ 1` ≡ `\lam x => x r.+ 1`), qualified ones too: `Monoid.* {M} f g` gives `Expression is applied to an argument, but does not have a function type / Argument: g / Type: M.E / In: f`. Write `(*) {M} f g`, or infix `f M.* g`.
- **An infix operator passed as an argument needs its parentheses**: `pmap2 (+) p q`, `foldr (+) 0 l`. For the errors when they're dropped, see **arend-error-type-mismatch**, *Stripped parentheses around an infix operator*.
- **`\Pi`, `\Sigma` or `\lam` to the right of an infix operator needs parentheses.** `P 0 <-> \Pi (k : Nat) -> P k` fails with `extraneous input '\Pi' expecting {<EOF>, '\open', '\import', …}`; write `P 0 <-> (\Pi (k : Nat) -> P k)`. The same goes for `->`-statements handed to `&&`, `||`, `<->`.
- `()` is the absurd pattern (`| fsuc (fsuc ())`, right-hand side omitted); `\as x` binds an as-pattern; `__` is the implicit-lambda slot (`__ + 1`).
- `\open M`, `\open M (f, g)`, `\open M \hiding (f)`, `\open M (f \as f')`, `\open M \using (f \as f')`. Alias a long name used more than ~3 times file-locally with `\open M \using (Long \as short)`, e.g. `\open Complex \using (iunit \as i)`.
- `\let` bindings are sequential and non-recursive.
- `\where` is a module; `f.g` reaches its members from outside.
- **`\private` inside a `\where` hides the member, with a misleading error.** For `\func parent : Nat => 0 \where { \private \func helper : Nat => 1 }`, `parent.helper` elsewhere falls back to field access on the value: `Type mismatch / Expected type: a class / Actual type: Nat / In: parent`. Drop `\private` (then it's reachable as `parent.helper`), or hoist it to a file-level `\private` definition, the usual library idiom. Siblings in the same `\where` see each other unqualified.

## Comments

- `-- …` is a line comment; `{- … -}` is a **nestable** block comment, so any `{-` inside a block opens another level. Common triggers: LaTeX in doc comments (`x^{-1}`, `\{-1, 0, 1\}`) and negative implicit arguments (`f {-2}`).
- Builds since the lexer fix report it at the opening `{-`:
  `Unclosed comment ('{-' opens a comment even inside a comment; write '{ -' to start an implicit argument with '-')`.
  Older builds, including the 1.12.0 release, are silent: the comment swallows everything up to the next matching `-}`. Definitions vanish with zero diagnostics in their file; their users report `Cannot resolve reference 'X'` for a definition on screen; other files report missing definitions; recompiling or restarting the daemon changes nothing. `arend -ss <name>` returning `No matches` for a visible definition confirms it fastest. On those builds the CLI and the IntelliJ plugin also disagree on `f {-2}`: the CLI falls back to an implicit argument when no `-}` follows, the plugin treats the rest of the file as a comment.
- Fix: break the token with a space — `x^{ -1}`, `\{ -1, 0, 1 \}`, `f { -2}`. Prefer `-- |` doc comments for one-liners. After editing doc comments, grep the sources for `{-` and `-}` and inspect every hit inside a comment; before committing, grep for `{-[0-9]`.

## "Expected type: a class" — causes

`Type mismatch / Expected type: a class / Actual type: X` means something was used as a record or class and wasn't one. Usual causes:

| What you wrote | Cause | Fix |
|---|---|---|
| `parent.helper`, with `helper` `\private` in `parent`'s `\where` | `helper` is invisible, so `.helper` is read as field access on `parent`'s value (`In: parent`) | drop `\private` or hoist (*Syntax*) |
| `M.x`, where `x` was only `\open`ed into `M`'s `\where` | `\open` doesn't re-export | qualify with the real owner (*Subtyping between records*) |
| `transport (\lam x => x.px = 0) p h` | the binder's type is unknown when `x.px` is checked (`Actual type: Pt2`, `In: x`) | `rewriteI p h`, or annotate: `\lam (x : Pt2) => …` |
| `(a + b).val` on a wrapper with `\coerce val` | the operands were coerced to the payload before `+` was resolved (`Actual type: M.E`) | drop the `\coerce` (*Coercions*) |
| `n Nat.<= n` | `Nat` is not a class (`Actual type: \Set0`, `In: Nat`) | bare `<=` with `\import Arith.Nat` |

## What comes for free

- Function extensionality is provable (paths through the interval).
- Propositional univalence (`A <-> B ⟹ A = B` for `A B : \Prop`) is provable; full univalence comes from `iso`.
- Record eta `\new R { … } ≡ r` makes record refactorings definitional; `path (\lam i => p @ i) ≡ p` likewise.

## arend-lib specifics

- **`ExUpperReal`** (reals possibly `+∞`) is **not** a `PosetSemiring`: `+` with its order is `ExUpperRealAbMonoid`, `*` is `ExUpperRealSemigroup`, separately. Lemmas needing both (`PosetSemiring.pow_<=-degree`, `pow<=1`) don't apply; prove the analogue.
  - `ExUpperRealSemigroup.ide-left {x : ExUpperReal} (x>=0 : 0 <= x) : fromRat 1 * x = x` (and `ide-right`) need the non-negativity proof; `ExUpperRealSemigroup.pow_>=0` usually supplies it: `ExUpperRealSemigroup.ide-left ExUpperRealSemigroup.pow_>=0`.
  - `ExUpperRealSemigroup.pow` is its own `\func`, not `Monoid.pow`, so `Monoid.pow_+` and friends don't apply. It reduces (`pow x (suc n) = pow x n * x`) and comes with `rat-pow`, `pow_<=`, `pow_>=0`; prove anything else yourself.
  - `series_<=` wants its bounds' `<=` to be `ExUpperRealAbMonoid.<=`; otherwise unification picks `LinearOrder.<=` and reports `Cannot infer parameter 'b' of definition 'series_<='`. Write the qualifier.
- **`RealNormed.norm`** is `abs` but has type `ExUpperReal`: `norm (fromRat r) <= ExUpperReal.fromRat c` unfolds to `join (fromRat r) (negative (fromRat r)) <= …`. Bridge to a `Rat` inequality `RatField.abs r <= c` with:
  1. `LatticeAbGroup.abs-ofPos : 0 <= x -> abs x = x`;
  2. `RealAbGroup.abs-rat : abs (Real.fromRat x) = Real.fromRat (RatField.abs x)`;
  3. `Real.<=-upper : x RealAbGroup.<= y <-> x ExUpperReal.<= y`;
  4. `rat_real_<= : a <= b <-> Real.fromRat a <= Real.fromRat b`.

  When the target is already an `ExUpperReal` bound, `norm_fromRat <=∘ ExUpperReal.<=-rat.1 …` is shorter.
- **`makeRat` doesn't reduce on `suc m` for a variable `m`.** It eliminates its denominator into two clauses:

  ```arend
  \func makeRat (nom : Int) (denom : Nat) (denom/=0 : denom /= 0) : Rat \elim denom
    | 1 => nom
    | denom => makeRat' nom denom denom/=0
  ```

  `suc m` matches neither clause definitionally, so `ratNom (ratio 1 (suc m))` doesn't reduce to `pos 1`, and `simplify`/`linarith` can't see through it. Fixes, cheapest first: rewrite with `makeRat.simp : makeRat nom denom denom/=0 = makeRat' nom denom denom/=0`; `mcases {makeRat}`; or `\elim m` / `\case \elim m`, after which the residue is usually `linarith`-soluble.
- **`rewrite zro_*-left` / `zro_*-right` over `Real` can misfire**: `zro * x` normalizes to `fromRat zro`, so the searched pattern isn't the one written (symptom: an expected type collapses to `zro < fromRat zro`). Use `transportInv` with an explicit motive: ``transportInv (`< <other side>) zro_*-left h``.

## Decision table

| Symptom | First thing to try |
|---|---|
| Goal has `f x` where `f` is defined by `\case` | redefine `f` with `\elim` (*\case, \elim, \with and termination*) |
| Termination error on obvious recursion | move the `\case` into a top-level `\elim`; first fix any unresolved reference above |
| "Cannot match on `idp`" | make one side a variable bound in the match and absent from the other side |
| Implicit not inferred from `p : f n = m` | `f` is not a constructor — pass it explicitly or restructure |
| Implicit not inferred, and the reduced goal doesn't mention it | make it explicit (*Implicit arguments*) |
| `*`, `ide`, a numeral on elements of a `\func`-computed structure misbehave | pin the structure: `(*) {X} a b`, `ide {X}` (*Instance search*) |
| Solver or `rewrite` fails on a concrete instance (`Complex`, `SetCat`) | state the step over an abstract class and instantiate (*Concrete instances compute*) |
| A `\have`-bound name doesn't unfold | use `\let`, or a helper parameter (*Opaque bindings: \have and \let*) |
| `Expected type: a class` | see *"Expected type: a class" — causes* |
| Definitions vanish after editing a doc comment | nested `{-` (*Comments*) |
| Proof term unfolds into a mess | `\func` → `\lemma` |
| Typechecking is slow | *Performance*: pin levels and implicits; `\type`, `\sfunc` |
| Need the link between a `\case` scrutinee and its value | `\case e \as x, idp : e = x \with { … }`, or `cases … arg addPath` (**arend-prove**) |
| Data type inferred in too high a universe | `\use \level` with a level proof in `\where` |
| Need to squash into `\Prop` | `\truncated \data … : \Prop` |
| Want an alias that doesn't unfold | `\type` |
| Equality, algebra or arithmetic goal | **arend-prove** |
