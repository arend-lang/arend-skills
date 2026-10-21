---
name: arend-formalize
description: Procedural workflow for turning an informal mathematical statement into a typechecking Arend definition/lemma, and the CLI tooling around it — the daemon, binary caches and their recovery, and the lookup flags `-ss`/`-ps`/`-fu`/`-ch`/`-sc`. Use when the user gives an informal claim and asks for a formalization, when starting a new .ard file from a math text, when looking something up in a library, or when the CLI reports errors that look like stale state. Covers what to read first, which CLI tools to reach for, the order of operations from "I have an idea" to "only GOAL errors remain", and the finish checklist.
user-invocable: true
---

# Arend formalization workflow

This skill takes you from an informal claim to a typechecking Arend statement. In practice the phases overlap, but don't start writing `.ard` before phase 1 is done.

For language-level surprises while writing the statement, see **arend-quirks**. For closing goals once the statement compiles, see **arend-prove**.

---

## 0. Tooling: daemon, caches, where to run

**Run every command from inside the library directory**, the one holding `arend.yaml`, or name the library as the first positional (`arend arend-lib -ss Monoid`). Otherwise the command has no library and prints `Nothing to load` … `[ERROR] No libraries to search.`

### The daemon

The daemon exists only in builds whose `arend --help` lists `-d`; it is not in the 1.12.0 release. Without it, every call pays for JVM startup and a full library load, which dominates the edit loop. The daemon keeps a warm server instead:

```bash
arend -d --serialize        # once per session, in the library directory (./arend.yaml when no LIBRARY is given)
arend . <Module>[:<def>]    # every later call in that library is routed to the daemon automatically
```

Starting the daemon resolves the libraries and typechecks nothing, so the first typecheck after it pays for the library.

| Command | Effect |
|---|---|
| `arend -d` | start a daemon holding the given libraries |
| `arend --daemon-ping` | `IDLE` or `BUSY`; an error if no daemon serves the library |
| `arend --daemon-status` | the daemon's state, including the locked flags in force |
| `arend --daemon-refresh` | resolve the libraries again, typechecking nothing. Call it after creating, deleting or renaming a module file, before a query or a typecheck that should see the change |
| `arend --daemon-stop` | stop it |
| `arend … --no-daemon` | run this one call in-process |

**Locked flags.** On a call served by the daemon, `-L -s -e -m -c -r --serialize` are warned about and ignored. The daemon's own values apply, which are the ones given to `-d`. Inside a served command, `-i` and the `--daemon-*` flags are rejected outright. Two consequences:
- `arend -r <Module>` against a live daemon recompiles nothing. Write `--no-daemon -r`, or stop the daemon first. Otherwise you will conclude "the recompile didn't fix it" from a run that never recompiled.
- A daemon started without `--serialize` never writes an `.arc` file, whatever the served calls pass. `--daemon-status` shows which flags are in force.

### Binary caches (`.arc`)

| | Behaviour |
|---|---|
| **Loading** existing `.arc` | On by default. `-r` / `--recompile` skips it for one run (not on a served call). |
| **Writing** `.arc` after a typecheck | Off by default. `--serialize` turns it on; there is no `--no-serialize`. On a served call, the daemon's value applies. |

### Stale caches and a poisoned daemon

These symptoms mean the state is stale, not the sources. They are typical after a class-hierarchy refactor:
- errors on definitions you never touched, which vanish under `-r`;
- type mismatches that print the same type twice under two names (`Rat` vs `Arith.Rat.Rat`);
- a Java stack trace out of the (de)serializer instead of a typecheck diagnostic;
- `arend` hangs, comes back with empty or suspiciously short output, or reports something that disagrees with what's on disk.

Recover with **`arend --no-daemon -r --serialize <Module>`**. All three parts matter:
- `--no-daemon`, because a served `-r` is ignored;
- `-r`, to skip loading the caches;
- `--serialize`, so that the clean build replaces them. Without it the clean build writes nothing, and the next run reads the same bad `.arc`.

For a one-off second opinion, leave `--serialize` off.

If the clean run is fine but the served one isn't, restart the daemon: `arend --daemon-stop && arend -d --serialize`. The same goes for a daemon that denies a definition plainly present in the sources, which can happen after a transient resolution error such as a duplicate name or a half-saved file. `-r` cannot fix this inside the daemon, and `--daemon-refresh` is not reliable here.

**On a Java exception (a stack trace, not a typecheck error), snapshot before recovering.** The `.arc` files are the only evidence of the serialization bug, and recompiling destroys them. First zip the library tree (sources and `bin/*.arc`) to an archive outside it, `zip -qr /tmp/<lib>-crash-$(date +%Y%m%d-%H%M%S).zip <library-dir>`, and tell the user the path. Only then recover. The exception to this is a parser exception right after a syntax error: it is fallout of that error, so fix the syntax instead (see **arend-error-extraneous-input**).

**The symbol index lags for a brand-new module.** `-ss`, `-fu` and `-ch` are served from a per-library on-disk index that re-parses only changed files, so a module you just created can be missing for a round. A `No matches` on something you just wrote is an index artefact, not a broken definition. Typecheck the module (with a daemon, `--daemon-refresh` first), then query again.

---

## 1. Orient: look things up before writing

Goal: find out whether the prerequisites exist, whether someone has already done this, and which names and classes to reuse. The retrieval flags query the loaded library without typechecking it. Go from cheap to expensive:

1. **`-ss <name>`: name lookup.** It is fast, served from the index, and prints each match's location, qualified name, kind and **one-line signature**, which is often the whole answer. Use it whenever you can guess any part of the name. It gets more useful as you learn the naming conventions (`+-comm`, `*-assoc`, `ide-left`).
2. **`-ss <Owner>.<name>`: long-name query.** A dotted pattern narrows the search to one module's or class's members: `-ss 'Monoid.*-comm'`.
3. **`-ps "<shape>"`: lookup by signature shape**, when you know the type but not the name: `arend -ps "_ + _ = _ + _"`. It is slow (~20 s), but **run it before stating any helper lemma**. A `No matches` is as valuable as a hit, because it tells you the helper doesn't exist. See `-ps --help` for the grammar.
4. **`-ch <class>` and `-fu <name>`: structure.**
   - `-ch` prints the super- and subclass trees with their `\new` and `\instance` sites. Use it to decide which class to parameterize over, and whether to extend a class or introduce a new one.
   - `-fu` lists every usage of a definition. It accepts a bare short name, a partial qualifier (`Monoid.pow`) or `MODULE:DEF`; an ambiguous name prints the candidates (`'pow' is ambiguous. Use one of: …`). Use it:
     - to learn a definition's purpose from its callers;
     - to get `No usages.` before deleting or refactoring;
     - as an existence probe: run `-fu` on a constant that *must* occur in the lemma you're looking for. If no usage site has the right shape, the lemma doesn't exist under any name.
5. **`-sc <referable>`: the scope at that referable's position.** Use it for "why isn't X visible here?" and "which of two same-named X is visible?". It accepts an optional `-ss`-style filter.
6. **Sources last.** Open a file only after the flags have told you which module to open. Read the signature line and skip the body; don't grep library sources to *find* something.
   - **Exception: before extending a module**, read the bodies of the three or four nearest definitions and note *how* they are proved: which summation API, which representation, which helper family. No name you can guess tells you that, and picking the wrong idiom costs an order of magnitude in proof length that no later cleanup recovers.

The tools combine: `-ss` finds candidates, `-ch` gives their structural context, `-fu` shows how to use them, and `-ps` finds them when you only know the shape.

**Then decide: postpone, reject, or proceed.** If a prerequisite is missing, don't formalize the goal on a foundation that doesn't exist yet. Either add the prerequisite first or report what's needed. If the prerequisites are there, proceed with a list of the signatures you intend to use.

### `-ss` grammar

`arend -ss --help` prints the authoritative grammar, so run it rather than trusting this table. Note that `arend -ss help`, without dashes, *searches for the name* "help".

| Pattern | Meaning |
|---|---|
| `Foo` | substring of the short name; characters are literal (`*-comm`, `^-1`, `<*`, `\|\|` work as typed) |
| `glob:Foo` | whole-name match: `*` = any run, `?` = one char, `\*` / `\?` for literals; with no wildcard it is an **exact** name |
| `re:<regex>` | Java regex, unanchored, case-sensitive as typed |
| `hb:<chars>` | humpback: word starts / prefixes (`hb:PAM` → `PosetAddMonoid`, `hb:isP` → `isProp`) |
| `A.B.C` | long name: earlier segments match enclosing module/namespace segments in order; the last is the short name |

- **Smart case** applies in every mode but `re:`: a lowercase letter matches either case, an uppercase letter only uppercase. So `monoid` finds `Monoid`, but `Monoid` skips `monoid`.
- **OR:** several patterns are OR'd, and whitespace inside one argument also separates them. `-ss "A B"` ≡ `-ss A -ss B`.
- **Options**, each a separate argument:
  - `limit=N` (0 = unlimited, default 200);
  - `kind=k,…` from `func sfunc lemma type axiom instance coclause coerce level data cons class record field meta`;
  - `self`, to search only the requested libraries and skip dependencies.

| Want | Wrong | Right |
|---|---|---|
| Names containing both `pow` and `<=` | `-ss "pow.*<="` (dotted → a long-name query, silent `No matches`) | `-ss "glob:*pow*<=*"`, or filter the output |
| Exact short name | `-ss eq:pmap` (removed; errors with a fix-it) | `-ss glob:pmap` |
| Either of two patterns | `-ss "A\|B"` (literal `\|`) | `-ss A -ss B`, or `-ss "A B"` |
| Wildcard | `-ss "Big*<="` (literal `*`) | `-ss "glob:Big*<="` |
| Regex | `-ss "^abs.*"` (has a dot → long-name query, `No matches`) | `-ss "re:^abs.*"` |
| Members of one class | — | `-ss "Monoid.*-comm"` |

**An unknown token is silently accepted as an extra OR'd pattern, so a filter that doesn't exist *widens* the results.** For example, `-ss BigSum 'contains=<='` returns everything bare `BigSum` returns. There is no AND filter. Each run echoes the parsed query, so **read those first lines**: they are the only sign of a misparse.

    Searching for (OR):
      literal 'BigSum'
      literal 'contains=<='

---

## 2. Draft the statement

- **Choose the class to parameterize over from `-ch`**, not by staring at the goal. Pick the smallest structure that has what the statement needs (see *Hypotheses* in the finish checklist).
- **Write the signatures with `{?}` bodies**, using the names collected in phase 1. Run `-ps` before stating each helper.
- **Choose the implicit/explicit split deliberately.** A parameter that the *reduced* statement no longer mentions cannot be inferred, so make it explicit. See **arend-quirks**, *Implicit arguments*.

---

## 3. Get to "only GOAL errors remain"

Goal: a typechecking file whose only errors are the `{?}`s, the unproven obligations. Stop there; closing them is **arend-prove**'s job.

1. **Add the `\import`s you remember needing.** Don't aim for completeness; the next steps fill the gaps.
2. **Typecheck, narrowing the scope with the positional** to keep the output readable:
   - `arend .`: the whole library;
   - `arend . <Module>`: that module and its cone;
   - `arend . <Module>:<def>`: one definition.

   Resolution and typechecking run in the same pass, so unresolved references surface as `[ERROR]` alongside genuine type errors.
3. **Clear every `Cannot resolve reference 'X'` first.** An unresolved name poisons every type downstream of it, so much of the rest disappears once it is fixed. `arend -ss X` gives the qualified name, which tells you both what to write and which module to `\import`. When several modules define the same short name, `arend -sc <referable>` shows which one is visible.
4. **Chase the remaining errors** with `-ss`/`-ps`/`-fu`/`-ch`.
5. **Capture what you learn as you go:**
   - a language-level fact (a quirk, a syntax surprise, a typing rule that bit you) → **arend-quirks**;
   - a meta-level fact (a failure mode, a non-obvious meta interaction) → **arend-prove**;
   - a misleading error, once you've found its cause → the matching **arend-error-*** skill.

   A missing library helper is not an issue: add it to the right module and move on. If the project keeps a file for tooling friction (e.g. `arend-issues.md` at the Arend repo root), append misleading diagnostics or slow CLI paths there.
6. **You're done when the only remaining errors are `GOAL`.** Type mismatches, unresolved references, universe-level and termination errors must all be gone.
7. **Re-read the final statement against the informal claim.** Variable order, implicit/explicit splits, universe levels and class parameters all change the meaning. Typechecking proves consistency, not faithfulness.

---

## 4. Finish checklist

**Run this as a pass, with the diff open, item by item. Do not run it from memory.** Every item here has been violated in work that had this skill loaded, so the failure mode is not forgetting the items but not executing them. Typechecking is the entry condition for this checklist, not a substitute for it. Groups 5 and 7 are *experiments*: make the edit, re-typecheck, and put it back only if the typechecker objects.

### 1. Goals and dead code
- `grep -n '{?}'` over every file you touched. A `{?}` must never reach a commit.
- `-fu` every new definition; `No usages.` → delete it.
- No lemma whose body is `idp`, no `pmap f idp` step, and no lemma that is a partial application of another (`f a b 0`).
- **No lemma whose body is a bare, argument-free solver call** (`equation.group`, `equation.cRing`, `linarith`, `simplify`). Writing the solver at the call site is shorter than writing the lemma's name. A solver *with* a hand-supplied bridge (`equation.group {pmap (* h) p}`) is different: the bridge is the content, so the lemma stays.

### 2. Naming: check every new name against this table

| Kind | Convention | Right | Wrong |
|---|---|---|---|
| `\Prop`/`\Type`-valued predicate or index family | Capitalised | `IsCentral`, `OnCircle` | `isCentral`, `on-circle` |
| "f commutes with g" | `f_g`, underscore | `inverse_*`, `negative_+` | `inverse-*`, `neg-plus` |
| adjectival / qualified variant | `f-adj`, hyphen | `abs-square`, `pow-positive` | — |
| coefficient | `coef` | `coef-sum` | `coeff-sum` |
| one of a directional pair | direction in the name | `cancel-left` / `cancel-right` | `cancel` |
| abbreviation | spell it out | `square` | `sq` |

Also: no proof-plan labels in names or doc comments (`L1:`, `Step 3:`, `Main theorem:`). No file-local `\alias` for a function used fewer than ~10 times; use `\open M \using (Long \as short)` instead.

### 3. Comments: delete on sight
- a comment that restates the signature in words;
- a comment documenting *your* workaround ("stated over a variable so the implicits infer");
- a proof sketch that duplicates the body, and any `-- Step N` marker inside a body;
- a comment narrating the file's organisation;
- `TODO: hoist to X` / `TODO: belongs in \where of X`: do the move now, it is two lines.

Then check that every surviving comment asserting a mathematical necessity ("needs commutativity", "not cancellative at ∞") is one you can defend. Such claims are often false.

### 4. Placement
- Exactly one consumer (`-fu`) → move it into that consumer's `\where`.
- Takes `{X : SomeClass}` and is only ever used at one `X` → make it a member of the class.
- `\where`-nested, `\private`, and needed by a sibling → drop `\private` or hoist it to file level (see **arend-quirks**, *Syntax*).
- The directory matches the subject: a real-analysis statement does not live under `Algebra/`.
- No import from a higher layer. In arend-lib, nothing under `Algebra/` imports `Analysis/` or `Topology/`; if you need a type from there, define the algebraic one locally.
- Delete every import that is no longer used.

### 5. Hypotheses: try to weaken every one
This is the check nobody performs by reflex, and it is the source of mathematically wrong signatures.
- For each explicit hypothesis: delete it and re-typecheck.
- For each class parameter: replace it by each superclass (`-ch <class>` lists them) and re-typecheck. A statement proved over a field often needs only a ring.
- `Fin n` in a statement → try `{A : FinSet}`. A statement about `Fin n` will not apply to other finite sets, and you will re-prove it by hand.
- `\Pi (y z : A) -> y * z = z * y` is almost always too strong: the statement usually needs only one element to be central (`Monoid.IsCentral`).
- An argument that is a proposition and gets `prop-pi`'d downstream → mark it `\property`.

### 6. Abstraction by repetition
- A hypothesis that appears in ≥3 signatures of the diff → name it.
- A class combination that appears in ≥3 signatures → declare the class. A one-line `\class C \extends A, B` can delete a repeated commutativity argument from every signature.
- Two definitions that differ only in a constant → generalise one and delete the other.

### 7. Redundancy
Run the compaction list in **arend-prove**, *Style › Compaction*, item by item, re-typechecking after each.

### 8. Layout
- Signature: the parameters, then `: Result` on its own line, then `=> body`. Never `… (args) :` at the end of a line.
- `\where {` on its own line, with members indented one level.
- `\have` for proofs, `\let` for values.
- `Record R`, not `Record { | R => R }`. Use `| Parent => …` to reuse a parent instance rather than re-implementing its fields.

---

## Diagnosis recipes

### "The lemma is `[GOAL]` but I didn't write `{?}` in the body"

Look upstream, not at the reported definition. A `[GOAL]` on a body you wrote in full usually means an *earlier* definition failed to typecheck, and the reference to it degraded into a hole. Re-run scoped to the whole module (`arend . <Module>`) and read the *first* `[ERROR]`: that is the real bug, and everything after it is fallout. To confirm, check the upstream definition alone with `arend . <Module>:<upstream-name>`.

### "Each module typechecks, but the whole-library run throws `IllegalArgumentException`"

This is usually `linarith` or `equation` choking on a goal where the implicit algebraic class can't be inferred. Per-module checks can skip the failing path because of caching. The exception isn't attached to a source line, so bisect by commenting out solver calls. Workaround: replace that `linarith` with an explicit lemma chain.

### "Bogus errors in modules I didn't touch" / "the daemon denies a definition I can see"

Stale caches or a poisoned daemon; see *Stale caches and a poisoned daemon* above.

### "A definition is on screen, yet it is `Cannot resolve reference` and `-ss` finds nothing"

If the index cannot see the definition, the parser never saw it either. Usually a `{-` inside an earlier comment swallowed it; see **arend-quirks**, *Comments*. (If the module itself is brand new, it may instead be index lag; see the end of section 0.)

---

## Quick reference

| Question | Command |
|---|---|
| "Does a lemma of this *shape* exist?" | `-ps "<shape>"` |
| "Is there a definition whose name matches X?" | `-ss X` (grammar: *`-ss` grammar* above) |
| "Where is this definition used?" | `-fu <name>` |
| "Which classes extend C / which instances exist?" | `-ch <class>` |
| "Why isn't X in scope here?" | `-sc <referable>` |
| "I edited; resolve + typecheck." | `arend . <Module>[:<def>]` |
| "Make the edit loop fast." | `arend -d --serialize` once per session |
| "Is a daemon up, and is it busy?" | `--daemon-ping` (`IDLE` / `BUSY`) |
| "I added, deleted or renamed a module file." | `--daemon-refresh` |
| "Errors that vanish under `-r`, a hang, bogus mismatches after a refactor." | `arend --no-daemon -r --serialize <Module>` |
| "The daemon is wedged / denies a visible definition." | `--daemon-stop`, then `-d --serialize` |
| "Which definitions are slow?" | `arend --no-daemon -r --show-times [MODULE[:DEF]]`, or `--show-sizes` for core-term sizes. A `:DEF`-scoped run checks only that definition's dependencies. Don't use the daemon here: it re-checks only definitions whose resolved AST changed, so it reports ~0 ms for the rest. To bisect, add variant definitions to a scratch copy of the library and time them all in one run. Causes and cures: **arend-quirks**, *Performance*. |
