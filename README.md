# lean-smt-hammer

A Lean 4 tactic that runs the full hammer pipeline against SMT solvers.

> Not the same project as the community's
> [LeanHammer](https://github.com/JOSHCLUNE/LeanHammer) (lean-auto + Duper). That one
> translates to TPTP / first-order logic and reconstructs entirely with Duper. This one
> translates to SMT-LIB, leans on z3 / cvc5's decision procedures for the heavy lifting,
> and only uses Duper at the very end to turn an unsat core into a real proof.

```
goal + local context
  │
  ├─(1) premise collection   scan the Environment, take every theorem as a candidate
  ├─(2) relevance filtering  MePo-style iterative expansion, rare symbols weighted higher
  ├─(3) monomorphization     instantiate polymorphic lemmas at the goal's concrete types,
  │                          filling instance arguments via synthInstance
  ├─(4) encoding + solving   translate to SMT-LIB 2, race z3 / cvc5, take the unsat core
  │
  └─(5) reconstruction       hand the core to Duper to reprove inside Lean -- partial
```

Steps 1-4 are the bulk of the work. Step 5 takes the outsourcing route: the external
solver does the *search* across tens of thousands of lemmas, and Duper (a superposition
prover running inside Lean) does the *rebuilding* over the handful in the core.

* Reconstruction succeeds: the goal is closed by a genuine proof term, and
  `#print axioms` is clean.
* Reconstruction fails: fall back to the axiom `Hammer.trustSMT : ∀ p : Prop, p`, and say
  so in the report.

```lean
theorem demo (l₁ l₂ : List Nat) : (l₁ ++ l₂).length = l₁.length + l₂.length := by hammer
-- hammer: z3 returned unsat (18ms) · premises: 96 selected → 170 monomorphized →
--   137 asserted (33 dropped)
-- premises in the unsat core:
--   · List.length_append
-- goal closed by a proof term reconstructed with Duper — a real proof, no `trustSMT`.
#print axioms demo
-- 'demo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Even when reconstruction fails the report earns its keep: it names the lemmas that suffice
to derive the goal, which you can then feed to `omega` or `simp` for a real proof.

## How much actually gets reconstructed

`HammerTest/Reconstruct.lean` measures this over 19 goals, adjudicated by `#print axioms`:

| Category | Reconstructed | Notes |
| --- | --- | --- |
| Propositional logic | 3 / 3 | Duper's home turf |
| Uninterpreted functions and equality | 3 / 3 | likewise |
| Quantifiers | 2 / 2 | likewise |
| Needs a lemma from the environment | 2 / 2 | `List.length_append` and friends |
| Integer / natural arithmetic | 2 / 9 | **the main gap** |
| **Total** | **12 / 19** | |

The reason for the gap is clear: **Duper is pure first-order equational reasoning with no
arithmetic decision procedure**. For goals like `a ≤ b → a ≤ b + 1`, `n - (n+1) = 0`, or
`n / 0 = 0`, the core often holds just one or two hypotheses while all the real work sits
in z3's linear arithmetic theory -- which Duper cannot pick up. (The two that do succeed
are special cases: `x < y → x + 1 ≤ y` has a ready-made lemma on `Int`, and `(-7)/2 = -4`
is a closed term that computes.)

The time cost is small: about 0.6 seconds across all 19 goals, roughly 30ms each. Duper
either succeeds quickly or gives up quickly.

## Installation

Needs z3 and cvc5 on `PATH` (at least one of them).

```bash
brew install z3
# cvc5 is not in homebrew; grab the release binary:
curl -sL -o cvc5.zip "$(curl -sL https://api.github.com/repos/cvc5/cvc5/releases/latest \
  | grep browser_download_url | grep 'cvc5-macOS-arm64-static.zip' | cut -d'"' -f4)"
unzip -q cvc5.zip && sudo cp cvc5-macOS-arm64-static/bin/cvc5 /usr/local/bin/
```

Then `lake build`. The first build fetches Duper and its dependencies (lean-auto,
batteries), which takes a few minutes.

The toolchain is pinned to `v4.30.0`: Duper has no `v4.31.0` tag (it jumps from v4.30.0
straight to v4.32.0), and v4.30.0 is the closest usable version.

> `lakefile.toml` sets `precompileModules = true`. Tactic code otherwise runs in the
> bytecode interpreter, an order of magnitude slower; compiling to a shared library drops
> the Lean-side cost from ~800ms to ~130ms per call. (The first call additionally spends
> ~2s scanning the environment; after that it hits an in-process cache.)

## Usage

```lean
import Hammer

example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by hammer
example : ... := by hammer (timeout := 30, premises := 256)
example : ... := by hammer (verbose := true)      -- print the SMT-LIB problem and its path
example : ... := by hammer (close := false)       -- report only, leave the goal open
```

| Option | Default | Meaning |
| --- | --- | --- |
| `premises` | 96 | Lemmas kept after relevance filtering |
| `timeout` | 10 | Wall-clock timeout per solver, in seconds |
| `instances` | 8 | Maximum instances generated per lemma during monomorphization |
| `solvers` | `"z3,cvc5"` | Backends to race, comma-separated |
| `mono` | true | Monomorphize; with it off, polymorphic lemmas are dropped entirely |
| `verbose` | false | Print the SMT-LIB problem |
| `close` | true | On failed reconstruction, close the goal with the trust axiom |
| `reconstruct` | true | Attempt proof reconstruction with Duper |
| `assumeNonempty` | false | See "Nonempty sorts" below |

## Layout

| File | Responsibility |
| --- | --- |
| `Hammer/Basic.lean` | Config, result types, the `trustSMT` axiom |
| `Hammer/Premise/Features.lean` | Premise features (constants in a statement) |
| `Hammer/Premise/Collect.lean` | Scan the Environment and local context, with caching |
| `Hammer/Premise/Select.lean` | MePo relevance filtering |
| `Hammer/Translate/Encode.lean` | `Expr` to SMT-LIB; the core of the project |
| `Hammer/Translate/Monomorphize.lean` | Goal-driven type instantiation |
| `Hammer/Translate/Problem.lean` | Assemble the problem, manage `:named` labels |
| `Hammer/Solver/Backend.lean` | Race z3 / cvc5, parse the unsat core |
| `Hammer/Translate/SMTLib.lean` | S-expression and command representation / printing |
| `Hammer/Tactic.lean` | Tactic frontend, reporting, reconstruction hook |
| `Hammer/Reconstruct.lean` | Rebuild proofs with Duper; the core library does not depend on it |

## Encoding trade-offs

CIC is far more expressive than many-sorted first-order logic, so the translation is
necessarily partial. Three principles:

1. **Translate precisely what we understand**: propositional connectives, quantifiers,
   equality, and arithmetic and comparisons over `Nat` / `Int` / `Real`.
2. **Abstract everything else into uninterpreted symbols.** Abstraction only discards
   equational information, making the problem harder rather than easier, so `unsat` stays
   trustworthy.
3. **Drop a premise that fails to translate**; only a failure on the goal aborts the call.

A few concrete decisions:

* **`Nat` maps to `Int` plus non-negativity.** Every `Nat` quantifier gets a `≥ 0` guard
  and every symbol returning `Nat` gets a non-negativity axiom.
* **Total-function semantics.** `a - b` becomes `(ite (<= b a) (- a b) 0)`, `a / 0`
  becomes `0`, `a % 0` becomes `a`. Lean's `Int` division happens to be exactly SMT-LIB's
  Euclidean `div` (measured: `(-7)/2 = -4`, `(-7)%2 = 1`), so only the zero-divisor guard
  is needed.
* **Monomorphization on the spot.** In `@f α inst a b`, the type and instance arguments
  fold into the symbol's **identity** rather than being translated as arguments:
  `@List.length Nat l` and `@List.length Int l` become two different SMT symbols. This way
  the first-order encoder never has to express polymorphism.

## Known unsoundness risks (all closed; recorded here for reference)

An encoding that turns a true statement into a contradiction would let `hammer` "prove"
false goals. `HammerTest/Soundness.lean` is the regression suite guarding that layer.

**Dependent sorts.** `Fin.pos : ∀ {n} (i : Fin n), 0 < n`. Abstracting `Fin n` into a sort
`Fin` independent of `n` turns the formula into "as long as `Fin` is nonempty, every
`n ≥ 0` satisfies `0 < n`" -- self-contradictory, so any goal at all becomes "provable".
This bug was caught by the counterexample `f a = f b`. The encoder now rejects any sort or
symbol that mentions a variable in scope of an SMT quantifier (`mentionsBound`).

**Nonempty sorts.** SMT-LIB assumes every sort is nonempty; Lean types can be empty.
`∀ x : Empty, P x` holds vacuously in Lean but becomes a real assertion in SMT. By default
we require a synthesizable `Nonempty` instance and drop the premise otherwise;
`assumeNonempty := true` buys coverage at the cost of trusting `unsat`.

The price is completeness: strict checking drops a fair number of premises (in the
counterexample tests, 95 encodable premises came down to 16).

## Not done yet

* **Reconstruction for arithmetic goals** -- the 7 gaps above. Two routes: add a Lean-side
  arithmetic tactic as a second reconstruction backend (`omega` would close most of them),
  or do it properly and rebuild proof terms from the solvers' proof logs (z3's
  `(get-proof)`, cvc5's Alethe) -- much more work, but complete coverage.
* **Higher order.** Lambda terms are currently always abstracted. TPTP THF plus
  Zipperposition would help a great deal here.
* **Induction.** SMT does not do induction, so any goal needing it is out of reach.
* **Machine-learned premise selection.** This is plain symbolic MePo; Sledgehammer's MaSh
  uses naive Bayes / kNN and does noticeably better.
* **An inverted index.** Relevance filtering currently scans the whole pool each round.
  Fast enough for core Lean's 37k theorems; Mathlib (~300k) would need a symbol index.

## License

Apache License 2.0, see [`LICENSE`](LICENSE). This is also the Lean ecosystem convention --
Mathlib, Duper, and lean-auto all use it.
