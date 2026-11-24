# The Vandiver step: findings, 20 Nov 2026

Status report for the handoff brief "Checking the Vandiver Step in Lean".
Stages 0–2 are done, Stage 4 is a first pass, Stage 3 is blocked for the reason
given below, Stage 5 is not started.

## Stage 0: the archive

- Source read: the independent mirror `Deicyde/riemann-hypothesis` at commit
  `e50d0981`. Its notes say its first commit is the archive's `lean/` directory
  unchanged, and that the joined archive has sha256 `9631b4f0…c7fc`.
- **Not done:** I did not download the 14 parts from `alpo.ge` or check that
  hash myself. The download was blocked in this session. Everything below
  trusts the mirror to be a faithful copy.
- Pins: Lean `v4.33.1`, Mathlib `0df444a360ea` (tag `v4.33.1`). This repo uses
  the same pins.
- The source has no comments or docstrings at all, and no declaration is named
  after Vandiver. The lemma was found by walking back from `rhOfAll`.

## Stage 1: where the step is

`Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean`, namespace
`UpperTheory.Top`:

| Archive name | What it is |
|---|---|
| `VVle E t B` | the bound for one number field `E` |
| `VAt`, `VWinAt`, `VWin` | the same bound over the family of fields the proof uses |
| `HypV` (`DivinNOfHypV.lean`) | `VVle` with `B = √b`, as consumed downstream |

Underlying definitions: `Formalism/GaloisCohomology/Statement.lean` (`LData`,
`qzTw`, `Sha`, `shaLen`) and `ReciprocityTheory/GaloisValuations/` (continuous
cochains written out by hand, the group `G_S`, inertia, the cyclotomic
character). All of it is built on Mathlib; none of it is a Mathlib definition.

How it reaches RH:

```
riemannHypothesis = rhOfAll = rh_of_every allChi
allChi = UpperTheory.FinalTheorems.everyCharacter
       = every_character_of_literature_of_vWin ⟨row, recTExists, row⟩ (vwin_of_row row)
row    = UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
```

So `VWin` is one of two inputs to the final theorem, and both inputs are
derived from one statement, `Row0b`: Galois representations attached to
regular algebraic polarized cuspidal automorphic representations of `GL_a`
over CM fields, with local–global compatibility. The archive claims to prove
`Row0b` rather than assume it.

## Stage 2: our statement

`VandiverStep/Statement.lean`. It imports only Mathlib, compiles, has no
`sorry`, and depends on `propext`, `Classical.choice`, `Quot.sound` only.
It proves nothing beyond the closure properties needed to define the objects.

In plain mathematics. For a number field `E`, a prime `ℓ` and `e ≥ 1`, let

    Ш(E, ℓ, e) = ker( H¹(𝒪_E[1/ℓ], ℚ_ℓ/ℤ_ℓ(−e)) → ∏_{w | ℓ} H¹(E_w, ℚ_ℓ/ℤ_ℓ(−e)) ).

`ShaBound E t B`: every `Ш(E, ℓ, e)` with `0 < e < t` is finite, and

    ∑_ℓ log ℓ · ∑_{0<e<t} length_{ℤ_ℓ} Ш(E, ℓ, e) ≤ B,

that is, `∏_ℓ ∏_{0<e<t} #Ш(E, ℓ, e) ≤ e^B`.

`WeakVandiver`: for every primitive Dirichlet character `χ` and every
`0 < ε < 1/52`, on suitable windows of `x`, every field `E` in a specific
family of subfields of cyclotomic fields `ℚ(ζ_N)` (level `2^k ≈ x^(2+8ε)`
times `χ`'s conductor times two auxiliary primes `q`, `d` with
`log q ≈ x^(ε/5)`) satisfies

    ShaBound E ⌊x^401⌋ √(exp(x^ε)).

Differences from the archive's wording, chosen for readability. Each is a
standard equivalence, but **none is proved here**, so our statement is not yet
known to be the same proposition as `VWin`:

1. We use cocycles on the full Galois group that are trivial on inertia
   outside `ℓ`. The archive uses the quotient group `G_S`. (The archive's own
   `InfUnram` is the bridge.)
2. We ask for local triviality at every place of `Ω` above `ℓ`. The archive
   picks one place per prime. (Conjugate decomposition groups.)
3. We write continuity as local constancy instead of giving `ℚ_ℓ/ℤ_ℓ` the
   discrete topology.

Definitions the statement needs that Mathlib lacks: continuous group `H¹`
with twisted `ℚ_ℓ/ℤ_ℓ` coefficients, the inertia subgroup of a valuation
subring in an infinite Galois group, and `Ш`. All three are in the one file;
they are short.

## Stage 3: proving it ourselves — blocked, and why

The archive's proof of `VWin` (`HVCore.of_four_alt`, `vvle_of_parts`,
`vwin_of_joint`) splits `Ш` into a 2-part, a minus part and a plus part, and
uses:

- **`LemmaK`**: a bound on `#H²(𝒪_L[1/ℓ], ℤ_ℓ(e+1))` in terms of `e`, the
  degree and the discriminant. This is a bound on the `ℓ`-part of
  `K_{2e}(𝒪_L)`.
- **`CountI` … `CountV`**: five case bounds whose hypotheses are automorphy
  and Galois-representation statements (`LiteratureRankNHypothesis`,
  `HypothesesH'`, a Kato-style input, deformations for `U(3)`).
- **`ThmBc`**: the minus-part bound, of class-number-formula type.
- Poitou–Tate duality and local Tate duality, stated in
  `ReciprocityTheory/Hypotheses/GalCoh.lean`.

A clean-room proof therefore needs, at minimum: global duality for Galois
cohomology, Galois representations attached to automorphic forms on unitary
groups with local–global compatibility, and automorphy lifting. Mathlib has
none of these. This is not a step that can be re-proved independently in
weeks; it is most of the arithmetic half of the archive. The `sorry` count for
a top-down skeleton would be meaningless until those theories exist.

New claims, where an error would live:

1. The plus-part bound itself. I know of no published unconditional bound of
   this strength. (From memory, not checked against the literature.)
2. `LemmaK`. Read on 24 November: `kBound C e n D = exp((2en)^C · log 2D)`,
   so it bounds `log #H²` by a quantity exponential in a power of `e·n`. That
   is the shape of Soulé-type bounds for K-groups, not an obviously new claim.
   Not compared with the literature.
3. `Row0b` in the generality stated. Results of this kind are published, but
   the archive's exact hypotheses need comparing with them.

## Stage 4: sanity check, first pass

- **How it weakens Vandiver.** Vandiver says `ℓ ∤ h⁺(ℚ(ζ_ℓ))`, which is the
  vanishing of certain eigenspaces; in this language, certain `Ш(E, ℓ, e)`
  are zero. The step asks only that the total size over all `ℓ` and all
  `e < t` is at most `e^B`. It allows any individual group to be nonzero.
- **Is the bound plausible?** By Poitou–Tate, `Ш(E, ℓ, e)` is dual to a piece
  of `H²(𝒪_E[1/ℓ], ℤ_ℓ(e+1))`, which is the `ℓ`-part of `K_{2e}(𝒪_E)` by the
  Quillen–Lichtenbaum conjecture (now a theorem). Where the analytic formula
  applies, the sizes are governed by `ζ_E(−e)`, and summing the logarithm
  over `e < t` gives roughly `t² · [E:ℚ] · log(cond)`, about
  `x^802 · exp(x^(ε/5) log² x)`. The allowed `B = exp(x^ε / 2)` is larger
  than that. So the step asks the plus part to be no larger than the scale
  the minus part is already known to have. That is not obviously false, and
  it is far stronger than anything I know to be proved for the plus part.
  This estimate is mine and rough.
- **Not done:** Kurihara's theorem (Vandiver ⇔ `K_{4n}(ℤ) = 0`) is still
  unconfirmed against a reference, and I have not derived consequences for
  K-groups of `ℤ` from `WeakVandiver`. Alpöge's footnote expects vanishing to
  follow; from the statement alone I only see bounds, so either the footnote
  refers to a different intermediate statement or there is an argument I do
  not see.
- Nothing found that contradicts a known result.

## Stage 5: not started

Building the archive's cone for `VWin` means building most of the archive
(the mirror estimates 5–7 hours and 86 GB on a large machine). This container
has 4 cores and 15 GB of memory.

## Things a verifier should know

- Many archive names read like assumptions (`Hypotheses/`, `PublishedTheorems`,
  `OpenLiteratureStatements`, `LiteratureRankNHypothesis`). They are `Prop`
  definitions passed as arguments, and `everyCharacter` takes no arguments, so
  at the top they are all claimed discharged. The mirror's text scan finds no
  `axiom` or `sorry`. Only a kernel replay with an axiom audit settles it.
- The archive defines the same notion several times in different namespaces
  (`H1`, `Sha1`, `GS` each appear in at least two files). Any bridge lemma has
  to name which copy it uses.

---

# Update, 24 November 2026: layers 1 and 2, and the archive's window argument

## Proved here (Mathlib only, no `sorry`)

| Theorem | File | Axioms |
|---|---|---|
| `interval_lemma` | `VandiverStep/IntervalLemma.lean` | `propext`, `Classical.choice`, `Quot.sound` |
| `interval_lemma_finset` | same | same |
| `exceptional_unique` | `VandiverStep/Counting.lean` | same |
| `exceptional_card_le` | same | same |

The three drafted statements compiled unchanged. `interval_lemma_finset` is an
addition: the interval lemma restated in the archive's shape and deduced from
`interval_lemma`.

## Where the declarations are

| Name | File (under `src/`) |
|---|---|
| `UpperTheory.Top.VWinAt`, `VWin`, `VAt`, `VVle` | `Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean` |
| `Formalism.GaloisCohomology.shaLen`, `Sha`, `LData` | `Formalism/GaloisCohomology/Statement.lean` |
| `UpperTheory.V.Win.window1` | `Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Window1.lean` |
| `UpperTheory.V.Win.window`, `near1`, `exc`, `partA`, `partB`, `thmBab_of` | same directory |

## `window1` versus `interval_lemma`

Same statement, same constants. The archive takes a `Finset ℝ` of at most `R`
left endpoints and writes disjointness as "`y ≤ u ≤ 2y` and `a ≤ u` imply
`B·a ≤ u`". `interval_lemma_finset` proves exactly that shape from ours. The
proofs differ: the archive inducts on `R`, ours is a pigeonhole over `R + 1`
windows.

It is used once, in `window`, with `U = log X`, `B = Ct/η` and endpoints
`log e / Ct` for `e` in the exceptional set. A twist `e` is harmful at scale
`x` when `x^η < e ≤ x^Ct`, which is `log x ∈ [log e / Ct, log e / η)`.

## The counting step in the archive: a mismatch with ours

`near1` is the archive's version of `exceptional_unique`. Its centre `s` lies
in any ultrametric normed field `K` over `ℚ_ℓ`, and closeness is
`‖s − a‖ < ℓ^(−⌊log_ℓ Z⌋)`. Ours takes the centre in `ℤ_ℓ`. With
`k = ⌊log_ℓ Z⌋` and `N = Z` the two agree when `K = ℚ_ℓ`, but the archive's
centres (`ABound`) are allowed to live in an extension of `ℚ_ℓ`. Layer 3 will
need the more general form.

## Placeholder check

- `shaLen D e` is `Module.length ℤ_ℓ (Sha D e)`. `Sha` is `Sha1`: the
  intersection of the kernels of restriction to the decomposition groups at
  the chosen places above `ℓ`, inside continuous `H¹` of
  `G_S = Gal(Ω/E) / closure(normal closure of inertia outside S)` with
  coefficients `ℚ_ℓ/ℤ_ℓ` twisted by `χ_cyc^(−e)`. Every layer is a real
  definition down to Mathlib (`cyclotomicCharacter`, `ValuationSubring`,
  `Module.length`, the Krull topology).
- `VWinAt` unfolds to `PageN`, `WinPair`, `IsChiField`, `VVle`, all written
  out; none is `True` or a constant.
- The archive has 8 definitions of the form `… : Prop := True` (names like
  `UnusedSlot55`, `NoCondition`). None is in the files `VWinAt`'s statement
  depends on.
- `VVle` quantifies over all `LData`. If `LData` were empty the bound would be
  vacuous; the archive has `ldataExists : LDataExists`.
- Not checked: that the hypotheses of `VWinAt` (`WinPair`, `IsChiField`) are
  satisfiable. That is settled by whoever consumes `VWin`, on the other side
  of the proof.
- `FerreroWashington` and `PoitouTateDuality` are `Prop`s passed as arguments
  to `thmBab_of_lemmaK`. The archive has a hypothesis-free theorem
  `UpperTheory.V.FW.ferreroWashington : Published.FerreroWashington`, so it
  claims to prove Ferrero–Washington rather than assume it. Its statement is
  the bounded-`ℓ`-rank form: `#(Cl(K')/ℓ) ≤ ℓ^r` up the cyclotomic tower.

## How the sum over all primes is handled

The Iwasawa-and-window argument does not run over all primes. It runs over a
finite set fixed in advance:

- `ℓ = 2` (`TwoIn`, `ThmBa`), because the fields `E` climb the 2-power
  cyclotomic tower as `x` grows.
- the odd primes in `Bchi ψ`: 3 and the odd prime factors of a number
  depending only on the character (`FixedIn`, `ThmBb`).

The number of centres is `R = R0 + ∑_{ℓ ∈ B'} Rl ℓ`, and the window constant
`J = 2^(R+2)·(2·CK·Ct/ε)^R` is `window1`'s constant for that total.

Every other prime is handled without a tower, for all `ℓ` at once:

- minus eigenspace of complex conjugation: `ThmBc`, with the explicit bound
  `minusBound` (class-number-formula size);
- plus eigenspace: `ThmHV`, which takes the window above as a hypothesis and
  comes from the Galois-representation counts `CountI`–`CountV`.

`vvle_of_parts` adds the three bounds. So the outside guide's sketch (fix
`ℓ`, count centres) describes only the finitely many tower primes.

## A discrepancy to fix in the handoff brief

The brief gives the bound as `exp(x^(ε/2))`. The archive has
`Real.sqrt (Real.exp (x ^ eps))`, which is `exp(x^ε / 2)`. These differ.
