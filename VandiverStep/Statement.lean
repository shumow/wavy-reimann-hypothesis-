/-
The "weakened Vandiver" step of the claimed proof of the Riemann hypothesis
(Alpöge with Claude, announced 20 November 2026), restated from scratch.

This file is a clean-room STATEMENT.  It imports only Mathlib, proves nothing
of substance, and shares no code with the published archive.  The archive's
version is `UpperTheory.Top.VVle` / `UpperTheory.Top.VWin` in
`Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean`.

Plain mathematics.  Let `E` be a number field, `ℓ` a prime, `e ≥ 1`.  Put

  Ш(E, ℓ, e) = ker( H¹(𝒪_E[1/ℓ], ℚ_ℓ/ℤ_ℓ(−e)) → ∏_{w ∣ ℓ} H¹(E_w, ℚ_ℓ/ℤ_ℓ(−e)) ).

`ShaBound E t B` says that every Ш(E, ℓ, e) with `0 < e < t` is finite and

  ∑_ℓ  log ℓ · ∑_{0 < e < t}  length_{ℤ_ℓ} Ш(E, ℓ, e)   ≤   B,

that is, `∏_ℓ ∏_{0<e<t} #Ш(E, ℓ, e) ≤ exp B`.

Vandiver's conjecture for `E = ℚ(ζ_ℓ)` is a statement that certain such groups
VANISH.  The step replaces "vanish" by "are not too big in total".
-/
import Mathlib

noncomputable section

namespace VandiverStep

open NumberField IsDedekindDomain
open scoped Pointwise

/-! ### Coefficients: `ℚ_ℓ / ℤ_ℓ` -/

section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `ℤ_ℓ` inside `ℚ_ℓ`, as a `ℤ_ℓ`-submodule. -/
abbrev integers : Submodule ℤ_[ℓ] ℚ_[ℓ] := LinearMap.range (Algebra.linearMap ℤ_[ℓ] ℚ_[ℓ])

/-- The divisible group `ℚ_ℓ / ℤ_ℓ`, a `ℤ_ℓ`-module.  It is given no topology:
continuity of cochains is expressed as local constancy. -/
abbrev QZ : Type := ℚ_[ℓ] ⧸ integers ℓ

end Coefficients

/-! ### Continuous `H¹` with coefficients `ℚ_ℓ/ℤ_ℓ` twisted by a character

`G` acts on `ℚ_ℓ/ℤ_ℓ` through a character `ψ : G →* ℤ_ℓˣ`. -/

section Cohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {G : Type*} [Group G] [TopologicalSpace G]

/-- Continuous 1-cocycles: locally constant `f : G → ℚ_ℓ/ℤ_ℓ` with
`f (g h) = f g + ψ(g) • f h`. -/
def cocycles (ψ : G →* ℤ_[ℓ]ˣ) : Submodule ℤ_[ℓ] (G → QZ ℓ) where
  carrier := {f | IsLocallyConstant f ∧ ∀ g h, f (g * h) = f g + (ψ g : ℤ_[ℓ]) • f h}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ _ => by simp⟩
  add_mem' := by
    rintro f f' ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨hf.add hg, fun g h => ?_⟩
    simp only [Pi.add_apply, hf', hg', smul_add]
    abel
  smul_mem' := by
    rintro c f ⟨hf, hf'⟩
    refine ⟨hf.comp (c • ·), fun g h => ?_⟩
    simp only [Pi.smul_apply, hf', smul_add, smul_comm c]

/-- `f` is a coboundary on the subgroup `H`: there is one `m` with
`f h = ψ(h) • m − m` for all `h ∈ H`.  For a cocycle `f` this says that the
restriction of its class to `H¹(H, ℚ_ℓ/ℤ_ℓ(ψ))` is zero. -/
def TrivialOn (ψ : G →* ℤ_[ℓ]ˣ) (H : Subgroup G) (f : G → QZ ℓ) : Prop :=
  ∃ m : QZ ℓ, ∀ h ∈ H, f h = (ψ h : ℤ_[ℓ]) • m - m

/-- Coboundaries on all of `G`. -/
def coboundaries (ψ : G →* ℤ_[ℓ]ˣ) : Submodule ℤ_[ℓ] (G → QZ ℓ) where
  carrier := {f | TrivialOn ψ ⊤ f}
  zero_mem' := ⟨0, fun _ _ => by simp⟩
  add_mem' := by
    rintro f f' ⟨m, hm⟩ ⟨m', hm'⟩
    refine ⟨m + m', fun h hh => ?_⟩
    simp only [Pi.add_apply, hm h hh, hm' h hh, smul_add]
    abel
  smul_mem' := by
    rintro c f ⟨m, hm⟩
    refine ⟨c • m, fun h hh => ?_⟩
    simp only [Pi.smul_apply, hm h hh, smul_sub, smul_comm c]

end Cohomology

/-! ### The Galois side -/

section Galois

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

/-- A place `w` of `Ω` (a valuation subring) lies over the prime `v` of `E`. -/
def LiesOver (w : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x : 𝓞 E, w.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ v.asIdeal

/-- `w` lies over a prime of `E` dividing `ℓ`. -/
def Above (ℓ : ℕ) (w : ValuationSubring Ω) : Prop :=
  ∃ v : HeightOneSpectrum (𝓞 E), LiesOver E Ω w v ∧ (ℓ : 𝓞 E) ∈ v.asIdeal

/-- `w` lies over a prime of `E` not dividing `ℓ`. -/
def Away (ℓ : ℕ) (w : ValuationSubring Ω) : Prop :=
  ∃ v : HeightOneSpectrum (𝓞 E), LiesOver E Ω w v ∧ (ℓ : 𝓞 E) ∉ v.asIdeal

variable {Ω} in
/-- The inertia group of `w` in `Gal(Ω/E)`: elements of the decomposition group
acting trivially on the residue field. -/
def inertia (w : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[E] Ω) where
  carrier := {σ | σ ∈ w.decompositionSubgroup E ∧
    ∀ x, w.valuation x ≤ 1 → w.valuation (σ x - x) < 1}
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨hσ, hσ'⟩ ⟨hτ, hτ'⟩
    refine ⟨mul_mem hσ hτ, fun x hx => ?_⟩
    have hτx : w.valuation (τ x) ≤ 1 := by
      have := hτ' x hx
      have h2 : τ x = (τ x - x) + x := by ring
      rw [h2]
      exact (w.valuation.map_add _ _).trans (max_le this.le hx)
    have e : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
      simp [AlgEquiv.mul_apply]
    rw [e]
    exact Valuation.map_add_lt _ (hσ' _ hτx) (hτ' x hx)
  inv_mem' := by
    rintro σ ⟨hσ, hσ'⟩
    refine ⟨inv_mem hσ, fun x hx => ?_⟩
    have hmem : (σ⁻¹ : Ω ≃ₐ[E] Ω) x ∈ w := by
      have h1 : (σ⁻¹ : Ω ≃ₐ[E] Ω) ∈ w.decompositionSubgroup E := inv_mem hσ
      have h2 : x ∈ w := (w.valuation_le_one_iff x).mp hx
      have h3 := congrArg (fun A : ValuationSubring Ω => (σ⁻¹ : Ω ≃ₐ[E] Ω) x ∈ A)
        (MulAction.mem_stabilizer_iff.mp h1)
      exact h3.mp ⟨x, h2, rfl⟩
    have hy : w.valuation ((σ⁻¹ : Ω ≃ₐ[E] Ω) x) ≤ 1 := (w.valuation_le_one_iff _).mpr hmem
    have hx' : σ ((σ⁻¹ : Ω ≃ₐ[E] Ω) x) = x := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    have e : (σ⁻¹ : Ω ≃ₐ[E] Ω) x - x = -(σ ((σ⁻¹ : Ω ≃ₐ[E] Ω) x) - (σ⁻¹ : Ω ≃ₐ[E] Ω) x) := by
      rw [hx']; ring
    rw [e, Valuation.map_neg]
    exact hσ' _ hy

/-- The `ℓ`-adic cyclotomic character of `Gal(Ω/E)`. -/
def cyclo (ℓ : ℕ) [Fact ℓ.Prime] : (Ω ≃ₐ[E] Ω) →* ℤ_[ℓ]ˣ :=
  (cyclotomicCharacter Ω ℓ).comp (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω)

/-- The character through which `Gal(Ω/E)` acts on `ℚ_ℓ/ℤ_ℓ(−e)`. -/
def twist (ℓ : ℕ) [Fact ℓ.Prime] (e : ℤ) : (Ω ≃ₐ[E] Ω) →* ℤ_[ℓ]ˣ := (cyclo E Ω ℓ) ^ (-e)

variable (ℓ : ℕ) [Fact ℓ.Prime] (e : ℤ)

/-- Cocycles representing classes in `Ш(E, ℓ, e)`:
continuous cocycles `Gal(Ω/E) → ℚ_ℓ/ℤ_ℓ(−e)` (Krull topology) that are

* trivial on the inertia group of every place not above `ℓ`
  (so the class comes from `𝒪_E[1/ℓ]`), and
* trivial on the decomposition group of every place above `ℓ`
  (so the class is locally trivial at `ℓ`). -/
def shaCocycles : Submodule ℤ_[ℓ] ((Ω ≃ₐ[E] Ω) → QZ ℓ) where
  carrier := {f | f ∈ cocycles (twist E Ω ℓ e) ∧
    (∀ w, Away E Ω ℓ w → TrivialOn (twist E Ω ℓ e) (inertia E w) f) ∧
    (∀ w, Above E Ω ℓ w → TrivialOn (twist E Ω ℓ e) (w.decompositionSubgroup E) f)}
  zero_mem' := ⟨zero_mem _, fun _ _ => ⟨0, fun _ _ => by simp⟩, fun _ _ => ⟨0, fun _ _ => by simp⟩⟩
  add_mem' := by
    rintro f f' ⟨hf, h1, h2⟩ ⟨hf', h1', h2'⟩
    refine ⟨add_mem hf hf', fun w hw => ?_, fun w hw => ?_⟩
    · obtain ⟨m, hm⟩ := h1 w hw
      obtain ⟨m', hm'⟩ := h1' w hw
      exact ⟨m + m', fun h hh => by simp only [Pi.add_apply, hm h hh, hm' h hh, smul_add]; abel⟩
    · obtain ⟨m, hm⟩ := h2 w hw
      obtain ⟨m', hm'⟩ := h2' w hw
      exact ⟨m + m', fun h hh => by simp only [Pi.add_apply, hm h hh, hm' h hh, smul_add]; abel⟩
  smul_mem' := by
    rintro c f ⟨hf, h1, h2⟩
    refine ⟨Submodule.smul_mem _ c hf, fun w hw => ?_, fun w hw => ?_⟩
    · obtain ⟨m, hm⟩ := h1 w hw
      exact ⟨c • m, fun h hh => by simp only [Pi.smul_apply, hm h hh, smul_sub, smul_comm c]⟩
    · obtain ⟨m, hm⟩ := h2 w hw
      exact ⟨c • m, fun h hh => by simp only [Pi.smul_apply, hm h hh, smul_sub, smul_comm c]⟩

/-- `Ш(E, ℓ, e)`: the cocycles above modulo coboundaries. -/
abbrev Sha : Type :=
  shaCocycles E Ω ℓ e ⧸ (coboundaries (twist E Ω ℓ e)).comap (shaCocycles E Ω ℓ e).subtype

/-- The length of `Ш(E, ℓ, e)` as a `ℤ_ℓ`-module; `ℓ ^ shaLength` is its order
when finite. -/
def shaLength : ℕ∞ := Module.length ℤ_[ℓ] (Sha E Ω ℓ e)

end Galois

/-! ### The step -/

/-- **The weakened Vandiver statement for one field.**
All `Ш(E, ℓ, e)` with `0 < e < t` are finite, and
`∑_ℓ log ℓ · ∑_{0<e<t} length Ш(E, ℓ, e) ≤ B`. -/
def ShaBound (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ (ℓ : ℕ) [Fact ℓ.Prime] (e : ℕ), 0 < e → e < t → shaLength E Ω ℓ e ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes,
      ∑ ℓ ∈ S, Real.log (ℓ : ℕ) *
        ∑ e ∈ Finset.Ico 1 t,
          ((haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩; shaLength E Ω ℓ e).toNat : ℝ) ≤ B

/-! ### The family of fields the proof needs it for

Fix a primitive Dirichlet character `χ` of conductor `M`.  The fields are
subfields of `ℚ(ζ_N)` cut out by congruence conditions. -/

/-- `E` is the subfield of some `ℚ(ζ_N)` (with `2^(k+2)`, `M`, `q`, `d` all
dividing `N`) fixed by exactly those `ζ ↦ ζ^a` with
`a ≡ ±1 mod 2^(k+2)`, `χ(a) = 1`, `(a/q) = 1` and `(a/d) = 1`. -/
def IsFieldFor {M : ℕ} (χ : DirichletCharacter ℂ M) (k q d : ℕ)
    (E : Type) [Field E] [NumberField E] : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ),
    2 ^ (k + 2) ∣ N ∧ M ∣ N ∧ q ∣ N ∧ d ∣ N ∧ IsPrimitiveRoot ζ N ∧
    ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : E, τ (j x) = j x) ↔
        (a ≡ 1 [MOD 2 ^ (k + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (k + 2)]) ∧ χ (a : ZMod M) = 1 ∧
          jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1)

/-- The size conditions on the auxiliary primes `q`, `d` at scale `Y`. -/
structure PrimePair (ε Y : ℝ) (q d : ℕ) : Prop where
  q_prime : q.Prime
  q_mod : q % 8 = 3
  q_lo : Y ^ (ε / 5) / 2 < Real.log q
  q_up : Real.log q ≤ Y ^ (ε / 5)
  d_prime : d.Prime
  d_mod : d % 16 = 7
  d_lo : Y ^ (ε / 5) * Real.log Y ^ 2 / 2 < Real.log d
  d_up : Real.log d ≤ Y ^ (ε / 5) * Real.log Y ^ 2
  q_dvd : q ∣ d + 1
  smooth : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ Y ^ (ε / 5) → p ∣ d + 1

/-- **The step as the proof uses it.**
For every primitive `χ`, every small `ε`, and every choice of `2`-power level
`2^k(x) ≈ x^(2+8ε)`: for all large `X` and all admissible prime pairs there is
a window `[Y, Y²] ⊆ [X^(1/J), X]` on which every field `E` attached to
`(χ, k(x), q, d)` satisfies

  `ShaBound E ⌊x^401⌋ (√(exp (x^ε)))`. -/
def WeakVandiver : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M), χ.IsPrimitive →
  ∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
  ∀ k : ℝ → ℕ, (∀ x ≥ (1 : ℝ), x ^ (2 + 8 * ε) ≤ (2 : ℝ) ^ k x ∧ (2 : ℝ) ^ k x ≤ 2 * x ^ (2 + 8 * ε)) →
    ∃ J : ℝ, 1 ≤ J ∧ ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ q d : ℕ, PrimePair ε (X ^ (1 / J)) q d →
      ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) →
        ∀ (E : Type) [Field E] [NumberField E], IsFieldFor χ (k x) q d E →
          ShaBound E ⌊x ^ (401 : ℝ)⌋₊ (Real.sqrt (Real.exp (x ^ ε)))

end VandiverStep
