/-
Layer 2 of the weakened Vandiver step: the counting step.

Clean-room: written from a one-paragraph description, against Mathlib only.

A twist `h` is *exceptional* for a centre `c ∈ ℤ_ℓ` when `ℓ^(k+1)` divides
`c − h`.  If `N < ℓ^(k+1)`, each centre has at most one exceptional twist in
`[1, N]`, so `R` centres have at most `R` between them.

Proof.  If `ℓ^(k+1)` divides `c − h` and `c − h'` in `ℤ_ℓ`, it divides their
difference `h − h'`, an ordinary integer; so it divides `h − h'` in `ℤ`.
But `|h − h'| < N < ℓ^(k+1)`, so `h = h'`.
-/
import Mathlib

theorem exceptional_unique (ℓ : ℕ) [Fact ℓ.Prime] (c : PadicInt ℓ) (k N : ℕ)
    (hN : N < ℓ ^ (k + 1)) (h h' : ℤ)
    (h1 : 1 ≤ h) (h2 : h ≤ N) (h1' : 1 ≤ h') (h2' : h' ≤ N)
    (hd : (ℓ : PadicInt ℓ) ^ (k + 1) ∣ c - h)
    (hd' : (ℓ : PadicInt ℓ) ^ (k + 1) ∣ c - h') :
    h = h' := by
  -- `ℓ^(k+1)` divides `h − h'` in `ℤ_ℓ` …
  have hsub : (ℓ : PadicInt ℓ) ^ (k + 1) ∣ ((h - h' : ℤ) : PadicInt ℓ) := by
    have := dvd_sub hd' hd
    have e : (c - (h' : PadicInt ℓ)) - (c - (h : PadicInt ℓ)) = ((h - h' : ℤ) : PadicInt ℓ) := by
      push_cast; ring
    rwa [e] at this
  -- … hence in `ℤ`.
  have hint : ((ℓ : ℤ) ^ (k + 1)) ∣ h - h' := (PadicInt.pow_p_dvd_int_iff (k + 1) (h - h')).mp hsub
  -- And `|h − h'| < ℓ^(k+1)`.
  have hN' : (N : ℤ) < (ℓ : ℤ) ^ (k + 1) := by exact_mod_cast hN
  have habs : |h - h'| < (ℓ : ℤ) ^ (k + 1) := by
    rw [abs_lt]
    constructor <;> linarith
  have := Int.eq_zero_of_abs_lt_dvd hint habs
  linarith

theorem exceptional_card_le (ℓ : ℕ) [Fact ℓ.Prime] (R k N : ℕ)
    (c : Fin R → PadicInt ℓ) (hN : N < ℓ ^ (k + 1)) :
    {h : ℤ | 1 ≤ h ∧ h ≤ N ∧
      ∃ i, (ℓ : PadicInt ℓ) ^ (k + 1) ∣ c i - h}.ncard ≤ R := by
  -- Send each exceptional twist to a centre that witnesses it.
  let S : Set ℤ := {h : ℤ | 1 ≤ h ∧ h ≤ N ∧ ∃ i, (ℓ : PadicInt ℓ) ^ (k + 1) ∣ c i - h}
  let f : S → Fin R := fun h => h.2.2.2.choose
  have hf : ∀ h : S, (ℓ : PadicInt ℓ) ^ (k + 1) ∣ c (f h) - (h : ℤ) := fun h => h.2.2.2.choose_spec
  -- Two twists with the same centre are equal.
  have hinj : Function.Injective f := by
    intro h h' hff
    apply Subtype.ext
    refine exceptional_unique ℓ (c (f h)) k N hN h h' h.2.1 h.2.2.1 h'.2.1 h'.2.2.1 (hf h) ?_
    rw [hff]
    exact hf h'
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_fin] at hcard
  rwa [Nat.card_coe_set_eq] at hcard

/-!
### Centres in an extension of `ℚ_ℓ`

The same counting step when the centre `s` lies in any ultrametric normed
field `K` over `ℚ_ℓ` (for instance a finite extension, where the eigenvalues
of an operator on a `ℤ_ℓ`-module live).  Divisibility by `ℓ^(k+1)` makes no
sense in `K`, so closeness is measured by the norm: `‖s − h‖ < ℓ^(−k)`.

For `K = ℚ_ℓ` and `s ∈ ℤ_ℓ` this is the condition `ℓ^(k+1) ∣ s − h` used above,
because `ℓ`-adic norms only take the values `ℓ^n`; `exceptional_unique'` below
re-derives the `ℤ_ℓ` statement from the general one.  In a ramified `K` the
norm takes more values, and `< ℓ^(−k)` is the weaker hypothesis, so this is
the stronger theorem.

Proof.  By the ultrametric inequality `‖h − h'‖ < ℓ^(−k)` in `K`.  The norm of
`K` restricts to the `ℓ`-adic norm on `ℚ_ℓ`, so `‖h − h'‖_ℓ < ℓ^(−k)`, that is
`≤ ℓ^(−(k+1))`, that is `ℓ^(k+1) ∣ h − h'` in `ℤ`.  Conclude as before.
-/

theorem exceptional_unique_field (ℓ : ℕ) [Fact ℓ.Prime]
    {K : Type*} [NormedField K] [NormedAlgebra ℚ_[ℓ] K] [IsUltrametricDist K]
    (s : K) (k N : ℕ) (hN : N < ℓ ^ (k + 1)) (h h' : ℤ)
    (h1 : 1 ≤ h) (h2 : h ≤ N) (h1' : 1 ≤ h') (h2' : h' ≤ N)
    (hd : ‖s - (h : K)‖ < (ℓ : ℝ) ^ (-(k : ℤ)))
    (hd' : ‖s - (h' : K)‖ < (ℓ : ℝ) ^ (-(k : ℤ))) :
    h = h' := by
  -- `h − h'` is small in `K`, by the ultrametric inequality …
  have hK : ‖((h - h' : ℤ) : K)‖ < (ℓ : ℝ) ^ (-(k : ℤ)) := by
    have e : ((h - h' : ℤ) : K) = (s - (h' : K)) + -(s - (h : K)) := by
      push_cast; ring
    rw [e]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hd' (by rwa [norm_neg]))
  -- … hence small in `ℚ_ℓ`, since the norm of `K` extends the `ℓ`-adic norm …
  have hQ : ‖((h - h' : ℤ) : ℚ_[ℓ])‖ < (ℓ : ℝ) ^ (-(k : ℤ)) := by
    rwa [← norm_algebraMap' K, map_intCast]
  -- … hence divisible by `ℓ^(k+1)` in `ℤ`, since `ℓ`-adic norms are powers of `ℓ`.
  have hle : ‖((h - h' : ℤ) : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
    have := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one _ _).mp hQ
    have e : -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [e] at this
  have hint : ((ℓ : ℤ) ^ (k + 1)) ∣ h - h' := (Padic.norm_int_le_pow_iff_dvd _ _).mp hle
  have hN' : (N : ℤ) < (ℓ : ℤ) ^ (k + 1) := by exact_mod_cast hN
  have habs : |h - h'| < (ℓ : ℤ) ^ (k + 1) := by
    rw [abs_lt]
    constructor <;> linarith
  have := Int.eq_zero_of_abs_lt_dvd hint habs
  linarith

theorem exceptional_card_le_field (ℓ : ℕ) [Fact ℓ.Prime]
    {K : Type*} [NormedField K] [NormedAlgebra ℚ_[ℓ] K] [IsUltrametricDist K]
    (R k N : ℕ) (s : Fin R → K) (hN : N < ℓ ^ (k + 1)) :
    {h : ℤ | 1 ≤ h ∧ h ≤ N ∧
      ∃ i, ‖s i - (h : K)‖ < (ℓ : ℝ) ^ (-(k : ℤ))}.ncard ≤ R := by
  let S : Set ℤ := {h : ℤ | 1 ≤ h ∧ h ≤ N ∧ ∃ i, ‖s i - (h : K)‖ < (ℓ : ℝ) ^ (-(k : ℤ))}
  let f : S → Fin R := fun h => h.2.2.2.choose
  have hf : ∀ h : S, ‖s (f h) - ((h : ℤ) : K)‖ < (ℓ : ℝ) ^ (-(k : ℤ)) :=
    fun h => h.2.2.2.choose_spec
  have hinj : Function.Injective f := by
    intro h h' hff
    apply Subtype.ext
    refine exceptional_unique_field ℓ (s (f h)) k N hN h h' h.2.1 h.2.2.1 h'.2.1 h'.2.2.1 (hf h) ?_
    rw [hff]
    exact hf h'
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_fin] at hcard
  rwa [Nat.card_coe_set_eq] at hcard

/-- The `ℤ_ℓ` statement `exceptional_unique`, re-derived from the field
version with `K = ℚ_ℓ`.  This checks that the field version really is a
generalization. -/
theorem exceptional_unique' (ℓ : ℕ) [Fact ℓ.Prime] (c : PadicInt ℓ) (k N : ℕ)
    (hN : N < ℓ ^ (k + 1)) (h h' : ℤ)
    (h1 : 1 ≤ h) (h2 : h ≤ N) (h1' : 1 ≤ h') (h2' : h' ≤ N)
    (hd : (ℓ : PadicInt ℓ) ^ (k + 1) ∣ c - h)
    (hd' : (ℓ : PadicInt ℓ) ^ (k + 1) ∣ c - h') :
    h = h' := by
  -- Divisibility by `ℓ^(k+1)` in `ℤ_ℓ` gives norm `< ℓ^(−k)` in `ℚ_ℓ`.
  have key : ∀ z : ℤ, (ℓ : PadicInt ℓ) ^ (k + 1) ∣ c - z →
      ‖(c : ℚ_[ℓ]) - (z : ℚ_[ℓ])‖ < (ℓ : ℝ) ^ (-(k : ℤ)) := by
    intro z hz
    have h3 : ‖c - (z : PadicInt ℓ)‖ ≤ (ℓ : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr (Ideal.mem_span_singleton.mpr hz)
    have h4 : ‖(c : ℚ_[ℓ]) - (z : ℚ_[ℓ])‖ = ‖c - (z : PadicInt ℓ)‖ := by
      rw [PadicInt.norm_def]; push_cast; rfl
    rw [h4]
    refine lt_of_le_of_lt h3 ?_
    have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    apply zpow_lt_zpow_right₀ hℓ
    push_cast
    linarith
  exact exceptional_unique_field ℓ (c : ℚ_[ℓ]) k N hN h h' h1 h2 h1' h2' (key h hd) (key h' hd')
