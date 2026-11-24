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
