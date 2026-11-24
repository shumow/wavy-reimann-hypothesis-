/-
Layer 1 of the weakened Vandiver step: the interval lemma.

Clean-room: written from the statement alone, against Mathlib only.

Statement.  Let `B ≥ 1` and `V > 0`.  For any `R` half-open intervals
`[λ_i, B·λ_i)` there is a window `[V', 2V']` disjoint from all of them, with
`V / (2^(R+2) · B^R) ≤ V'` and `2V' ≤ V`.

Proof.  Take the `R + 1` candidate windows `W_k = [a_k, 2·a_k]` with
`a_k = V / (2·(2B)^k)`, `k = 0, …, R`.  They are spread out: `2B·a_k ≤ a_j`
for `j < k`.  If `[λ, Bλ)` meets `W_k` then `λ ≤ 2·a_k`, so every point of the
interval is `< Bλ ≤ 2B·a_k ≤ a_j`, and the interval misses `W_j`.  So each
interval meets at most one window, and `R` intervals cannot use up `R + 1`
windows.
-/
import Mathlib

theorem interval_lemma (B V : ℝ) (hB : 1 ≤ B) (hV : 0 < V)
    (R : ℕ) (lam : Fin R → ℝ) :
    ∃ V' : ℝ, V / (2 ^ (R + 2) * B ^ R) ≤ V' ∧ 2 * V' ≤ V ∧
      ∀ i, Disjoint (Set.Icc V' (2 * V')) (Set.Ico (lam i) (B * lam i)) := by
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB
  -- `c = 2B` is the ratio between consecutive candidate windows.
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * B := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by rw [hc]; linarith
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  -- The left endpoints `a k = V / (2 c^k)`.
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ k, a k = V / (2 * c ^ k) := ⟨fun k => V / (2 * c ^ k), fun _ => rfl⟩
  -- The windows are spread out: `c · a k ≤ a j` for `j < k`.
  have hstep : ∀ j k, j < k → c * a k ≤ a j := by
    intro j k hjk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hjk
    have h1 : c * a (j + m + 1) = V / (2 * c ^ j * c ^ m) := by
      rw [ha]
      field_simp
      ring
    rw [h1, ha]
    apply div_le_div_of_nonneg_left hV.le (by positivity)
    have hm : 1 ≤ c ^ m := one_le_pow₀ hc1
    nlinarith [pow_pos hc0 j]
  -- An interval that meets window `k` misses every earlier window `j < k`.
  have hmiss : ∀ i j k, j < k →
      ¬Disjoint (Set.Icc (a k) (2 * a k)) (Set.Ico (lam i) (B * lam i)) →
      Disjoint (Set.Icc (a j) (2 * a j)) (Set.Ico (lam i) (B * lam i)) := by
    intro i j k hjk hk
    rw [Set.not_disjoint_iff] at hk
    obtain ⟨t, ⟨_, ht2⟩, ⟨ht3, _⟩⟩ := hk
    rw [Set.disjoint_left]
    rintro s ⟨hs1, _⟩ ⟨_, hs4⟩
    have h1 : B * lam i ≤ B * (2 * a k) := mul_le_mul_of_nonneg_left (ht3.trans ht2) hB0.le
    have h2 := hstep j k hjk
    have h3 : B * (2 * a k) = c * a k := by rw [hc]; ring
    linarith
  -- Each candidate window satisfies the two size conditions.
  have hlow : ∀ k, k ≤ R → V / (2 ^ (R + 2) * B ^ R) ≤ a k := by
    intro k hk
    rw [ha]
    apply div_le_div_of_nonneg_left hV.le (by positivity)
    have h1 : c ^ k ≤ c ^ R := pow_le_pow_right₀ hc1 hk
    have h2 : c ^ R = 2 ^ R * B ^ R := by rw [hc, mul_pow]
    have h3 : (0 : ℝ) < 2 ^ R * B ^ R := by positivity
    have h4 : (2 : ℝ) ^ (R + 2) * B ^ R = 4 * (2 ^ R * B ^ R) := by ring
    rw [h4]
    linarith
  have hup : ∀ k, 2 * a k ≤ V := by
    intro k
    have h1 : 2 * a k = V / c ^ k := by
      rw [ha]
      field_simp
    rw [h1]
    exact div_le_self hV.le (one_le_pow₀ hc1)
  -- Pigeonhole: if every window were hit, we would inject `R + 1` windows into `R` intervals.
  by_contra hcon
  push Not at hcon
  have hall : ∀ k : Fin (R + 1), ∃ i,
      ¬Disjoint (Set.Icc (a k) (2 * a k)) (Set.Ico (lam i) (B * lam i)) :=
    fun k => hcon (a k) (hlow k (Nat.lt_succ_iff.mp k.2)) (hup k)
  choose f hf using hall
  have hinj : Function.Injective f := by
    intro k k' hkk
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · exact hf k (hmiss (f k) k k' h (hkk ▸ hf k'))
    · exact hf k' (hmiss (f k') k' k h (hkk ▸ hf k))
  have hcard := Fintype.card_le_of_injective f hinj
  simp at hcard

/-- The same lemma in the shape the archive states it
(`UpperTheory.V.Win.window1`): the left endpoints are a finite set `T` of at
most `R` reals, and disjointness is written out pointwise.  It follows from
`interval_lemma`, so the two statements agree. -/
theorem interval_lemma_finset (R : ℕ) (B U : ℝ) (T : Finset ℝ) (hB : 1 ≤ B) (hU : 0 < U)
    (hT : T.card ≤ R) :
    ∃ y : ℝ, U / (2 ^ (R + 2) * B ^ R) ≤ y ∧ 2 * y ≤ U ∧
      ∀ a ∈ T, ∀ u : ℝ, y ≤ u → u ≤ 2 * y → a ≤ u → B * a ≤ u := by
  obtain ⟨y, hy1, hy2, hy3⟩ :=
    interval_lemma B U hB hU T.card (fun i => (T.equivFin.symm i : ℝ))
  refine ⟨y, le_trans ?_ hy1, hy2, ?_⟩
  · have hB0 : 0 < B := lt_of_lt_of_le one_pos hB
    apply div_le_div_of_nonneg_left hU.le (by positivity)
    have h1 : (2 : ℝ) ^ (T.card + 2) ≤ 2 ^ (R + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : B ^ T.card ≤ B ^ R := pow_le_pow_right₀ hB hT
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  · intro a ha u hu1 hu2 hau
    by_contra hlt
    push Not at hlt
    have hdis := hy3 (T.equivFin ⟨a, ha⟩)
    rw [Set.disjoint_left] at hdis
    apply hdis ⟨hu1, hu2⟩
    simp only [Equiv.symm_apply_apply]
    exact ⟨hau, hlt⟩
