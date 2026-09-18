import Mathlib
import JSPProblem.Basic
import JSPProblem.PowSum

/-!
# The `k = 2` power-sum transfer identity (Selfridge–Straus)

For `j ≥ 1`, the `j`-th power sum of the `2`-subset sums of `A` satisfies

`2 * psumk A 2 j = (2 * |A| - 2^j) * psum A j + ∑_{r ∈ Ioo 0 j} C(j,r) * psum A r * psum A (j-r)`,

obtained by expanding `∑_{a,b ∈ A, a ≠ b} (a+b)^j` binomially.  As a corollary,
`psum A j` is determined by `psumk A 2 j`, the lower power sums `psum A r`
(`0 < r < j`), and `|A|`, provided `|A| ≠ 2^(j-1)`.
-/

namespace JSP399

/-- The `k = 2` power-sum transfer identity. -/
theorem psumk_two (A : Finset ℚ) {j : ℕ} (hj : 1 ≤ j) :
    2 * psumk A 2 j = (2 * (A.card : ℚ) - 2 ^ j) * psum A j +
      ∑ r ∈ Finset.Ioo 0 j, (j.choose r : ℚ) * psum A r * psum A (j - r) := by
  -- `2 * psumk` is the sum of `(a+b)^j` over *ordered* off-diagonal pairs.
  have hoff : 2 * psumk A 2 j = ∑ p ∈ A.offDiag, (p.1 + p.2) ^ j := by
    have hmaps : ∀ p ∈ A.offDiag, ({p.1, p.2} : Finset ℚ) ∈ A.powersetCard 2 := by
      intro p hp
      rw [Finset.mem_offDiag] at hp
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.insert_subset_iff.mpr ⟨hp.1, Finset.singleton_subset_iff.mpr hp.2.1⟩,
        Finset.card_pair hp.2.2⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => (p.1 + p.2) ^ j)]
    unfold psumk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨hTS, hT2⟩ := hT
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hT2
    have habS : a ∈ A ∧ b ∈ A := by
      have h := hTS
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff] at h
      exact h
    have hfib : A.offDiag.filter (fun p : ℚ × ℚ => ({p.1, p.2} : Finset ℚ) = {a, b})
        = {(a, b), (b, a)} := by
      apply Finset.ext
      intro p
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨ha, hb, hne⟩, hpair⟩
        have h1 : p.1 = a ∨ p.1 = b := by
          have hm : p.1 ∈ ({a, b} : Finset ℚ) :=
            hpair ▸ Finset.mem_insert_self p.1 ({p.2} : Finset ℚ)
          simpa using hm
        have h2 : p.2 = a ∨ p.2 = b := by
          have hp2 : p.2 ∈ ({p.1, p.2} : Finset ℚ) := by
            rw [Finset.pair_comm]; exact Finset.mem_insert_self _ _
          have hm : p.2 ∈ ({a, b} : Finset ℚ) := hpair ▸ hp2
          simpa using hm
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hne
        · left; exact Prod.ext h1 h2
        · right; exact Prod.ext h1 h2
        · exact absurd (h1.trans h2.symm) hne
      · rintro (rfl | rfl)
        · exact ⟨⟨habS.1, habS.2, hab⟩, rfl⟩
        · exact ⟨⟨habS.2, habS.1, fun h => hab h.symm⟩, Finset.pair_comm b a⟩
    have hneab : (a, b) ≠ (b, a) := fun h => absurd (Prod.ext_iff.mp h).1 hab
    rw [hfib, Finset.sum_pair hneab, Finset.sum_pair hab]
    show 2 * (a + b) ^ j = (a + b) ^ j + (b + a) ^ j
    rw [add_comm b a, ← two_mul]
  -- The diagonal contributes `2^j * psum A j`.
  have hdiag : ∑ p ∈ A.diag, (p.1 + p.2) ^ j = (2 : ℚ) ^ j * psum A j := by
    show ∑ p ∈ A.map ⟨Function.diag, Function.diag_injective⟩, (p.1 + p.2) ^ j = _
    rw [Finset.sum_map]
    unfold psum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    show (a + a) ^ j = 2 ^ j * a ^ j
    rw [← two_mul, mul_pow]
  -- The full product `A ×ˢ A` sum is the binomial double sum.
  have hprod : ∑ p ∈ A ×ˢ A, (p.1 + p.2) ^ j
      = ∑ r ∈ Finset.range (j + 1),
          (j.choose r : ℚ) * psum A r * psum A (j - r) := by
    have hexp : ∀ a ∈ A, ∀ b ∈ A, (a + b) ^ j
        = ∑ r ∈ Finset.range (j + 1), a ^ r * b ^ (j - r) * (j.choose r : ℚ) :=
      fun a _ b _ => add_pow a b j
    calc ∑ p ∈ A ×ˢ A, (p.1 + p.2) ^ j
        = ∑ a ∈ A, ∑ b ∈ A, (a + b) ^ j := Finset.sum_product _ _ _
      _ = ∑ a ∈ A, ∑ b ∈ A, ∑ r ∈ Finset.range (j + 1),
            a ^ r * b ^ (j - r) * (j.choose r : ℚ) :=
          Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl (hexp a ha)
      _ = ∑ a ∈ A, ∑ r ∈ Finset.range (j + 1), ∑ b ∈ A,
            a ^ r * b ^ (j - r) * (j.choose r : ℚ) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ r ∈ Finset.range (j + 1), ∑ a ∈ A, ∑ b ∈ A,
            a ^ r * b ^ (j - r) * (j.choose r : ℚ) :=
          Finset.sum_comm
      _ = ∑ r ∈ Finset.range (j + 1),
            (j.choose r : ℚ) * psum A r * psum A (j - r) := by
          apply Finset.sum_congr rfl
          intro r _
          have hs : (∑ a ∈ A, ∑ b ∈ A, a ^ r * b ^ (j - r))
              = psum A r * psum A (j - r) := by
            unfold psum
            rw [Finset.sum_mul_sum]
          calc ∑ a ∈ A, ∑ b ∈ A, a ^ r * b ^ (j - r) * (j.choose r : ℚ)
              = (∑ a ∈ A, ∑ b ∈ A, a ^ r * b ^ (j - r)) * (j.choose r : ℚ) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro a _
                rw [Finset.sum_mul]
            _ = psum A r * psum A (j - r) * (j.choose r : ℚ) := by rw [hs]
            _ = (j.choose r : ℚ) * psum A r * psum A (j - r) := by ring
  -- `A ×ˢ A` splits into diagonal and off-diagonal.
  have hsplit : ∑ p ∈ A ×ˢ A, (p.1 + p.2) ^ j
      = ∑ p ∈ A.diag, (p.1 + p.2) ^ j + ∑ p ∈ A.offDiag, (p.1 + p.2) ^ j := by
    rw [← Finset.diag_union_offDiag A,
      Finset.sum_union (Finset.disjoint_diag_offDiag A)]
  have hoff2 : ∑ p ∈ A.offDiag, (p.1 + p.2) ^ j
      = ∑ p ∈ A ×ˢ A, (p.1 + p.2) ^ j - ∑ p ∈ A.diag, (p.1 + p.2) ^ j := by
    rw [hsplit]; ring
  -- `psum A 0 = |A|`.
  have hpsum0 : psum A 0 = (A.card : ℚ) := by simp [psum]
  -- Peel off the `r = 0` and `r = j` boundary terms.
  have hsplit_range : ∑ r ∈ Finset.range (j + 1),
        (j.choose r : ℚ) * psum A r * psum A (j - r)
      = 2 * (A.card : ℚ) * psum A j
        + ∑ r ∈ Finset.Ioo 0 j, (j.choose r : ℚ) * psum A r * psum A (j - r) := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    -- The `r ∈ range k` block is the `Ioo 0 (k+1)` sum reindexed.
    have hmid : (∑ r ∈ Finset.range k,
          ((k + 1).choose (r + 1) : ℚ) * psum A (r + 1) * psum A (k + 1 - (r + 1)))
        = ∑ r ∈ Finset.Ioo 0 (k + 1),
            ((k + 1).choose r : ℚ) * psum A r * psum A (k + 1 - r) := by
      have h1 : ∀ i ∈ Finset.range k,
          ((k + 1).choose (i + 1) : ℚ) * psum A (i + 1) * psum A (k + 1 - (i + 1))
          = ((k + 1).choose (1 + i) : ℚ) * psum A (1 + i)
            * psum A (k + 1 - (1 + i)) := by
        intro i _
        rw [Nat.add_comm i 1]
      have h2 : (∑ i ∈ Finset.Ico 1 (k + 1),
            ((k + 1).choose i : ℚ) * psum A i * psum A (k + 1 - i))
          = ∑ i ∈ Finset.range k,
              ((k + 1).choose (1 + i) : ℚ) * psum A (1 + i)
                * psum A (k + 1 - (1 + i)) :=
        Finset.sum_Ico_eq_sum_range _ 1 (k + 1)
      rw [Finset.sum_congr rfl h1, ← h2]
      exact Finset.sum_congr rfl (fun _ _ => rfl)
    rw [Finset.sum_range_succ, Finset.sum_range_succ', hmid]
    simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul,
      Nat.sub_zero, Nat.sub_self, hpsum0]
    ring
  rw [hoff, hoff2, hprod, hdiag, hsplit_range]
  ring

/-- Corollary: the `j`-th power sum is recoverable from the `2`-subset-sum
power sum, the lower power sums and the cardinality, provided
`|A| ≠ 2^(j-1)`. -/
theorem psum_eq_of_psumk_two_eq {A B : Finset ℚ} (hcard : A.card = B.card)
    {j : ℕ} (hj : 1 ≤ j) (hn : (A.card : ℚ) ≠ 2 ^ (j - 1))
    (hk : psumk A 2 j = psumk B 2 j)
    (hlow : ∀ r ∈ Finset.Ioo 0 j, psum A r = psum B r) :
    psum A j = psum B j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hn : (A.card : ℚ) ≠ 2 ^ k := hn
  have hA := psumk_two A hj
  have hB := psumk_two B hj
  rw [hcard] at hA
  -- The middle sums agree: for `r ∈ Ioo 0 (k+1)` also `k+1-r ∈ Ioo 0 (k+1)`.
  have hmid : (∑ r ∈ Finset.Ioo 0 (k + 1),
        ((k + 1).choose r : ℚ) * psum A r * psum A (k + 1 - r))
      = ∑ r ∈ Finset.Ioo 0 (k + 1),
          ((k + 1).choose r : ℚ) * psum B r * psum B (k + 1 - r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrc := Finset.mem_Ioo.mp hr
    have hr' : k + 1 - r ∈ Finset.Ioo 0 (k + 1) :=
      Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
    rw [hlow r hr, hlow (k + 1 - r) hr']
  rw [hmid] at hA
  -- The leading coefficient `2·|B| - 2^(k+1) = 2·(|B| - 2^k)` is nonzero.
  have hcoef : (2 * (B.card : ℚ) - 2 ^ (k + 1)) ≠ 0 := by
    have hne : (B.card : ℚ) ≠ 2 ^ k := by
      have h := hn
      rwa [hcard] at h
    intro hcon
    apply hne
    rw [pow_succ] at hcon
    linear_combination hcon / 2
  have hmain : (2 * (B.card : ℚ) - 2 ^ (k + 1)) * psum A (k + 1)
      = (2 * (B.card : ℚ) - 2 ^ (k + 1)) * psum B (k + 1) := by
    have h2 : 2 * psumk A 2 (k + 1) = 2 * psumk B 2 (k + 1) := by rw [hk]
    rw [hA, hB] at h2
    linear_combination h2
  exact mul_left_cancel₀ hcoef hmain

end JSP399
