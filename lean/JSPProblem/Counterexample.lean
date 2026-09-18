import Mathlib
import JSPProblem.Basic

/-!
# Counterexamples to unique recovery from subset sums (JSP-000399)

We exhibit explicit failures of `UR ℤ k n`: pairs of distinct `n`-element sets of
integers whose multisets of `k`-subset sums coincide.
-/

namespace JSP399

/-- `{0,3,5,6}` and `{1,2,4,7}` both have pair-sum multiset `{3,5,6,8,9,11}`:
unique recovery from 2-sums fails already at size 4. -/
theorem not_UR_two_four : ¬ UR ℤ 2 4 := by
  intro hUR
  have hcardA : ({0, 3, 5, 6} : Finset ℤ).card = 4 := by decide
  have hcardB : ({1, 2, 4, 7} : Finset ℤ).card = 4 := by decide
  have hks : kSums ({0, 3, 5, 6} : Finset ℤ) 2 = kSums ({1, 2, 4, 7} : Finset ℤ) 2 := by
    decide
  have hne : ({0, 3, 5, 6} : Finset ℤ) ≠ ({1, 2, 4, 7} : Finset ℤ) := by
    intro h
    have h0 : (0 : ℤ) ∈ ({0, 3, 5, 6} : Finset ℤ) := by decide
    rw [h] at h0
    exact absurd h0 (by decide)
  exact hne (hUR _ _ hcardA hcardB hks)

/-- For `k ≥ 2`, `A = {0, 1, …, k-1}` and `B` obtained by replacing `0, k-1` with
`-1, k` are distinct `k`-element sets with the same total sum, hence equal
(singleton) `k`-sum multisets. -/
theorem not_UR_self {k : ℕ} (hk : 2 ≤ k) : ¬ UR ℤ k k := by
  intro hUR
  set A : Finset ℤ := Finset.Icc 0 ((k : ℤ) - 1) with hA
  set C : Finset ℤ := (A.erase 0).erase ((k : ℤ) - 1) with hC
  set B : Finset ℤ := insert (-1) (insert (k : ℤ) C) with hB
  -- membership facts
  have e0 : (0 : ℤ) ∈ A := by
    rw [hA, Finset.mem_Icc]
    exact ⟨le_refl _, by omega⟩
  have e1z : ((k : ℤ) - 1) ∈ A := by
    rw [hA, Finset.mem_Icc]
    exact ⟨by omega, le_refl _⟩
  have e1 : ((k : ℤ) - 1) ∈ A.erase 0 := Finset.mem_erase.mpr ⟨by omega, e1z⟩
  have hkn : (k : ℤ) ∉ A := by
    rw [hA, Finset.mem_Icc]
    rintro ⟨-, hle⟩
    omega
  have hneg : (-1 : ℤ) ∉ A := by
    rw [hA, Finset.mem_Icc]
    rintro ⟨hle, -⟩
    omega
  have hCsub : C ⊆ A :=
    (Finset.erase_subset ((k : ℤ) - 1) (A.erase 0)).trans (Finset.erase_subset 0 A)
  have hknC : (k : ℤ) ∉ C := fun h => hkn (hCsub h)
  have hnegnC : (-1 : ℤ) ∉ C := fun h => hneg (hCsub h)
  have hk1nC : ((k : ℤ) - 1) ∉ C := Finset.notMem_erase ((k : ℤ) - 1) (A.erase 0)
  have h0nC : (0 : ℤ) ∉ C := fun h =>
    Finset.notMem_erase 0 A (Finset.erase_subset ((k : ℤ) - 1) (A.erase 0) h)
  -- cardinalities
  have hcardA : A.card = k := by
    rw [hA, Int.card_Icc, show ((k : ℤ) - 1 + 1 - 0) = (k : ℤ) from by ring,
      Int.toNat_natCast]
  have hcardC : C.card = k - 2 := by
    rw [hC, Finset.card_erase_of_mem e1, Finset.card_erase_of_mem e0, hcardA]
    omega
  have hin2 : (-1 : ℤ) ∉ insert (k : ℤ) C := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · omega
    · exact hnegnC h
  have h0ni : (0 : ℤ) ∉ insert ((k : ℤ) - 1) C := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · omega
    · exact h0nC h
  have hcardB : B.card = k := by
    rw [hB, Finset.card_insert_of_notMem hin2, Finset.card_insert_of_notMem hknC, hcardC]
    omega
  -- sums
  have hCeq : insert ((k : ℤ) - 1) C = A.erase 0 := Finset.insert_erase e1
  have hAeq : insert 0 (insert ((k : ℤ) - 1) C) = A := by
    rw [hCeq]
    exact Finset.insert_erase e0
  have hsumA : A.sum id = (k : ℤ) - 1 + C.sum id := by
    rw [← hAeq, Finset.sum_insert h0ni, Finset.sum_insert hk1nC]
    simp only [id_eq, zero_add]
  have hsumB : B.sum id = (k : ℤ) - 1 + C.sum id := by
    rw [hB, Finset.sum_insert hin2, Finset.sum_insert hknC]
    simp only [id_eq]
    ring
  have hsum : B.sum id = A.sum id := hsumB.trans hsumA.symm
  -- k-sums coincide since each set has exactly `k` elements
  have hA' : kSums A k = {A.sum id} := by
    rw [← hcardA]
    exact kSums_self A
  have hB' : kSums B k = {B.sum id} := by
    rw [← hcardB]
    exact kSums_self B
  have hks : kSums A k = kSums B k := by
    rw [hA', hB', hsum]
  have hne : A ≠ B := by
    intro hAB
    have hmem : (-1 : ℤ) ∈ B := by
      rw [hB]
      exact Finset.mem_insert_self _ _
    rw [← hAB] at hmem
    exact hneg hmem
  exact hne (hUR A B hcardA hcardB hks)

/-- If `n < k`, any two distinct `n`-element sets have empty (hence equal)
`k`-sum multisets. -/
theorem not_UR_of_card_lt {n k : ℕ} (h1 : 1 ≤ n) (h2 : n < k) : ¬ UR ℤ k n := by
  intro hUR
  set A : Finset ℤ := Finset.Icc 0 ((n : ℤ) - 1) with hA
  set B : Finset ℤ := Finset.Icc 1 (n : ℤ) with hB
  have hcardA : A.card = n := by
    rw [hA, Int.card_Icc, show ((n : ℤ) - 1 + 1 - 0) = (n : ℤ) from by ring,
      Int.toNat_natCast]
  have hcardB : B.card = n := by
    rw [hB, Int.card_Icc, show ((n : ℤ) + 1 - 1) = (n : ℤ) from by ring,
      Int.toNat_natCast]
  have hks : kSums A k = kSums B k := by
    rw [kSums_eq_zero_of_card_lt (show A.card < k by rw [hcardA]; exact h2),
      kSums_eq_zero_of_card_lt (show B.card < k by rw [hcardB]; exact h2)]
  have h0A : (0 : ℤ) ∈ A := by
    rw [hA, Finset.mem_Icc]
    exact ⟨le_refl _, by omega⟩
  have h0B : (0 : ℤ) ∉ B := by
    rw [hB, Finset.mem_Icc]
    rintro ⟨hle, -⟩
    omega
  have hne : A ≠ B := by
    intro hAB
    rw [hAB] at h0A
    exact h0B h0A
  exact hne (hUR A B hcardA hcardB hks)

/-- For `k = 0`, every set has `k`-sum multiset `{0}`, so any two distinct
`n`-element sets with `n ≥ 1` give a failure of unique recovery. -/
theorem not_UR_zero {n : ℕ} (h1 : 1 ≤ n) : ¬ UR ℤ 0 n := by
  intro hUR
  have kSums_zero : ∀ A : Finset ℤ, kSums A 0 = {0} := by
    intro A
    unfold kSums
    rw [Finset.powersetCard_zero, Finset.singleton_val, Multiset.map_singleton,
      Finset.sum_empty]
  set A : Finset ℤ := Finset.Icc 0 ((n : ℤ) - 1) with hA
  set B : Finset ℤ := Finset.Icc 1 (n : ℤ) with hB
  have hcardA : A.card = n := by
    rw [hA, Int.card_Icc, show ((n : ℤ) - 1 + 1 - 0) = (n : ℤ) from by ring,
      Int.toNat_natCast]
  have hcardB : B.card = n := by
    rw [hB, Int.card_Icc, show ((n : ℤ) + 1 - 1) = (n : ℤ) from by ring,
      Int.toNat_natCast]
  have hks : kSums A 0 = kSums B 0 := by
    rw [kSums_zero, kSums_zero]
  have h0A : (0 : ℤ) ∈ A := by
    rw [hA, Finset.mem_Icc]
    exact ⟨le_refl _, by omega⟩
  have h0B : (0 : ℤ) ∉ B := by
    rw [hB, Finset.mem_Icc]
    rintro ⟨hle, -⟩
    omega
  have hne : A ≠ B := by
    intro hAB
    rw [hAB] at h0A
    exact h0B h0A
  exact hne (hUR A B hcardA hcardB hks)

end JSP399
