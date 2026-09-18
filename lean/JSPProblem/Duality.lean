import Mathlib
import JSPProblem.Basic

namespace JSP399

/-- Complement duality for `k`-subset sums: the map `S ↦ A \ S` is a bijection
between `A.powersetCard k` and `A.powersetCard (A.card - k)`, and the sum of the
complement equals `A.sum id - s`. -/
theorem kSums_compl (A : Finset ℤ) {k : ℕ} (hk : k ≤ A.card) :
    kSums A (A.card - k) = (kSums A k).map (fun s => A.sum id - s) := by
  have hbij : A.powersetCard (A.card - k) =
      (A.powersetCard k).image (fun S => A \ S) := by
    ext T
    constructor
    · intro hT
      rw [Finset.mem_powersetCard] at hT
      rw [Finset.mem_image]
      exact ⟨A \ T,
        Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset, by
          rw [Finset.card_sdiff_of_subset hT.1, hT.2, Nat.sub_sub_self hk]⟩,
        Finset.sdiff_sdiff_eq_self hT.1⟩
    · intro hT
      rw [Finset.mem_image] at hT
      obtain ⟨S, hS, hST⟩ := hT
      have hST' : A \ S = T := hST
      rw [Finset.mem_powersetCard] at hS ⊢
      rw [← hST']
      exact ⟨Finset.sdiff_subset, by rw [Finset.card_sdiff_of_subset hS.1, hS.2]⟩
  have hinj : Set.InjOn (fun S => A \ S) (A.powersetCard k) := by
    intro S hS T hT h
    have hS' : S ⊆ A := (Finset.mem_powersetCard.mp (Finset.mem_coe.mp hS)).1
    have hT' : T ⊆ A := (Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT)).1
    have h2 : A \ S = A \ T := h
    rw [← Finset.sdiff_sdiff_eq_self hS', ← Finset.sdiff_sdiff_eq_self hT', h2]
  show (A.powersetCard (A.card - k)).val.map (fun S => S.sum id) =
    ((A.powersetCard k).val.map fun S => S.sum id).map (fun s => A.sum id - s)
  rw [hbij, Finset.image_val_of_injOn hinj, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun S hS => ?_
  have hSA : S ⊆ A := (Finset.mem_powersetCard.mp hS).1
  exact Finset.sum_sdiff_eq_sub hSA

/-- Complement duality transfers an equality of `k`-subset sums to an equality
of `(card - k)`-subset sums, provided the cardinalities and total sums agree. -/
theorem kSums_compl_eq_of_kSums_eq {A B : Finset ℤ} {k : ℕ} (hA : k ≤ A.card)
    (hcard : A.card = B.card) (hsum : A.sum id = B.sum id)
    (h : kSums A k = kSums B k) :
    kSums A (A.card - k) = kSums B (B.card - k) := by
  have hB : k ≤ B.card := by rw [← hcard]; exact hA
  rw [kSums_compl A hA, kSums_compl B hB, h, hsum]

/-- Unique recovery from `k`-subset sums implies unique recovery from
`(n - k)`-subset sums, for `0 ≤ k < n`. -/
theorem UR_compl {k n : ℕ} (hn : k < n) : UR ℤ k n → UR ℤ (n - k) n := by
  intro hUR A B hAcard hBcard h
  have hA : k ≤ A.card := by rw [hAcard]; exact hn.le
  have hB : k ≤ B.card := by rw [hBcard]; exact hn.le
  have h1 : 1 ≤ n - k := Nat.sub_pos_of_lt hn
  have hsubA : n - k ≤ A.card := by rw [hAcard]; exact Nat.sub_le n k
  have hsubB : n - k ≤ B.card := by rw [hBcard]; exact Nat.sub_le n k
  have hsumA : (kSums A (n - k)).sum =
      ((n - 1).choose (n - k - 1) : ℤ) * A.sum id := by
    have h := sum_kSums A h1 hsubA
    rw [hAcard] at h
    exact h
  have hsumB : (kSums B (n - k)).sum =
      ((n - 1).choose (n - k - 1) : ℤ) * B.sum id := by
    have h := sum_kSums B h1 hsubB
    rw [hBcard] at h
    exact h
  have hsumAB : A.sum id = B.sum id := by
    have hpos : 0 < (n - 1).choose (n - k - 1) := Nat.choose_pos (by omega)
    have h0 : ((n - 1).choose (n - k - 1) : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
    apply mul_left_cancel₀ h0
    rw [← hsumA, ← hsumB]
    exact congrArg Multiset.sum h
  have hA' : kSums A (A.card - k) = kSums B (B.card - k) := by
    rw [hAcard, hBcard]
    exact h
  rw [kSums_compl A hA, kSums_compl B hB, hsumAB] at hA'
  have hinj : Function.Injective fun s : ℤ => B.sum id - s := by
    intro x y hxy
    have hxy' : B.sum id - x = B.sum id - y := hxy
    omega
  have hkSums : kSums A k = kSums B k := Multiset.map_injective hinj hA'
  exact hUR A B hAcard hBcard hkSums

end JSP399
