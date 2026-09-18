import Mathlib

namespace JSP399

/-- Multiset of sums of all `k`-element subsets of `A`. -/
def kSums {α : Type*} [AddCommMonoid α] (A : Finset α) (k : ℕ) : Multiset α :=
  (A.powersetCard k).val.map fun S => S.sum id

/-- `UR α k n`: every `n`-element finset of `α` is uniquely determined by
its multiset of `k`-element subset sums. -/
def UR (α : Type*) [DecidableEq α] [AddCommMonoid α] (k n : ℕ) : Prop :=
  ∀ A B : Finset α, A.card = n → B.card = n → kSums A k = kSums B k → A = B

theorem kSums_card {α : Type*} [AddCommMonoid α] (A : Finset α) (k : ℕ) :
    (kSums A k).card = A.card.choose k := by
  unfold kSums
  rw [Multiset.card_map]
  exact Finset.card_powersetCard _ _

/-- Auxiliary step: for `1 ≤ k ≤ m`, the binomial coefficient `n.choose k` is
strictly increasing in `n` at `m`. -/
private theorem choose_lt_succ {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    m.choose k < (m + 1).choose k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [Nat.succ_eq_add_one]
  rw [Nat.choose_succ_succ']
  have h : 0 < m.choose k := Nat.choose_pos (by omega)
  omega

/-- Note: a `1 ≤ k` hypothesis is needed; for `k = 0` every `kSums` equals
`{0}`, so the multiset carries no cardinality information. -/
theorem card_eq_of_kSums_eq {α : Type*} [DecidableEq α] [AddCommMonoid α] {A B : Finset α}
    {k : ℕ} (hk : 1 ≤ k) (hA : k ≤ A.card) (h : kSums A k = kSums B k) :
    A.card = B.card := by
  have h1 : A.card.choose k = B.card.choose k := by
    have h2 := congrArg Multiset.card h
    rwa [kSums_card, kSums_card] at h2
  have hB : k ≤ B.card := by
    by_contra hcon
    have hz : B.card.choose k = 0 := Nat.choose_eq_zero_of_lt (lt_of_not_ge hcon)
    rw [← h1] at hz
    exact (Nat.choose_pos hA).ne' hz
  rcases lt_trichotomy A.card B.card with hlt | heq | hgt
  · exfalso
    have h3 : A.card.choose k < B.card.choose k :=
      (choose_lt_succ hk hA).trans_le
        (Nat.choose_le_choose k (show A.card + 1 ≤ B.card by omega))
    omega
  · exact heq
  · exfalso
    have h3 : B.card.choose k < A.card.choose k :=
      (choose_lt_succ hk hB).trans_le
        (Nat.choose_le_choose k (show B.card + 1 ≤ A.card by omega))
    omega

theorem kSums_eq_zero_of_card_lt {α : Type*} [AddCommMonoid α] {A : Finset α} {k : ℕ}
    (h : A.card < k) : kSums A k = 0 := by
  rw [← Multiset.card_eq_zero, kSums_card, Nat.choose_eq_zero_of_lt h]

theorem kSums_one {α : Type*} [DecidableEq α] [AddCommMonoid α] (A : Finset α) :
    kSums A 1 = A.val := by
  unfold kSums
  rw [Finset.powersetCard_one, Finset.map_val, Multiset.map_map]
  have hfun : ((fun S : Finset α => S.sum id) ∘
      (⟨_, Finset.singleton_injective⟩ : α ↪ Finset α)) = id := by
    funext a
    exact Finset.sum_singleton id a
  rw [hfun, Multiset.map_id]

theorem UR_one (α : Type*) [DecidableEq α] [AddCommMonoid α] (n : ℕ) : UR α 1 n := by
  intro A B _ _ h
  rw [kSums_one, kSums_one] at h
  exact Finset.val_inj.mp h

theorem UR_card_zero (α : Type*) [DecidableEq α] [AddCommMonoid α] (k : ℕ) :
    UR α k 0 := by
  intro A B hA hB _
  rw [Finset.card_eq_zero] at hA hB
  rw [hA, hB]

theorem kSums_self {α : Type*} [AddCommMonoid α] (A : Finset α) :
    kSums A A.card = {A.sum id} := by
  unfold kSums
  rw [Finset.powersetCard_self]
  rfl

theorem sum_kSums (A : Finset ℤ) {k : ℕ} (hk : 1 ≤ k) (hkA : k ≤ A.card) :
    (kSums A k).sum = ((A.card - 1).choose (k - 1) : ℤ) * A.sum id := by
  classical
  have h2 : ∀ S ∈ A.powersetCard k,
      S.sum id = ∑ a ∈ A, (if a ∈ S then (a : ℤ) else 0) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hS.1]
    rfl
  have h4 : ∀ a ∈ A, ∑ S ∈ A.powersetCard k, (if a ∈ S then (a : ℤ) else 0)
      = ((A.card - 1).choose (k - 1) : ℤ) * a := by
    intro a ha
    rw [← Finset.sum_filter, Finset.sum_const]
    have h5 : ((A.powersetCard k).filter fun S => a ∈ S).card
        = (A.card - 1).choose (k - 1) := by
      have h6 : (A.powersetCard k).filter (fun S => a ∈ S)
          = (A.powersetCard k).filter ({a} ⊆ ·) := by
        apply Finset.filter_congr
        intro S _
        exact Finset.singleton_subset_iff.symm
      rw [h6, Finset.card_filter_powersetCard_subset {a} A k
        (Finset.singleton_subset_iff.mpr ha) (by rw [Finset.card_singleton]; exact hk)]
      simp
    rw [h5, nsmul_eq_mul]
  calc (kSums A k).sum = ∑ S ∈ A.powersetCard k, S.sum id := rfl
    _ = ∑ S ∈ A.powersetCard k, ∑ a ∈ A, (if a ∈ S then (a : ℤ) else 0) :=
        Finset.sum_congr rfl h2
    _ = ∑ a ∈ A, ∑ S ∈ A.powersetCard k, (if a ∈ S then (a : ℤ) else 0) :=
        Finset.sum_comm
    _ = ∑ a ∈ A, ((A.card - 1).choose (k - 1) : ℤ) * a := Finset.sum_congr rfl h4
    _ = ((A.card - 1).choose (k - 1) : ℤ) * ∑ a ∈ A, a :=
        (Finset.mul_sum _ _ _).symm
    _ = ((A.card - 1).choose (k - 1) : ℤ) * A.sum id := rfl

end JSP399
