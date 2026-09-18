import Mathlib
import JSPProblem.Basic

namespace JSP399

/-!
Boundary cases of the `k`-subset-sum recovery problem (Erdős #494).

* `UR_pred_card`: the `(n - 1)`-sums of an `n`-element set of integers determine it
  uniquely (the `(n-1)`-subsets are exactly the erasures `A.erase a`, and their sums
  are `(∑ x ∈ A, x) - a`; comparing total sums gives `∑ x ∈ A, x = ∑ x ∈ B, x`, and
  the map `a ↦ (∑ x ∈ B, x) - a` is injective on `ℤ`).
* `UR_card_one`: unique recoverability for `n = 1` holds exactly when `k = 1`
  (`k = 0` gives a singleton multiset `{0}` for every input; `k ≥ 2` gives the empty
  multiset for every input).
-/

/-- The 1-sums of a set of integers are its elements. Private variant of the
sibling-file lemma specialized to `ℤ`. -/
private lemma kSums_one_int (A : Finset ℤ) : kSums A 1 = A.val := by
  unfold kSums
  rw [Finset.powersetCard_one, Finset.map_val, Multiset.map_map]
  simp [Function.comp_apply]

/-- If `k` exceeds the cardinality of `A`, there are no `k`-subsets, so the multiset
of `k`-sums is empty. Private variant of the sibling-file lemma specialized to `ℤ`. -/
private lemma kSums_eq_zero_int {A : Finset ℤ} {k : ℕ} (h : A.card < k) : kSums A k = 0 := by
  unfold kSums
  rw [Finset.powersetCard_eq_empty.mpr h, Finset.empty_val, Multiset.map_zero]

/-- 1-sums recover any set of integers. Private variant of `UR_one` for `ℤ`. -/
private theorem UR_one_int (n : ℕ) : UR ℤ 1 n := by
  intro A B hA hB h
  rw [kSums_one_int A, kSums_one_int B] at h
  exact Finset.val_injective h

/-- The `(card - 1)`-subsets of a nonempty finset are exactly its erasures. -/
private lemma powersetCard_pred {α : Type*} [DecidableEq α] (A : Finset α) (hA : 1 ≤ A.card) :
    A.powersetCard (A.card - 1) = A.image (fun a => A.erase a) := by
  ext S
  simp only [Finset.mem_powersetCard, Finset.mem_image]
  constructor
  · rintro ⟨hsub, hcard⟩
    have hsingleton : (A \ S).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, hcard]
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hsingleton
    have haA : a ∈ A := by
      have hmem : a ∈ A \ S := by rw [ha]; exact Finset.mem_singleton_self a
      exact (Finset.mem_sdiff.mp hmem).1
    refine ⟨a, haA, ?_⟩
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_erase] at hx
      by_contra hxS
      have hxsd : x ∈ A \ S := Finset.mem_sdiff.mpr ⟨hx.2, hxS⟩
      rw [ha] at hxsd
      exact hx.1 (Finset.mem_singleton.mp hxsd)
    · rw [Finset.card_erase_of_mem haA, hcard]
  · rintro ⟨a, haA, rfl⟩
    exact ⟨Finset.erase_subset _ _, Finset.card_erase_of_mem haA⟩

/-- The `(n - 1)`-sums of an `n`-element set of integers are the complements
`(∑ x ∈ A, x) - a` for `a ∈ A`. -/
private lemma kSums_pred {A : Finset ℤ} {n : ℕ} (hA : A.card = n) (hn : 1 ≤ n) :
    kSums A (n - 1) = A.val.map (fun a => (∑ x ∈ A, x) - a) := by
  have h1 : n - 1 = A.card - 1 := by rw [← hA]
  have hApos : 1 ≤ A.card := by omega
  have hinj : Set.InjOn (fun a => A.erase a) ↑A := by
    intro a ha b hb hab
    by_contra hne
    have hab' : A.erase a = A.erase b := hab
    have ha' : a ∈ A.erase b := Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp ha⟩
    rw [← hab'] at ha'
    exact Finset.notMem_erase a A ha'
  unfold kSums
  rw [h1, powersetCard_pred A hApos, Finset.image_val_of_injOn hinj, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a ha
  simp only [Function.comp_apply]
  exact Finset.sum_erase_eq_sub ha

/-- The total of the `(n - 1)`-sums of an `n`-element set of integers is
`(n - 1)` times the total of the set (each element is omitted exactly once). -/
private lemma sum_kSums_pred {A : Finset ℤ} {n : ℕ} (hA : A.card = n) (hn : 1 ≤ n) :
    (kSums A (n - 1)).sum = ((n - 1 : ℕ) : ℤ) * (∑ x ∈ A, x) := by
  rw [kSums_pred hA hn, ← Finset.sum_eq_multiset_sum, Finset.sum_sub_distrib,
    Finset.sum_const, hA, nsmul_eq_mul]
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [hcast]
  ring

theorem UR_pred_card (n : ℕ) (hn : 2 ≤ n) : UR ℤ (n - 1) n := by
  intro A B hA hB h
  have hsum := congrArg Multiset.sum h
  rw [sum_kSums_pred hA (by omega : 1 ≤ n), sum_kSums_pred hB (by omega : 1 ≤ n)] at hsum
  have hne : ((n - 1 : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (by omega : n - 1 ≠ 0)
  have hs : (∑ x ∈ A, x) = ∑ x ∈ B, x := mul_left_cancel₀ hne hsum
  rw [kSums_pred hA (by omega : 1 ≤ n), kSums_pred hB (by omega : 1 ≤ n), hs] at h
  have hinj : Function.Injective (fun a : ℤ => (∑ x ∈ B, x) - a) := fun x y hxy => by linarith
  have hval := Multiset.map_injective hinj h
  exact Finset.val_injective hval

theorem UR_card_one (k : ℕ) : UR ℤ k 1 ↔ k = 1 := by
  constructor
  · intro h
    by_contra hk
    have hks : kSums ({0} : Finset ℤ) k = kSums ({1} : Finset ℤ) k := by
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simp [kSums, Finset.powersetCard_zero]
      · rw [kSums_eq_zero_int (show ({0} : Finset ℤ).card < k by
              rw [Finset.card_singleton]; omega),
            kSums_eq_zero_int (show ({1} : Finset ℤ).card < k by
              rw [Finset.card_singleton]; omega)]
    have heq := h _ _ (Finset.card_singleton 0) (Finset.card_singleton 1) hks
    rw [Finset.singleton_inj] at heq
    exact zero_ne_one heq
  · rintro rfl
    exact UR_one_int 1

end JSP399
