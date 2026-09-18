import Mathlib
import JSPProblem.Basic

namespace JSP399

/-- Negation on `ℤ`, packaged as an embedding. -/
private def negEmb : ℤ ↪ ℤ := ⟨Neg.neg, neg_injective⟩

private theorem negEmb_apply (a : ℤ) : negEmb a = -a := rfl

/-- Tao's `n = 2k` family: a set `A ⊆ ℤ` of `2k` integers summing to `0` has
the same `k`-subset-sum multiset as its reflection `-A`.

Indeed, a `k`-subset of `-A` is `-T` for a `k`-subset `T` of `A`, and
`∑ (-T) = -∑ T = ∑ A - ∑ T = ∑ (A \ T)`, while `T ↦ A \ T` is an involution of
the `k`-subsets of `A` (since `|A \ T| = 2k - k = k`). -/
theorem kSums_neg_of_sum_eq_zero (A : Finset ℤ) (k : ℕ) (hA : A.card = 2 * k)
    (hsum : A.sum id = 0) :
    kSums A k = kSums (A.map ⟨Neg.neg, neg_injective⟩) k := by
  show kSums A k = kSums (A.map negEmb) k
  -- Negation is an involution on finsets.
  have hmap2 : ∀ s : Finset ℤ, (s.map negEmb).map negEmb = s := by
    intro s
    rw [Finset.map_map]
    ext x
    simp only [Finset.mem_map, Function.Embedding.coe_trans, Function.comp_apply,
      negEmb_apply, neg_neg]
    exact ⟨fun ⟨a, ha, hax⟩ => hax ▸ ha, fun hx => ⟨x, hx, rfl⟩⟩
  -- The `k`-subsets of `-A` are exactly `-T` for `T` a `k`-subset of `A`.
  have hpow : (A.map negEmb).powersetCard k
      = (A.powersetCard k).image fun T => T.map negEmb := by
    ext S
    simp only [Finset.mem_powersetCard, Finset.mem_image]
    constructor
    · rintro ⟨hSsub, hScard⟩
      refine ⟨S.map negEmb, ⟨?_, by rw [Finset.card_map]; exact hScard⟩, hmap2 S⟩
      have h : S.map negEmb ⊆ (A.map negEmb).map negEmb :=
        Finset.map_subset_map.2 hSsub
      rwa [hmap2 A] at h
    · rintro ⟨T, ⟨hTsub, hTcard⟩, rfl⟩
      exact ⟨Finset.map_subset_map.2 hTsub, (Finset.card_map _).trans hTcard⟩
  -- `∑ (-T) = -∑ T = ∑ (A \ T)` since `∑ A = 0`.
  have hsum_eq : ∀ T ∈ A.powersetCard k,
      (T.map negEmb).sum id = (A \ T).sum id := by
    intro T hT
    obtain ⟨hTsub, -⟩ := Finset.mem_powersetCard.1 hT
    have hs : (A \ T).sum id + T.sum id = A.sum id := Finset.sum_sdiff hTsub
    rw [hsum] at hs
    have h1 : (T.map negEmb).sum id = -T.sum id := by
      simp only [Finset.sum_map, ← Finset.sum_neg_distrib, id_eq, negEmb_apply]
    omega
  -- `T ↦ A \ T` maps `k`-subsets to `k`-subsets, bijectively.
  have himg : (A.powersetCard k).image (fun T => A \ T) = A.powersetCard k := by
    ext U
    simp only [Finset.mem_image, Finset.mem_powersetCard]
    constructor
    · rintro ⟨T, ⟨hTsub, hTcard⟩, rfl⟩
      refine ⟨Finset.sdiff_subset, ?_⟩
      rw [Finset.card_sdiff_of_subset hTsub, hTcard, hA]
      omega
    · rintro ⟨hUsub, hUcard⟩
      exact ⟨A \ U,
        ⟨Finset.sdiff_subset, by
          rw [Finset.card_sdiff_of_subset hUsub, hUcard, hA]; omega⟩,
        Finset.sdiff_sdiff_eq_self hUsub⟩
  -- The corresponding `Multiset.map`s stay nodup, so `image` ↦ `val.map`.
  have hnd1 : Multiset.Nodup ((A.powersetCard k).val.map fun T => T.map negEmb) :=
    Multiset.Nodup.map (Finset.map_injective negEmb) (Finset.nodup _)
  have hval1 : ((A.powersetCard k).image fun T => T.map negEmb).val
      = (A.powersetCard k).val.map fun T => T.map negEmb := by
    rw [Finset.image_val, Multiset.dedup_eq_self.mpr hnd1]
  have hnd2 : Multiset.Nodup ((A.powersetCard k).val.map fun T => A \ T) := by
    refine Multiset.Nodup.map_on ?_ (Finset.nodup _)
    intro T₁ h₁ T₂ h₂ h
    rw [Finset.mem_val, Finset.mem_powersetCard] at h₁ h₂
    have h' : A \ T₁ = A \ T₂ := h
    calc T₁ = A \ (A \ T₁) := (Finset.sdiff_sdiff_eq_self h₁.1).symm
      _ = A \ (A \ T₂) := by rw [h']
      _ = T₂ := Finset.sdiff_sdiff_eq_self h₂.1
  have hval2 : ((A.powersetCard k).image fun T => A \ T).val
      = (A.powersetCard k).val.map fun T => A \ T := by
    rw [Finset.image_val, Multiset.dedup_eq_self.mpr hnd2]
  -- Chain of multiset equalities.
  have step1 : ((A.map negEmb).powersetCard k).val.map (fun S => S.sum id)
      = (A.powersetCard k).val.map fun T => (T.map negEmb).sum id := by
    rw [hpow, hval1, Multiset.map_map]
    rfl
  have step2 : (A.powersetCard k).val.map (fun T => (T.map negEmb).sum id)
      = (A.powersetCard k).val.map fun T => (A \ T).sum id :=
    Multiset.map_congr rfl fun T hT => hsum_eq T hT
  have step3 : (A.powersetCard k).val.map (fun T => (A \ T).sum id)
      = (A.powersetCard k).val.map fun S => S.sum id := by
    have h := Multiset.map_map (fun S : Finset ℤ => S.sum id) (fun T => A \ T)
        (A.powersetCard k).val
    rw [← hval2, himg] at h
    exact h.symm
  show (A.powersetCard k).val.map (fun S => S.sum id)
      = ((A.map negEmb).powersetCard k).val.map fun S => S.sum id
  rw [step1, step2, step3]

/-- Failure of unique recoverability at `n = 2k` for `k ≥ 2`: the set
`A = {1, …, 2k - 1} ∪ {-k(2k - 1)}` has `2k` elements, sums to `0`, and is not
equal to its reflection `-A`, yet shares its `k`-subset-sum multiset. -/
theorem not_UR_two_mul {k : ℕ} (hk : 2 ≤ k) : ¬ UR ℤ k (2 * k) := by
  intro hUR
  set m : ℕ := 2 * k - 1 with hm
  have hm3 : 3 ≤ m := by omega
  -- `P = {1, …, m} ⊆ ℤ` where `m = 2k - 1 ≥ 3`.
  set P : Finset ℤ := (Finset.Icc 1 m).image fun n : ℕ => (n : ℤ) with hPdef
  have hinj : Function.Injective fun n : ℕ => (n : ℤ) := Nat.cast_injective
  have hPcard : P.card = m := by
    rw [hPdef, Finset.card_image_of_injective _ hinj, Nat.card_Icc]
    omega
  have hPmem : ∀ x ∈ P, 1 ≤ x := by
    intro x hx
    rw [hPdef, Finset.mem_image] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    show (1 : ℤ) ≤ (n : ℤ)
    rw [Finset.mem_Icc] at hn
    exact_mod_cast hn.1
  have h12 : ({1, 2} : Finset ℤ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [hPdef, Finset.mem_image]
      exact ⟨1, by rw [Finset.mem_Icc]; exact ⟨le_refl 1, by omega⟩, by simp⟩
    · rw [hPdef, Finset.mem_image]
      exact ⟨2, by rw [Finset.mem_Icc]; exact ⟨by norm_num, by omega⟩, by simp⟩
  have hPsum3 : 3 ≤ P.sum id := by
    have h : ({1, 2} : Finset ℤ).sum id ≤ P.sum id :=
      Finset.sum_le_sum_of_subset_of_nonneg h12 fun x hx _ =>
        le_trans (by norm_num : (0 : ℤ) ≤ 1) (hPmem x hx)
    have hs : ({1, 2} : Finset ℤ).sum id = 3 := by
      rw [Finset.sum_pair (show (1 : ℤ) ≠ 2 by norm_num)]
      norm_num [id_eq]
    rwa [hs] at h
  -- `A = P ∪ {-∑ P}`: the extra element is negative, hence new.
  have hnegP : -(P.sum id) ∉ P := by
    intro hx
    have hx1 := hPmem _ hx
    omega
  set A : Finset ℤ := insert (-(P.sum id)) P with hAdef
  have hAcard : A.card = 2 * k := by
    rw [hAdef, Finset.card_insert_of_notMem hnegP, hPcard]
    omega
  have hAsum : A.sum id = 0 := by
    have h : A.sum id = -(P.sum id) + P.sum id := by
      rw [hAdef]
      exact Finset.sum_insert hnegP
    omega
  -- `A ≠ -A` because `1 ∈ A` but `-1 ∉ A`.
  have h1A : (1 : ℤ) ∈ A := by
    rw [hAdef, Finset.mem_insert]
    exact Or.inr (h12 (Finset.mem_insert_self 1 {2}))
  have hneg1A : (-1 : ℤ) ∉ A := by
    rw [hAdef, Finset.mem_insert]
    rintro (h | h)
    · omega
    · have := hPmem _ h; omega
  have hne : A ≠ A.map ⟨Neg.neg, neg_injective⟩ := by
    intro h
    have h1B : (1 : ℤ) ∈ A.map ⟨Neg.neg, neg_injective⟩ := h ▸ h1A
    rw [Finset.mem_map] at h1B
    obtain ⟨a, ha, hae⟩ := h1B
    have hae' : -a = 1 := hae
    have ha' : a = -1 := by omega
    exact hneg1A (ha' ▸ ha)
  have hBcard : (A.map ⟨Neg.neg, neg_injective⟩).card = 2 * k := by
    rw [Finset.card_map]
    exact hAcard
  have hks := kSums_neg_of_sum_eq_zero A k hAcard hAsum
  exact hne (hUR A (A.map ⟨Neg.neg, neg_injective⟩) hAcard hBcard hks)

end JSP399
