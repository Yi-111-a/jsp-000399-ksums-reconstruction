import Mathlib
import JSPProblem.Basic
import JSPProblem.PowSum

/-!
# Transport along the coercion `ℤ ↪ ℚ`

The coercion embedding `ℤ ↪ ℚ` transports integer `kSums` data into `ℚ`, where
the power-sum infrastructure of `JSPProblem/PowSum.lean` applies.  The technique
mirrors `powersetCard_map_intEmb` and `kSums_map_intEmb` in
`JSPProblem/ThueMorse.lean`.
-/

namespace JSP399

/-- The coercion embedding `ℤ ↪ ℚ`. -/
def ratCastEmb : ℤ ↪ ℚ := ⟨fun z => (z : ℚ), Int.cast_injective⟩

/-- `powersetCard` commutes with mapping a finset along an embedding. -/
theorem powersetCard_map_emb {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (S : Finset α) (k : ℕ) :
    (S.map e).powersetCard k
      = (S.powersetCard k).map ⟨fun T => T.map e, Finset.map_injective e⟩ := by
  rw [Finset.map_eq_image, Finset.powersetCard_eq_filter, Finset.powerset_image,
    Finset.filter_image]
  have h1 : (S.powerset.filter fun T => (T.image e).card = k)
      = S.powerset.filter (·.card = k) := by
    apply Finset.filter_congr
    intro T _
    rw [Finset.card_image_of_injective _ e.injective]
  rw [h1]
  rw [Finset.map_eq_image, Finset.powersetCard_eq_filter]
  apply Finset.image_congr
  intro T _
  exact (Finset.map_eq_image _ _).symm

/-- `psumzk` is the multiset power sum of `kSums`. -/
theorem psumzk_eq_map_sum (A : Finset ℤ) (k j : ℕ) :
    psumzk A k j = Multiset.sum (Multiset.map (fun s => (Int.cast s : ℚ) ^ j)
      (kSums A k)) := by
  unfold psumzk
  rw [Finset.sum_eq_multiset_sum]
  show Multiset.sum (Multiset.map (fun T => (Int.cast (T.sum id) : ℚ) ^ j)
      (A.powersetCard k).val)
    = Multiset.sum (Multiset.map (fun s => (Int.cast s : ℚ) ^ j)
      (Multiset.map (fun S => S.sum id) (A.powersetCard k).val))
  rw [Multiset.map_map]
  rfl

/-- Equal `kSums` multisets give equal `k`-sum power sums. -/
theorem psumzk_eq_of_kSums_eq {A B : Finset ℤ} {k j : ℕ}
    (h : kSums A k = kSums B k) : psumzk A k j = psumzk B k j := by
  rw [psumzk_eq_map_sum, psumzk_eq_map_sum, h]

theorem psum_map_ratCast (A : Finset ℤ) (j : ℕ) :
    psum (A.map ratCastEmb) j = psumz A j := by
  unfold psum psumz
  rw [Finset.sum_map]
  rfl

theorem psumk_map_ratCast (A : Finset ℤ) (k j : ℕ) :
    psumk (A.map ratCastEmb) k j = psumzk A k j := by
  have hsum : ∀ T : Finset ℤ,
      (T.map ratCastEmb).sum id = ((T.sum id : ℤ) : ℚ) := by
    intro T
    rw [Finset.sum_map]
    show (∑ x ∈ T, ((x : ℤ) : ℚ)) = _
    exact (Int.cast_sum T fun x => x).symm
  unfold psumk psumzk
  rw [powersetCard_map_emb, Finset.sum_map]
  refine Finset.sum_congr rfl fun T _ => ?_
  show ((T.map ratCastEmb).sum id) ^ j = ((T.sum id : ℤ) : ℚ) ^ j
  congr 1
  exact hsum T

theorem card_map_ratCast (A : Finset ℤ) : (A.map ratCastEmb).card = A.card :=
  Finset.card_map _

theorem finset_eq_of_map_ratCast_eq {A B : Finset ℤ}
    (h : A.map ratCastEmb = B.map ratCastEmb) : A = B :=
  Finset.map_injective ratCastEmb h

end JSP399
