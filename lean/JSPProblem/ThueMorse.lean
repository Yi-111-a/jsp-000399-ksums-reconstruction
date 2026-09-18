import Mathlib
import JSPProblem.Basic

/-!
# JSP-000399 (Erdős #494) — the Thue–Morse counterexample at `k = 2`

Splitting `Finset.range (2 ^ m)` into the numbers whose binary digit sum is
even (`tmA m`) and odd (`tmB m`) gives two distinct sets of size `2 ^ (m - 1)`
with the *same* multiset of pairwise sums.  Hence `k = 2` sums do not uniquely
recover a set of `2 ^ (m - 1)` integers for `m ≥ 2`.

The proof uses generating polynomials in `ℤ[X]`.  Writing
`F m u = ∑_{i < 2^m} u^{t(i)} X^i` where `t(i)` is the binary digit sum, the
Prouhet factorization `F m u = ∏_{r < m} (1 + u X^{2^r})` gives
`F m (-1) · F m 1 = (F m (-1)).comp (X ^ 2)`, which says exactly that the
squared generating polynomials of `tmA m` and `tmB m` differ only on the
diagonal — i.e. their pair-sum multisets agree.
-/

namespace JSP399

open Polynomial

/-- Even/odd binary-digit-sum halves of `Finset.range (2^m)`. -/
def tmA (m : ℕ) : Finset ℕ := (Finset.range (2^m)).filter fun i => Even (Nat.digits 2 i).sum
def tmB (m : ℕ) : Finset ℕ := (Finset.range (2^m)).filter fun i => Odd (Nat.digits 2 i).sum

/-! ## Binary digit sums -/

theorem digits_sum_bit0 (i : ℕ) :
    (Nat.digits 2 (2 * i)).sum = (Nat.digits 2 i).sum := by
  rcases eq_or_ne i 0 with rfl | hi
  · simp
  · rw [Nat.digits_two_eq_bits, Nat.bit0_bits i hi, List.map_cons, List.sum_cons,
      ← Nat.digits_two_eq_bits]
    show (0 : ℕ) + (Nat.digits 2 i).sum = (Nat.digits 2 i).sum
    exact zero_add _

theorem digits_sum_bit1 (i : ℕ) :
    (Nat.digits 2 (2 * i + 1)).sum = (Nat.digits 2 i).sum + 1 := by
  rw [Nat.digits_two_eq_bits, Nat.bit1_bits, List.map_cons, List.sum_cons,
    ← Nat.digits_two_eq_bits]
  show (1 : ℕ) + (Nat.digits 2 i).sum = (Nat.digits 2 i).sum + 1
  omega

/-- Adding a fresh top bit `2^m` to `i < 2^m` raises the digit sum by one. -/
theorem digits_sum_add_pow : ∀ m i : ℕ, i < 2 ^ m →
    (Nat.digits 2 (2 ^ m + i)).sum = (Nat.digits 2 i).sum + 1 := by
  intro m
  induction m with
  | zero =>
    intro i hi
    have hi0 : i = 0 := Nat.lt_one_iff.mp (by simpa using hi)
    subst hi0
    decide
  | succ m ih =>
    intro i hi
    rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have hj : j < 2 ^ m := by
        have h := hi
        rw [pow_succ] at h
        omega
      have hrw : 2 ^ (m + 1) + (j + j) = 2 * (2 ^ m + j) := by
        rw [pow_succ]; ring
      rw [hrw, digits_sum_bit0, ih j hj, ← two_mul j, digits_sum_bit0]
    · have hj : j < 2 ^ m := by
        have h := hi
        rw [pow_succ] at h
        omega
      have hrw : 2 ^ (m + 1) + (2 * j + 1) = 2 * (2 ^ m + j) + 1 := by
        rw [pow_succ]; ring
      rw [hrw, digits_sum_bit1, ih j hj, digits_sum_bit1]

/-! ## The Prouhet factorization -/

/-- Signed Thue–Morse generating sum `∑_{i < 2^m} u^{t(i)} X^i` in `ℤ[X]`. -/
noncomputable def F (m : ℕ) (u : ℤ) : ℤ[X] :=
  ∑ i ∈ Finset.range (2 ^ m), C (u ^ (Nat.digits 2 i).sum) * X ^ i

theorem F_succ (m : ℕ) (u : ℤ) :
    F (m + 1) u = (1 + C u * X ^ (2 ^ m)) * F m u := by
  have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ, mul_two]
  unfold F
  rw [h2, Finset.sum_range_add]
  have step : ∀ i ∈ Finset.range (2 ^ m),
      C (u ^ (Nat.digits 2 (2 ^ m + i)).sum) * X ^ (2 ^ m + i)
        = (C u * X ^ (2 ^ m)) * (C (u ^ (Nat.digits 2 i).sum) * X ^ i) := by
    intro i hi
    rw [digits_sum_add_pow m i (Finset.mem_range.mp hi)]
    rw [pow_succ, map_mul, pow_add]
    ring
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum]
  ring

theorem F_eq_prod (m : ℕ) (u : ℤ) :
    F m u = ∏ r ∈ Finset.range m, (1 + C u * X ^ (2 ^ r)) := by
  induction m with
  | zero => simp [F]
  | succ m ih =>
    rw [F_succ, Finset.prod_range_succ, ih]
    ring

/-- The generating polynomial of a finset of naturals. -/
noncomputable def gf (S : Finset ℕ) : ℤ[X] := ∑ a ∈ S, X ^ a

theorem tmB_eq_filter_not_even (m : ℕ) :
    tmB m = (Finset.range (2 ^ m)).filter fun i => ¬Even (Nat.digits 2 i).sum := by
  unfold tmB
  apply Finset.filter_congr
  intro i _
  exact Nat.not_even_iff_odd.symm

theorem F_eq_tm_sum (m : ℕ) (u : ℤ) :
    F m u = ∑ i ∈ tmA m, C (u ^ (Nat.digits 2 i).sum) * X ^ i
      + ∑ i ∈ tmB m, C (u ^ (Nat.digits 2 i).sum) * X ^ i := by
  have hB : (∑ i ∈ tmB m, C (u ^ (Nat.digits 2 i).sum) * X ^ i)
      = ∑ i ∈ (Finset.range (2 ^ m)).filter (fun i => ¬Even (Nat.digits 2 i).sum),
          C (u ^ (Nat.digits 2 i).sum) * X ^ i := by
    rw [tmB_eq_filter_not_even]
  unfold F tmA
  rw [hB, Finset.sum_filter_add_sum_filter_not]

theorem F_neg_one (m : ℕ) : F m (-1) = gf (tmA m) - gf (tmB m) := by
  unfold gf
  rw [F_eq_tm_sum]
  have hEv : ∑ i ∈ tmA m, C ((-1 : ℤ) ^ (Nat.digits 2 i).sum) * X ^ i
      = ∑ i ∈ tmA m, X ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    rw [Even.neg_one_pow hi'.2]
    simp
  have hNotEv : ∑ i ∈ tmB m, C ((-1 : ℤ) ^ (Nat.digits 2 i).sum) * X ^ i
      = -∑ i ∈ tmB m, X ^ i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    rw [Odd.neg_one_pow hi'.2]
    simp
  rw [hEv, hNotEv, sub_eq_add_neg]

theorem F_one (m : ℕ) : F m 1 = gf (tmA m) + gf (tmB m) := by
  unfold gf
  rw [F_eq_tm_sum]
  rw [show (∑ i ∈ tmA m, C ((1 : ℤ) ^ (Nat.digits 2 i).sum) * X ^ i)
        = ∑ i ∈ tmA m, X ^ i from
      Finset.sum_congr rfl (fun i _ => by simp),
    show (∑ i ∈ tmB m, C ((1 : ℤ) ^ (Nat.digits 2 i).sum) * X ^ i)
        = ∑ i ∈ tmB m, X ^ i from
      Finset.sum_congr rfl (fun i _ => by simp)]

/-- The punchline identity `F(-1)(X) · F(1)(X) = F(-1)(X²)`. -/
theorem F_mul (m : ℕ) : F m (-1) * F m 1 = (F m (-1)).comp (X ^ 2) := by
  rw [F_eq_prod, F_eq_prod, ← Finset.prod_mul_distrib, Polynomial.prod_comp]
  apply Finset.prod_congr rfl
  intro r _
  rw [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_pow_comp, Polynomial.one_comp]
  have e : ((X : ℤ[X]) ^ 2) ^ (2 ^ r) = X ^ (2 ^ (r + 1)) := by
    rw [← pow_mul, ← pow_succ']
  rw [e]
  simp only [map_neg, map_one]
  rw [pow_succ', two_mul, pow_add]
  ring

/-! ## Squaring the generating function -/

/-- The pair-sum generating polynomial of `S`. -/
noncomputable def e2 (S : Finset ℕ) : ℤ[X] := ∑ T ∈ S.powersetCard 2, X ^ (T.sum id)

theorem gf_comp_X_sq (S : Finset ℕ) :
    (gf S).comp (X ^ 2) = ∑ a ∈ S, X ^ (2 * a) := by
  unfold gf
  rw [Polynomial.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [Polynomial.X_pow_comp, ← pow_mul]

theorem sum_diag (S : Finset ℕ) :
    ∑ p ∈ S.diag, X ^ (p.1 + p.2) = (gf S).comp (X ^ 2) := by
  rw [gf_comp_X_sq]
  show ∑ p ∈ S.map ⟨Function.diag, Function.diag_injective⟩, X ^ (p.1 + p.2) = _
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a _
  show X ^ (a + a) = X ^ (2 * a)
  congr 1
  exact (two_mul a).symm

theorem sum_offDiag (S : Finset ℕ) :
    ∑ p ∈ S.offDiag, X ^ (p.1 + p.2) = 2 * e2 S := by
  have hmaps : ∀ p ∈ S.offDiag, ({p.1, p.2} : Finset ℕ) ∈ S.powersetCard 2 := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.insert_subset_iff.mpr ⟨hp.1, Finset.singleton_subset_iff.mpr hp.2.1⟩,
      Finset.card_pair hp.2.2⟩
  unfold e2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => X ^ (p.1 + p.2))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hTS, hT2⟩ := hT
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hT2
  have habS : a ∈ S ∧ b ∈ S := by
    have h := hTS
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff] at h
    exact h
  have hfib : S.offDiag.filter (fun p : ℕ × ℕ => ({p.1, p.2} : Finset ℕ) = {a, b})
      = {(a, b), (b, a)} := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨ha, hb, hne⟩, hpair⟩
      have h1 : p.1 = a ∨ p.1 = b := by
        have hm : p.1 ∈ ({a, b} : Finset ℕ) :=
          hpair ▸ Finset.mem_insert_self p.1 ({p.2} : Finset ℕ)
        simpa using hm
      have h2 : p.2 = a ∨ p.2 = b := by
        have hp2 : p.2 ∈ ({p.1, p.2} : Finset ℕ) := by
          rw [Finset.pair_comm]; exact Finset.mem_insert_self _ _
        have hm : p.2 ∈ ({a, b} : Finset ℕ) := hpair ▸ hp2
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
  show X ^ (a + b) + X ^ (b + a) = 2 * X ^ (a + b)
  rw [add_comm b a, ← two_mul]

theorem gf_sq (S : Finset ℕ) :
    (gf S) ^ 2 = (gf S).comp (X ^ 2) + 2 * e2 S := by
  have h1 : (gf S) ^ 2 = ∑ p ∈ S ×ˢ S, X ^ (p.1 + p.2) := by
    unfold gf
    rw [sq, Finset.sum_mul_sum]
    rw [← Finset.sum_product']
    apply Finset.sum_congr rfl
    intro p _
    rw [← pow_add]
  rw [h1, ← Finset.diag_union_offDiag S,
    Finset.sum_union (Finset.disjoint_diag_offDiag S), sum_diag S, sum_offDiag S]

/-! ## Coefficients count pair sums -/

theorem kSums_count (S : Finset ℕ) (d : ℕ) :
    (kSums S 2).count d = ((S.powersetCard 2).filter fun T => T.sum id = d).card := by
  unfold kSums
  rw [Multiset.count_eq_card_filter_eq, Multiset.filter_map, Multiset.card_map]
  suffices h : (S.powersetCard 2).filter ((fun x => d = x) ∘ fun T => T.sum id)
      = (S.powersetCard 2).filter fun T => T.sum id = d by
    rw [← Finset.filter_val, h]
    rfl
  apply Finset.filter_congr
  intro T _
  exact eq_comm

theorem e2_coeff (S : Finset ℕ) (d : ℕ) :
    (e2 S).coeff d = ((kSums S 2).count d : ℤ) := by
  rw [kSums_count]
  unfold e2
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow, Finset.sum_boole]
  norm_cast
  congr 1
  apply Finset.filter_congr
  intro T _
  exact eq_comm

/-! ## The main theorem -/

theorem tm_kSums_two (m : ℕ) : kSums (tmA m) 2 = kSums (tmB m) 2 := by
  have hsq : gf (tmA m) ^ 2 - (gf (tmA m)).comp (X ^ 2)
      = gf (tmB m) ^ 2 - (gf (tmB m)).comp (X ^ 2) := by
    have h : gf (tmA m) ^ 2 - gf (tmB m) ^ 2
        = (gf (tmA m)).comp (X ^ 2) - (gf (tmB m)).comp (X ^ 2) := by
      rw [sq_sub_sq, ← F_one m, ← F_neg_one m, mul_comm (F m 1) (F m (-1)),
        F_mul, F_neg_one m, Polynomial.sub_comp]
    linear_combination h
  have e2A : 2 * e2 (tmA m) = gf (tmA m) ^ 2 - (gf (tmA m)).comp (X ^ 2) := by
    rw [gf_sq, add_sub_cancel_left]
  have e2B : 2 * e2 (tmB m) = gf (tmB m) ^ 2 - (gf (tmB m)).comp (X ^ 2) := by
    rw [gf_sq, add_sub_cancel_left]
  have e2eq : e2 (tmA m) = e2 (tmB m) := by
    have h2 : (2 : ℤ[X]) * e2 (tmA m) = 2 * e2 (tmB m) := by
      rw [e2A, e2B, hsq]
    exact mul_left_cancel₀ two_ne_zero h2
  apply Multiset.ext.2
  intro d
  have hA := e2_coeff (tmA m) d
  have hB := e2_coeff (tmB m) d
  rw [e2eq] at hA
  exact Nat.cast_injective (hA.symm.trans hB)

/-! ## Cardinalities of the two halves -/

theorem card_tm (m : ℕ) (hm : 1 ≤ m) :
    (tmA m).card = 2 ^ (m - 1) ∧ (tmB m).card = 2 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base =>
    constructor
    · have h : tmA 1 = {0} := by decide
      rw [h]; simp
    · have h : tmB 1 = {1} := by decide
      rw [h]; simp
  | succ n hn ih =>
    obtain ⟨ihA, ihB⟩ := ih
    have hAe : tmA (n + 1) = tmA n ∪ (tmB n).map (addLeftEmbedding (2 ^ n)) := by
      unfold tmA
      rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by rw [pow_succ, mul_two],
        Finset.range_add, Finset.filter_union]
      congr 1
      rw [Finset.filter_map]
      congr 1
      unfold tmB
      apply Finset.filter_congr
      intro i hi
      simp only [Function.comp_apply, addLeftEmbedding_apply]
      rw [digits_sum_add_pow n i (Finset.mem_range.mp hi)]
      exact (Nat.even_add_one).trans Nat.not_even_iff_odd
    have hBe : tmB (n + 1) = tmB n ∪ (tmA n).map (addLeftEmbedding (2 ^ n)) := by
      unfold tmB
      rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by rw [pow_succ, mul_two],
        Finset.range_add, Finset.filter_union]
      congr 1
      rw [Finset.filter_map]
      congr 1
      unfold tmA
      apply Finset.filter_congr
      intro i hi
      simp only [Function.comp_apply, addLeftEmbedding_apply]
      rw [digits_sum_add_pow n i (Finset.mem_range.mp hi)]
      exact (Nat.odd_add_one).trans Nat.not_odd_iff_even
    have hdisjA : Disjoint (tmA n) ((tmB n).map (addLeftEmbedding (2 ^ n))) := by
      rw [Finset.disjoint_left]
      intro x hxA hxmap
      rw [Finset.mem_map] at hxmap
      obtain ⟨j, _, hjx⟩ := hxmap
      rw [tmA, Finset.mem_filter, Finset.mem_range] at hxA
      rw [← hjx, addLeftEmbedding_apply] at hxA
      omega
    have hdisjB : Disjoint (tmB n) ((tmA n).map (addLeftEmbedding (2 ^ n))) := by
      rw [Finset.disjoint_left]
      intro x hxB hxmap
      rw [Finset.mem_map] at hxmap
      obtain ⟨j, _, hjx⟩ := hxmap
      rw [tmB, Finset.mem_filter, Finset.mem_range] at hxB
      rw [← hjx, addLeftEmbedding_apply] at hxB
      omega
    constructor
    · rw [hAe, Finset.card_union_of_disjoint hdisjA, Finset.card_map, ihA, ihB]
      have hn1 : n + 1 - 1 = n := Nat.add_sub_cancel n 1
      rw [hn1, ← two_mul, ← pow_succ', Nat.sub_add_cancel hn]
    · rw [hBe, Finset.card_union_of_disjoint hdisjB, Finset.card_map, ihA, ihB]
      have hn1 : n + 1 - 1 = n := Nat.add_sub_cancel n 1
      rw [hn1, ← two_mul, ← pow_succ', Nat.sub_add_cancel hn]

/-! ## Transport to `ℤ` and failure of unique recoverability -/

/-- The coercion embedding `ℕ ↪ ℤ`. -/
def intEmb : ℕ ↪ ℤ := ⟨fun n => (n : ℤ), Nat.cast_injective⟩

theorem powersetCard_map_intEmb (S : Finset ℕ) (k : ℕ) :
    (S.map intEmb).powersetCard k
      = (S.powersetCard k).map ⟨fun T => T.map intEmb, Finset.map_injective intEmb⟩ := by
  rw [Finset.map_eq_image, Finset.powersetCard_eq_filter, Finset.powerset_image,
    Finset.filter_image]
  have h1 : (S.powerset.filter fun T => (T.image intEmb).card = k)
      = S.powerset.filter (·.card = k) := by
    apply Finset.filter_congr
    intro T _
    rw [Finset.card_image_of_injective _ intEmb.injective]
  rw [h1]
  rw [Finset.map_eq_image, Finset.powersetCard_eq_filter]
  apply Finset.image_congr
  intro T _
  exact (Finset.map_eq_image _ _).symm

theorem kSums_map_intEmb (S : Finset ℕ) (k : ℕ) :
    kSums (S.map intEmb) k = Multiset.map (fun n : ℕ => (n : ℤ)) (kSums S k) := by
  have hsum : ∀ T : Finset ℕ, (T.map intEmb).sum id = ((T.sum id : ℕ) : ℤ) := by
    intro T
    rw [Finset.sum_map]
    exact (Nat.cast_sum T (fun x => x)).symm
  unfold kSums
  rw [powersetCard_map_intEmb, Finset.map_val, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro T _
  exact hsum T

theorem zero_mem_tmA (m : ℕ) : (0 : ℕ) ∈ tmA m := by
  rw [tmA, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (pow_pos (by norm_num) m), by decide⟩

theorem zero_notMem_tmB (m : ℕ) : (0 : ℕ) ∉ tmB m := by
  rw [tmB, Finset.mem_filter]
  simp

theorem not_UR_two_pow (m : ℕ) (hm : 2 ≤ m) : ¬ UR ℤ 2 (2 ^ (m - 1)) := by
  intro hUR
  have hcard := card_tm m (by omega : 1 ≤ m)
  have hne : (tmA m).map intEmb ≠ (tmB m).map intEmb := by
    intro h
    have h0A : (0 : ℤ) ∈ (tmA m).map intEmb := by
      rw [Finset.mem_map]
      exact ⟨0, zero_mem_tmA m, rfl⟩
    have h0B : (0 : ℤ) ∈ (tmB m).map intEmb := h ▸ h0A
    rw [Finset.mem_map] at h0B
    obtain ⟨b, hb, hb0⟩ := h0B
    have hbz : b = 0 := Nat.cast_eq_zero.mp hb0
    subst hbz
    exact zero_notMem_tmB m hb
  exact hne (hUR _ _ (by rw [Finset.card_map, hcard.1]) (by rw [Finset.card_map, hcard.2])
    (by rw [kSums_map_intEmb, kSums_map_intEmb, tm_kSums_two]))

end JSP399
