import Mathlib
import JSPProblem.PowSum

/-!
# Newton's identities: the first `n` power sums determine an `n`-element finset of rationals

We prove `finset_eq_of_psum_eq`: if `A` and `B` are finsets of rationals of the same
cardinality whose power sums `psum A j = ∑ a ∈ A, a ^ j` agree for `1 ≤ j ≤ A.card`,
then `A = B`.

The proof uses Mathlib's Newton identities for multivariate polynomials
(`MvPolynomial.mul_esymm_eq_sum`), evaluated at the elements of the finset via
`MvPolynomial.aeval`.  This shows that the elementary symmetric functions
`Multiset.esymm A.val k` of `A` are determined by the first `k` power sums.  Vieta's
formula `Multiset.prod_X_sub_C_coeff` then identifies `A` and `B` as the root
multisets of the same polynomial `∏ a ∈ A, (X - C a)`.
-/

namespace JSP399

open Finset Nat Polynomial

/-- Newton's identity evaluated at the elements of a finset `A` of rationals:
`k • eₖ(A)` equals an alternating sum of products `eᵢ(A) · pⱼ(A)`. -/
theorem mul_esymm_eq_sum_eval (A : Finset ℚ) (k : ℕ) :
    (k : ℚ) * Multiset.esymm A.val k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * Multiset.esymm A.val a.1 * psum A a.2 := by
  classical
  have hval : Finset.univ.val.map (Subtype.val : ↥A → ℚ) = A.val := by
    rw [Finset.univ_eq_attach, Finset.attach_val, Multiset.attach_map_val]
  have hpsum (j : ℕ) : MvPolynomial.aeval (Subtype.val : ↥A → ℚ)
      (MvPolynomial.psum ↥A ℚ j) = psum A j := by
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
    exact Finset.sum_coe_sort A (fun a : ℚ => a ^ j)
  have h := congrArg (⇑(MvPolynomial.aeval (Subtype.val : ↥A → ℚ)))
    (MvPolynomial.mul_esymm_eq_sum ↥A ℚ k)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, hval, hpsum] at h
  exact h

/-- The elementary symmetric functions of `A.val` up to order `A.card` are
determined by the first `A.card` power sums. -/
theorem esymm_eq_of_psum_eq {A B : Finset ℚ} (hcard : A.card = B.card)
    (h : ∀ j ∈ Finset.Icc 1 A.card, psum A j = psum B j) :
    ∀ k ≤ A.card, Multiset.esymm A.val k = Multiset.esymm B.val k := by
  intro k
  refine Nat.strong_induction_on k fun k ih => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · intro _; simp
  · intro hk
    have hA := mul_esymm_eq_sum_eval A k
    have hB := mul_esymm_eq_sum_eval B k
    have hsum : (∑ a ∈ antidiagonal k with a.1 < k,
          (-1) ^ a.1 * Multiset.esymm A.val a.1 * psum A a.2) =
        ∑ a ∈ antidiagonal k with a.1 < k,
          (-1) ^ a.1 * Multiset.esymm B.val a.1 * psum B a.2 := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_filter] at ha
      have had : a.1 + a.2 = k := mem_antidiagonal.mp ha.1
      have ha1 : a.1 < k := ha.2
      rw [ih a.1 ha1 ((Nat.le_of_lt ha1).trans hk),
        h a.2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    rw [hsum] at hA
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hkpos.ne'
    exact mul_left_cancel₀ hk0 (hA.trans hB.symm)

/-- If two finsets of rationals of the same cardinality have equal power sums for
`1 ≤ j ≤ card`, they are equal. -/
theorem finset_eq_of_psum_eq {A B : Finset ℚ} (hcard : A.card = B.card)
    (h : ∀ j ∈ Finset.Icc 1 A.card, psum A j = psum B j) : A = B := by
  have hesymm := esymm_eq_of_psum_eq hcard h
  have hAB : Multiset.card A.val = Multiset.card B.val := hcard
  -- The monic polynomials `∏ a ∈ A, (X - a)` and `∏ b ∈ B, (X - b)` are equal,
  -- since their coefficients are (up to sign) the elementary symmetric functions.
  have hpoly : (A.val.map fun a => (X : ℚ[X]) - C a).prod =
      (B.val.map fun b => (X : ℚ[X]) - C b).prod := by
    apply Polynomial.ext
    intro k
    by_cases hk : k ≤ Multiset.card A.val
    · rw [Multiset.prod_X_sub_C_coeff A.val hk,
        Multiset.prod_X_sub_C_coeff B.val (hAB ▸ hk)]
      show (-1) ^ (A.card - k) * Multiset.esymm A.val (A.card - k) =
        (-1) ^ (B.card - k) * Multiset.esymm B.val (B.card - k)
      rw [hcard, hesymm (B.card - k) (by omega)]
    · replace hk : Multiset.card A.val < k := Nat.lt_of_not_ge hk
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (by rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]; exact hk)]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (by rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, ← hAB]; exact hk)]
  -- The root multiset of `∏ a ∈ M, (X - a)` is `M` itself.
  have hroots := congrArg Polynomial.roots hpoly
  rw [Polynomial.roots_multiset_prod_X_sub_C,
    Polynomial.roots_multiset_prod_X_sub_C] at hroots
  exact Finset.val_inj.mp hroots

end JSP399
