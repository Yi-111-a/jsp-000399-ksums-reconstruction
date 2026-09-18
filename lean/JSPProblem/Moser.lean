import Mathlib
import JSPProblem.Basic
import JSPProblem.PowSum

/-!
# Moser polynomials for JSP-000399 (Selfridge–Straus layer)

The Moser coefficient

  `F_{k,j}(n) = ∑_{p=1}^{k} (-1)^{p-1} p^{j-1} * C(n, k-p)`

is the coefficient of the `j`-th power sum `psum A j` in the expansion of
`psumk A k j = ∑_{T ∈ A.powersetCard k} (∑ a ∈ T, a)^j` as a polynomial in the
power sums `psum A i`, `1 ≤ i ≤ j` (Selfridge–Straus 1958).  Its key arithmetic
property: if a prime `p > k` divides `n`, then `F_{k,j}(n) ≠ 0`, which is the
sufficient-condition core of the Selfridge–Straus theorem.
-/

namespace JSP399

/-- The Moser coefficient `F_{k,j}(n) = ∑_{p=1}^{k} (-1)^{p-1} p^{j-1} C(n, k-p)`. -/
def moserF (k j n : ℕ) : ℚ :=
  ∑ p ∈ Finset.Icc 1 k, (-1 : ℚ) ^ (p + 1) * (p : ℚ) ^ (j - 1) * (n.choose (k - p) : ℚ)

/-- Integer version, for congruence arguments. -/
def moserFz (k j n : ℕ) : ℤ :=
  ∑ p ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (p + 1) * (p : ℤ) ^ (j - 1) * (n.choose (k - p) : ℤ)

/-- `F_{2,j}(n) = n - 2^{j-1}`. -/
theorem moserF_two (j n : ℕ) : moserF 2 j n = (n : ℚ) - 2 ^ (j - 1) := by
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  unfold moserF
  rw [hIcc, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  norm_num [Nat.choose_one_right]
  ring

/-- The rational and integer Moser coefficients agree under the cast `ℤ → ℚ`. -/
theorem moserF_eq_cast (k j n : ℕ) : moserF k j n = (moserFz k j n : ℚ) := by
  unfold moserF moserFz
  rw [Int.cast_sum]
  exact Finset.sum_congr rfl fun p _ => by push_cast; ring

/-- If `p` is prime, `p ∣ n` and `1 ≤ m < p`, then `p ∣ C(n, m)`.
This is the divisibility heart of the Selfridge–Straus argument: from
`C(n,m) * m = n * C(n-1, m-1)` and `p ∤ m` one gets `p ∣ C(n,m)`. -/
theorem prime_dvd_choose {p n m : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hm : 1 ≤ m) (hmp : m < p) : p ∣ n.choose m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.choose_eq_zero_of_lt hm]
    exact dvd_zero p
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    have hmul : (n + 1).choose (m + 1) * (m + 1) = (n + 1) * n.choose m :=
      (Nat.add_one_mul_choose_eq n m).symm
    have hdvd : p ∣ (n + 1).choose (m + 1) * (m + 1) :=
      hmul ▸ dvd_mul_of_dvd_left hpn _
    rcases hp.dvd_mul.mp hdvd with h | h
    · exact h
    · have hle : p ≤ m + 1 := Nat.le_of_dvd (Nat.succ_pos m) h
      omega

/-- If a prime `p > k` divides `n`, then `F_{k,j}(n) ≠ 0` (Selfridge–Straus
sufficient-condition core).  Modulo `p`, every summand indexed by `q < k`
vanishes (since `p ∣ C(n, k-q)`), leaving `F_{k,j}(n) ≡ (-1)^{k+1} k^{j-1}`,
which is nonzero mod `p`. -/
theorem moserF_ne_zero_of_prime_dvd {k n j p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hkp : k < p) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    moserF k j n ≠ 0 := by
  have hz : moserFz k j n ≠ 0 := by
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    -- hkp : b + 1 < p
    have hsmall : (p : ℤ) ∣ ∑ q ∈ Finset.Icc 1 b,
        (-1 : ℤ) ^ (q + 1) * (q : ℤ) ^ (j - 1) * (n.choose (b + 1 - q) : ℤ) := by
      apply Finset.dvd_sum
      intro q hq
      rw [Finset.mem_Icc] at hq
      apply dvd_mul_of_dvd_right
      apply Int.natCast_dvd_natCast.mpr
      exact prime_dvd_choose hp hpn (by omega) (by omega)
    have hbig : ¬ (p : ℤ) ∣
        (-1 : ℤ) ^ ((b + 1) + 1) * ((b + 1 : ℕ) : ℤ) ^ (j - 1) := by
      intro h
      have h2 : p ∣ ((-1 : ℤ) ^ ((b + 1) + 1) * ((b + 1 : ℕ) : ℤ) ^ (j - 1)).natAbs :=
        Int.natCast_dvd.mp h
      have habs : ((-1 : ℤ) ^ ((b + 1) + 1) * ((b + 1 : ℕ) : ℤ) ^ (j - 1)).natAbs
          = (b + 1) ^ (j - 1) := by
        have e1 : ((-1 : ℤ)).natAbs = 1 := by decide
        rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow, e1, one_pow, one_mul,
          Int.natAbs_natCast]
      rw [habs] at h2
      have h3 : p ∣ b + 1 := hp.dvd_of_dvd_pow h2
      have h4 : p ≤ b + 1 := Nat.le_of_dvd (by omega) h3
      omega
    intro hz0
    have hsplit : moserFz (b + 1) j n =
        (∑ q ∈ Finset.Icc 1 b,
          (-1 : ℤ) ^ (q + 1) * (q : ℤ) ^ (j - 1) * (n.choose (b + 1 - q) : ℤ))
          + (-1 : ℤ) ^ ((b + 1) + 1) * ((b + 1 : ℕ) : ℤ) ^ (j - 1) := by
      unfold moserFz
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ b + 1)]
      congr 1
      rw [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [hsplit] at hz0
    apply hbig
    have hbeq : (-1 : ℤ) ^ ((b + 1) + 1) * ((b + 1 : ℕ) : ℤ) ^ (j - 1)
        = -(∑ q ∈ Finset.Icc 1 b, (-1 : ℤ) ^ (q + 1) * (q : ℤ) ^ (j - 1) *
            (n.choose (b + 1 - q) : ℤ)) := by
      linear_combination hz0
    rw [hbeq]
    exact dvd_neg.mpr hsmall
  intro h
  rw [moserF_eq_cast, Int.cast_eq_zero] at h
  exact hz h

end JSP399
