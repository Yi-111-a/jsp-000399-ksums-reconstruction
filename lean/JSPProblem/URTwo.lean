import Mathlib
import JSPProblem.Basic
import JSPProblem.PowSum
import JSPProblem.PowSumTwo
import JSPProblem.Newton
import JSPProblem.Transport
import JSPProblem.Negatives
import JSPProblem.ThueMorse
import JSPProblem.Counterexample

/-!
# The `k = 2` characterization (Selfridge–Straus)

`UR ℤ 2 n` holds iff `n` is not a power of two.
* Failure direction: `not_UR_two_pow'` (Thue–Morse for `l ≥ 1`, degenerate `l = 0`).
* Recovery direction: equal 2-sum multisets give equal power sums via the
  transfer identity `psumk_two`; since `n ≠ 2^{j-1}` the coefficient never
  vanishes, so all power sums `psum A j = psum B j` for `j ≤ n` agree, and
  `finset_eq_of_psum_eq` (Newton identities) yields `A = B`.
-/

namespace JSP399

theorem UR_two_of_forall_ne_pow_two {n : ℕ} (hn : ∀ l : ℕ, n ≠ 2 ^ l) :
    UR ℤ 2 n := by
  intro A B hA hB hks
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · rw [Finset.card_eq_zero] at hA hB
    rw [hA, hB]
  have hcardAB : A.card = B.card := by
    rw [hA, hB]
  -- transport the integer sets to ℚ
  have hcardQ : (A.map ratCastEmb).card = (B.map ratCastEmb).card := by
    rw [card_map_ratCast, card_map_ratCast, hcardAB]
  -- the ℚ power sums of the 2-subset sums agree
  have hkQ : ∀ j : ℕ, psumk (A.map ratCastEmb) 2 j = psumk (B.map ratCastEmb) 2 j := by
    intro j
    rw [psumk_map_ratCast, psumk_map_ratCast]
    exact psumzk_eq_of_kSums_eq hks
  -- the coefficient `n - 2^{j-1}` never vanishes in ℚ
  have hcoef : ∀ j : ℕ, 1 ≤ j → ((A.map ratCastEmb).card : ℚ) ≠ 2 ^ (j - 1) := by
    intro j hj h
    rw [card_map_ratCast, hA] at h
    have h' : (n : ℚ) = ((2 ^ (j - 1) : ℕ) : ℚ) := by
      rw [h]
      norm_cast
    have h'' : n = 2 ^ (j - 1) := Nat.cast_injective h'
    exact hn (j - 1) h''
  -- strong induction: all power sums up to `n` agree on the ℚ-images
  have hps : ∀ j ∈ Finset.Icc 1 (A.map ratCastEmb).card,
      psum (A.map ratCastEmb) j = psum (B.map ratCastEmb) j := by
    intro j
    induction j using Nat.strongRecOn with
    | _ j ih =>
      intro hj
      rw [Finset.mem_Icc] at hj
      refine psum_eq_of_psumk_two_eq hcardQ hj.1 (hcoef j hj.1) (hkQ j) ?_
      intro r hr
      rw [Finset.mem_Ioo] at hr
      exact ih r hr.2 (Finset.mem_Icc.mpr ⟨hr.1, hr.2.le.trans hj.2⟩)
  have himg : A.map ratCastEmb = B.map ratCastEmb :=
    finset_eq_of_psum_eq hcardQ hps
  exact finset_eq_of_map_ratCast_eq himg

/-- Selfridge–Straus, `k = 2`: an `n`-element set of integers is uniquely
recoverable from its multiset of pair sums iff `n` is not a power of two. -/
theorem UR_two_iff (n : ℕ) : UR ℤ 2 n ↔ ∀ l : ℕ, n ≠ 2 ^ l := by
  constructor
  · intro hUR l hl
    exact not_UR_two_pow' l (hl ▸ hUR)
  · exact UR_two_of_forall_ne_pow_two

end JSP399
