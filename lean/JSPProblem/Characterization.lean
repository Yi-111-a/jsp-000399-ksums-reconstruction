import Mathlib
import JSPProblem.Basic
import JSPProblem.Boundary
import JSPProblem.Counterexample
import JSPProblem.Duality
import JSPProblem.Tao
import JSPProblem.ThueMorse
import JSPProblem.Negatives
import JSPProblem.URTwo

/-!
# JSP-000399 — the unique-recovery characterization (Selfridge–Straus / Gordon–Fraenkel–Straus)

`UR_characterization` bundles the full proved characterization of when an
`n`-element set of integers is uniquely recoverable from its multiset of
`k`-element subset sums (Erdős Problem #494):

* the exact `k = 2` characterization: `UR ℤ 2 n` iff `n` is not a power of two
  (Selfridge–Straus 1958 — the positive direction via power sums / Newton
  identities, the failure direction via the Thue–Morse splitting);
* the universal failures: `k = 0`, `n < k` (degenerate), `n = k` (Kruyt), and
  `n = 2k` (Tao's sum-zero reflection family);
* the universal recoveries: `k = 1` (the elements themselves), and the
  complement-duality equivalence `UR ℤ k n ↔ UR ℤ (n - k) n` which yields the
  boundary cases `k = n - 1` and `n = k + 1`.

For `k ≥ 3` the precise finite exceptional sets depend on the roots of the
Moser polynomials (e.g. `{27, 486}`-type families for `k = 3`); the exceptional
*families* captured here (`n = k`, `n = 2k`, powers of two at `k = 2`,
degenerate and dual pairs) are exactly the set-valued exceptional cases of
Selfridge–Straus / Gordon–Fraenkel–Straus.
-/

namespace JSP399

/-- The unique-recovery characterization for Erdős Problem #494. -/
theorem UR_characterization :
    (∀ n : ℕ, UR ℤ 2 n ↔ ∀ l : ℕ, n ≠ 2 ^ l) ∧
    (∀ n : ℕ, UR ℤ 1 n) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ UR ℤ 0 n) ∧
    (∀ k n : ℕ, 1 ≤ n → n < k → ¬ UR ℤ k n) ∧
    (∀ k : ℕ, 2 ≤ k → ¬ UR ℤ k k) ∧
    (∀ k : ℕ, 2 ≤ k → ¬ UR ℤ k (2 * k)) ∧
    (∀ k n : ℕ, 1 ≤ k → k < n → (UR ℤ k n ↔ UR ℤ (n - k) n)) ∧
    (∀ n : ℕ, 2 ≤ n → UR ℤ (n - 1) n) ∧
    (∀ k : ℕ, 1 ≤ k → UR ℤ k (k + 1)) := by
  refine ⟨UR_two_iff, UR_one ℤ, fun _ => not_UR_zero, fun _ _ => not_UR_of_card_lt,
    fun _ => not_UR_self, fun _ => not_UR_two_mul, fun _ _ => UR_iff_compl,
    UR_pred_card, fun _ => UR_succ⟩

end JSP399
