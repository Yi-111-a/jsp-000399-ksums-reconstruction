import Mathlib
import JSPProblem.Basic
import JSPProblem.Boundary
import JSPProblem.Counterexample
import JSPProblem.Duality
import JSPProblem.ThueMorse

/-!
# JSP-000399 — negative results and duality corollaries

Collects a few corollaries of the main development:

* `not_UR_two_pow'`: `UR ℤ 2 n` fails at *every* power of two `n = 2^l`
  (the case `l = 0`, i.e. `n = 1 < 2`, is degenerate; `l ≥ 1` is the
  Thue–Morse counterexample `not_UR_two_pow` at `m = l + 1`).
* `UR_iff_compl`: complement duality as an `↔`.  **Note:** a `1 ≤ k`
  hypothesis is necessary — at `k = 0, n = 1` the bare statement would read
  `UR ℤ 0 1 ↔ UR ℤ 1 1`, but `UR ℤ 0 1` fails (`not_UR_zero`) while
  `UR ℤ 1 1` holds (`UR_one`).
* `UR_succ`: `n = k + 1` always recovers, as the dual of `k = 1`.
* `UR_pred'`: the `k = n - 1` boundary case restated.
-/

namespace JSP399

/-- `n = 2^l` fails UR for `k = 2` at every `l`. -/
theorem not_UR_two_pow' (l : ℕ) : ¬ UR ℤ 2 (2 ^ l) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simpa using not_UR_of_card_lt (n := 1) (k := 2) (by norm_num) (by norm_num)
  · have h := not_UR_two_pow (l + 1) (by omega)
    rwa [Nat.add_sub_cancel] at h

/-- Duality as an iff (apply `UR_compl` in both directions).
The `1 ≤ k` side condition is needed for the reverse direction so that
`n - k < n`; without it the statement is false already at `k = 0, n = 1`. -/
theorem UR_iff_compl {k n : ℕ} (hk : 1 ≤ k) (hn : k < n) :
    UR ℤ k n ↔ UR ℤ (n - k) n := by
  refine ⟨UR_compl hn, fun h => ?_⟩
  have h2 := UR_compl (Nat.sub_lt (by omega : 0 < n) (by omega : 0 < k)) h
  rwa [Nat.sub_sub_self (by omega : k ≤ n)] at h2

/-- `n = k + 1` always recovers (dual of `k = 1`). -/
theorem UR_succ {k : ℕ} (hk : 1 ≤ k) : UR ℤ k (k + 1) := by
  have h := UR_compl (by omega : 1 < k + 1) (UR_one ℤ (k + 1))
  rwa [Nat.add_sub_cancel] at h

/-- `k = n - 1` restated (boundary, for convenience). -/
theorem UR_pred' {n : ℕ} (hn : 2 ≤ n) : UR ℤ (n - 1) n := UR_pred_card n hn

end JSP399
