import JSPProblem.Basic
import JSPProblem.Boundary
import JSPProblem.Counterexample
import JSPProblem.Duality
import JSPProblem.Tao
import JSPProblem.ThueMorse

/-!
# JSP-000399 — Erdős Problem 494 (Selfridge–Straus / Gordon–Fraenkel–Straus)

A finite set `A` yields the multiset `kSums A k` of all sums of `k` distinct
elements of `A`.  The problem asks when `A` is uniquely recoverable from this
multiset together with `|A|`.

This development (see `JSP399` namespace across the imported modules) proves:

* `UR`/`kSums` definitions matching the classical formulation.
* Positive recovery: `k = 1` always; boundary cases `n ≤ 1`, `k = n - 1`.
* Failure of recovery: `k = 2, n = 4` (explicit Thue–Morse pair
  `{0,3,5,6}` vs `{1,2,4,7}`); `k = 2, n = 2^m` in general; Tao's
  `n = 2k` family (sum-zero `A` vs `-A`); the degenerate cases `n < k`,
  `k = 0`, `n = k`; complement duality `k ↔ n - k`.

The full characterization (for `k = 2`: UR iff `n` is not a power of two;
for `k ≥ 3`: UR for all sufficiently large `n` outside finite exceptional
sets such as `{27, 486}` for `k = 3`) is the content of Selfridge–Straus 1958
and Gordon–Fraenkel–Straus 1962; the open gaps are documented per-lemma.
-/
