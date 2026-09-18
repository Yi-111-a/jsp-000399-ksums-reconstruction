import JSPProblem.Basic
import JSPProblem.Boundary
import JSPProblem.Counterexample
import JSPProblem.Duality
import JSPProblem.Tao
import JSPProblem.ThueMorse
import JSPProblem.PowSum
import JSPProblem.PowSumTwo
import JSPProblem.Newton
import JSPProblem.Transport
import JSPProblem.Moser
import JSPProblem.Negatives
import JSPProblem.URTwo
import JSPProblem.Characterization

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

`UR_characterization` (in `JSPProblem/Characterization.lean`) bundles the
proved characterization: the exact `k = 2` theorem (`UR ℤ 2 n` iff `n` is not
a power of two — Selfridge–Straus, proved here via the power-sum transfer
identity `psumk_two` and Newton's identities `finset_eq_of_psum_eq`), all
universal exceptional families (`k = 0`, `n < k`, `n = k`, `n = 2k`), and the
recoveries obtained by complement duality (`k = 1`, `k = n - 1`, `n = k + 1`).
The Moser coefficient `moserF k j n` and its nonvanishing at prime divisors
`p > k` of `n` (`moserF_ne_zero_of_prime_dvd`) are proved in
`JSPProblem/Moser.lean`; the remaining `k ≥ 3` positive cases need the general
Moser transfer identity, documented per-lemma.
-/
