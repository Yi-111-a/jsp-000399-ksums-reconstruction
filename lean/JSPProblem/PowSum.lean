import Mathlib
import JSPProblem.Basic

/-!
# Power-sum infrastructure for JSP-000399 (Erdős #494)

`psum A j` is the `j`-th power sum of a finset of rationals, and `psumk A k j`
is the `j`-th power sum of the multiset `kSums A k`.  The integer variants
`psumz` / `psumzk` view a `Finset ℤ` inside `ℚ`.
-/

namespace JSP399

/-- Power sum of degree `j` of a finset of rationals. -/
def psum (A : Finset ℚ) (j : ℕ) : ℚ := ∑ a ∈ A, a ^ j

/-- Power sum of degree `j` of the `k`-subset sums of `A`. -/
def psumk (A : Finset ℚ) (k j : ℕ) : ℚ :=
  ∑ T ∈ A.powersetCard k, (T.sum id) ^ j

/-- Power sum of degree `j` of a finset of integers, viewed in `ℚ`. -/
def psumz (A : Finset ℤ) (j : ℕ) : ℚ := ∑ a ∈ A, (a : ℚ) ^ j

/-- Power sum of degree `j` of the integer `k`-subset sums, viewed in `ℚ`. -/
def psumzk (A : Finset ℤ) (k j : ℕ) : ℚ :=
  ∑ T ∈ A.powersetCard k, ((T.sum id : ℤ) : ℚ) ^ j

end JSP399
