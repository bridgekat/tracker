/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numbers.Parity

/-!
# Odd numbers

The task in progress: one lemma is stated with `sorry`, and one the plan asks for is not written
yet.
-/

namespace Numbers

/-- An odd number plus one is even. -/
theorem IsOdd.add_one_even {n : Nat} (h : IsOdd n) : IsEven (n + 1) := by
  sorry

end Numbers
