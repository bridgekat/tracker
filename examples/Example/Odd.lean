import Example.Parity

/-!
# Odd numbers

The task in progress: one lemma is stated with `sorry`, and one the plan asks for is not written
yet.
-/

namespace Example

/-- An odd number plus one is even. -/
theorem IsOdd.add_one_even {n : Nat} (h : IsOdd n) : IsEven (n + 1) := by
  sorry

end Example
