/-!
# Parity

The finished part of the example: every declaration here is proved, and all but one carry a doc
comment, so their plan entries need nothing but an id.
-/

namespace Example

/-- A natural number is even when it is twice some natural number. -/
def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k

/-- A natural number is odd when it is one more than twice some natural number. -/
def IsOdd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

/-- Zero is even. -/
theorem isEven_zero : IsEven 0 := ⟨0, rfl⟩

/-- One is odd. Filed here although the plan expects it in `Example.Odd`; `tracker lint` says so. -/
theorem isOdd_one : IsOdd 1 := ⟨0, rfl⟩

-- No doc comment on purpose: the plan keeps this node's `desc`.
theorem isEven_two_mul (k : Nat) : IsEven (2 * k) := ⟨k, rfl⟩

/-- The sum of two even numbers is even. -/
theorem IsEven.add {m n : Nat} (hm : IsEven m) (hn : IsEven n) : IsEven (m + n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  exact ⟨a + b, by omega⟩

/-- An even number plus one is odd. -/
theorem IsEven.add_one_odd {n : Nat} (h : IsEven n) : IsOdd (n + 1) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by omega⟩

end Example
