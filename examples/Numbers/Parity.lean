/-!
# Parity

The finished part of the example: every declaration here is proved, and all but one carry a doc
comment, so their plan entries need nothing but an id.
-/

namespace Numbers

/-- A natural number is even when it is twice some natural number. -/
def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k

/-- A natural number is odd when it is one more than twice some natural number. -/
def IsOdd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

/-- Zero is even. -/
theorem isEven_zero : IsEven 0 := ⟨0, rfl⟩

/-- One is odd. Filed here although the plan expects it in `Numbers.Odd`; `tracker lint` says so. -/
theorem isOdd_one : IsOdd 1 := ⟨0, rfl⟩

-- No doc comment on purpose: the plan keeps this declaration's `desc`.
theorem isEven_two_mul (k : Nat) : IsEven (2 * k) := ⟨k, rfl⟩

/-- Doubling distributes over a sum. No plan names this helper; it is a declaration all the same,
so `status` counts it and `graph --all` draws it. -/
theorem two_mul_add_two_mul (a b : Nat) : 2 * a + 2 * b = 2 * (a + b) := by omega

/-- The sum of two even numbers is even. -/
theorem IsEven.add {m n : Nat} (hm : IsEven m) (hn : IsEven n) : IsEven (m + n) := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  exact ⟨a + b, two_mul_add_two_mul a b⟩

/-- An even number plus one is odd. -/
theorem IsEven.add_one_odd {n : Nat} (h : IsEven n) : IsOdd (n + 1) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by omega⟩

end Numbers
