import Numbers.Parity

/-!
# A refuted proposal

The plan proposed "every natural number is even". It is false, and the plan records that with the
counterexample.
-/

namespace Numbers

/-- The proposition the plan proposed: every natural number is even. -/
def everyEven : Prop := ∀ n, IsEven n

/-- The proposal is false: `1` is not even. -/
theorem not_everyEven : ¬ everyEven := fun h => by
  obtain ⟨k, hk⟩ := h 1
  omega

end Numbers
