import MaleyLean.PaperStatements

namespace MaleyLean

/--
Constructive core no-generators theorem.

This avoids classical negation elimination by taking the same-act fact
explicitly as an equality hypothesis.
-/
theorem no_generators_same_act
  {α : Type}
  (S : System α)
  (T : Redescription α α)
  (a : α) :
  ¬ standing S a → standing S (T a) → T a = a → False :=
by
  intro h_fail h_gen hEq
  have hA : standing S a := by
    simpa [hEq] using h_gen
  exact h_fail hA

/--
Constructive paper-facing replacement in same-act form.
-/
theorem PaperNoGeneratorsStatementConstructive
  {α : Type}
  (S : System α)
  (T : Redescription α α)
  (a : α) :
  ¬ standing S a → standing S (T a) → T a = a → False :=
by
  exact no_generators_same_act S T a

end MaleyLean
