import MaleyLean.PaperStatements

namespace MaleyLean

theorem desired_bridge_shape
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h1 : ∀ a, QD a → standing S a)
  (h2 : ∀ a, standing S a → QD a) :
  ∀ a, QD a ↔ standing S a :=
by
  intro a
  constructor
  · intro h
    exact h1 a h
  · intro h
    exact h2 a h

end MaleyLean
