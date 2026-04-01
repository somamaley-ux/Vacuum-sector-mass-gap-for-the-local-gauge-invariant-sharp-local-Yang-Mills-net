import MaleyLean.Core
import MaleyLean.InvariantBundle
import MaleyLean.EnvelopeInvariants

namespace MaleyLean

/-
A stronger object language for admissible transport:
transport moves are licensed relative to a scope.
-/
structure ScopedTransportAction (α : Type) where
  Scope : Type
  Move : Scope → Type
  act : {s : Scope} → Move s → α → α

/-
Every scope-preserving endomap is realized by some licensed scoped transport move.
This links the old predicate-level interface to the stronger action language.
-/
def realizes_scope_preserving
  {α : Type}
  (A : ScopedTransportAction α)
  (scope_preserving : (α → α) → Prop) : Prop :=
  ∀ C : α → α,
    scope_preserving C →
    ∃ s : A.Scope, ∃ m : A.Move s, A.act m = C

/-
Licensed scoped transport preserves each invariant in the bundle pointwise.
This is the stronger, object-language transport condition.
-/
def scoped_transport_preserves_invariants
  {α : Type}
  (A : ScopedTransportAction α)
  (B : InvariantBundle α) : Prop :=
  ∀ s : A.Scope,
    ∀ m : A.Move s,
      ∀ a : α,
        ∀ i : B.Ix,
          B.inv i a = B.inv i (A.act m a)

/-
From the stronger object language, recover the existing primitive-looking interface:
scope-preserving maps preserve the invariant bundle pointwise.
-/
theorem scope_preserving_invariant_transport_of_scoped_action
  {α : Type}
  (A : ScopedTransportAction α)
  (B : InvariantBundle α)
  (scope_preserving : (α → α) → Prop)
  (h_realizes :
    realizes_scope_preserving
      A
      scope_preserving)
  (h_pres :
    scoped_transport_preserves_invariants
      A
      B) :
  scope_preserving_invariant_transport_interface
    B
    scope_preserving := by
  intro a C hscope i
  rcases h_realizes C hscope with ⟨s, m, hm⟩
  rw [← hm]
  exact h_pres s m a i

/-
The stronger object language also recovers the target-level transport interface.
-/
theorem scope_preserving_target_transport_of_scoped_action
  {α : Type}
  (A : ScopedTransportAction α)
  (B : InvariantBundle α)
  (scope_preserving : (α → α) → Prop)
  (h_realizes :
    realizes_scope_preserving
      A
      scope_preserving)
  (h_pres :
    scoped_transport_preserves_invariants
      A
      B) :
  scope_preserving_target_transport
    B
    scope_preserving := by
  exact
    scope_preserving_target_transport_of_invariant_transport
      B
      scope_preserving
      (scope_preserving_invariant_transport_of_scoped_action
        A
        B
        scope_preserving
        h_realizes
        h_pres)

end MaleyLean
