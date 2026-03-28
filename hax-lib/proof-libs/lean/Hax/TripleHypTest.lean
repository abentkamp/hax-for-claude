import Hax.rust_primitives.RustM
import Std.Do.PostCond
import Std.Do.Triple.Basic
import Hax.MissingLean.Std.Do.Triple.Basic

open Std.Do

/-- A monad is "grounded" if a noThrow triple with a constant postcondition implies that postcondition.
    This is the key property needed to extract propositions from Hoare triples. -/
class GroundedWP (m : Type → Type) [Monad m] (ps : outParam PostShape) [WPMonad m ps] : Prop where
  grounded : ∀ {α : Type} (f : m α) (p : Prop),
    ⦃ ⌜ True ⌝ ⦄ f ⦃ PostCond.noThrow (fun (_ : α) => ⌜ p ⌝) ⦄ → p

instance : GroundedWP RustM (.except Error .pure) where
  grounded f p h := by
    simp only [Triple, SPred.entails] at h
    cases f with
    | ok v   => exact h trivial
    | fail e => exact absurd (h trivial) id
    | div    => exact absurd (h trivial) id

theorem triple_in_hypothesis {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] [GroundedWP m ps]
    {α : Type} {f : m α} {Q : α → Assertion ps} {p : Prop}
    (h  : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓ r => Q r ⦄)
    (hp : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓? r => Q r → ⌜ p ⌝ ⦄) :
    p := by
  apply GroundedWP.grounded f p
  have hconj := Triple.and f h hp
  have h2 := Triple.of_entails_left _ _ _ f hconj SPred.and_self.mpr
  apply Triple.of_entails_right ⌜True⌝ _ _ f h2
  exact ⟨fun r => SPred.imp_elim_r, ExceptConds.false_and⟩
