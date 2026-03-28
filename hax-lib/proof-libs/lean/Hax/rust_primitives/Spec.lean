import Std.Do
import Hax.rust_primitives.RustM

open Std.Do

/-

# Specs

-/

theorem Triple.of_hypothesis {α : Type} {f : RustM α} {Q : α → Assertion _} {p : Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓ r => Q r ⦄)
    (hp : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓? r => Q r → ⌜ p ⌝ ⦄) :
    p := sorry

structure Spec {α}
    (requires : RustM Prop)
    (ensures : α → RustM Prop)
    (f : RustM α) where
  pureRequires : {p : Prop // ⦃ ⌜ True ⌝ ⦄ requires ⦃ ⇓r => ⌜ r = p ⌝ ⦄}
  pureEnsures : {p : α → Prop // pureRequires.val → ∀ a, ⦃ ⌜ True ⌝ ⦄ ensures a ⦃ ⇓r => ⌜ r = p a ⌝ ⦄}
  contract : ⦃ ⌜ pureRequires.val ⌝ ⦄ f ⦃ ⇓r => ⌜ pureEnsures.val r ⌝ ⦄
