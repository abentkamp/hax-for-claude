import Hax.Tactic.Init
import Hax.Tactic.SpecSet
import Hax.MissingLean.Init.While
import Std.Tactic.Do

open Std.Do
open Std.Tactic

/-
# Monadic encoding

The encoding is based on the `RustM` monad: all rust computations are wrapped
in the monad, representing the fact that they are not total.

It borrows some definitions from the Aeneas project
(https://github.com/AeneasVerif/aeneas/)

-/

/--
  (Aeneas) Error cases
-/
inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
   | undef: Error
deriving Repr, BEq, DecidableEq
open Error

deriving instance Repr, BEq, DecidableEq for Except

/--
  RustM monad (corresponding to Aeneas's `Result` monad), representing
  possible results of rust computations.

  Defined as `ExceptT Error Option`, i.e. `Option (Except Error α)`.
  The `Option` layer models divergence and the `Except Error` layer models
  Rust panics.
-/
def RustM (α : Type) := ExceptT Error Option α

namespace RustM

instance {α : Type} [Repr α] : Repr (RustM α) := inferInstanceAs (Repr (Option (Except Error α)))
instance {α : Type} [BEq α] : BEq (RustM α) := inferInstanceAs (BEq (Option (Except Error α)))
instance {α : Type} [DecidableEq α] : DecidableEq (RustM α) := inferInstanceAs (DecidableEq (Option (Except Error α)))
instance {α : Type} : Inhabited (RustM α) := inferInstanceAs (Inhabited (Option (Except Error α)))

instance instMonad : Monad RustM := inferInstanceAs (Monad (ExceptT Error Option))
instance instLawfulMonad : LawfulMonad RustM := inferInstanceAs (LawfulMonad (ExceptT Error Option))

@[reducible, match_pattern] def ok {α : Type} (v : α) : RustM α := some (.ok v)
@[reducible, match_pattern] def fail {α : Type} (e : Error) : RustM α := some (.error e)
@[reducible, match_pattern] def div {α : Type} : RustM α := none

def ofOption {α : Type} (x : Option α) (e : Error) : RustM α := match x with
  | .some v => pure v
  | .none => .fail e

@[reducible]
def isOk {α : Type} (x : RustM α) : Bool := match x with
| .ok _ => true
| _ => false

@[reducible, specset bv, hax_bv_decide]
def of_isOk {α : Type} (x : RustM α) (h : RustM.isOk x) : α :=
  match x with
  | .ok v => v

@[simp, spec]
def ok_of_isOk {α : Type} (v : α) (h : isOk (ok v)) : (ok v).of_isOk h = v := by rfl

instance instWP : WP RustM (.except Error (.except PUnit .pure)) :=
  inferInstanceAs (WP (ExceptT Error Option) _)
instance instWPMonad : WPMonad RustM (.except Error (.except PUnit .pure)) :=
  inferInstanceAs (WPMonad (ExceptT Error Option) _)

section Order

open Lean.Order

/- These instances are required to use `partial_fixpoint` in the `RustM` monad. -/

instance {α : Type} : PartialOrder (RustM α) := inferInstanceAs (PartialOrder (ExceptT Error Option α))
instance {α : Type} : CCPO (RustM α) := inferInstanceAs (CCPO (ExceptT Error Option α))
instance : MonoBind RustM := inferInstanceAs (MonoBind (ExceptT Error Option))

open Lean Order in
/-- `Loop.MonoLoopCombinator` is used to implement while loops in `RustM`: -/
instance {β : Type} (f : Unit → β → RustM (ForInStep β)) : Loop.MonoLoopCombinator f := {
  mono := by
    unfold Loop.loopCombinator
    repeat monotonicity
}

end Order

end RustM
