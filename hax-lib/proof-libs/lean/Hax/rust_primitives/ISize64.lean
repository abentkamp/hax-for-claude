import Hax.MissingLean
import Hax.rust_primitives.USize64
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.SInt

/-!
# ISize64

We define a type `ISize64` to represent Rust's `isize` type. It is simply a copy of `Int64`.
This file aims to collect all definitions, lemmas, and type class instances about `Int64` from
Lean's standard library and to state them for `ISize64`.

The regular `ISize` type does not work for us because of https://github.com/cryspen/hax/issues/1702.
-/

/-- A copy of `Int64`, which we use to represent Rust's `isize` type. -/
structure ISize64 where ofBitVec :: toBitVec : BitVec 64

/-- The number of distinct values representable by `ISize64`, that is, `2^64 = 18446744073709551616`. -/
@[reducible] def ISize64.size : Nat := Int64.size

theorem ISize64.toBitVec.inj : {x y : ISize64} → x.toBitVec = y.toBitVec → x = y
  | ⟨_⟩, ⟨_⟩, rfl => rfl

/-- Converts an arbitrary-precision integer to `ISize64`, wrapping on overflow or underflow. -/
def ISize64.ofInt (i : @& Int) : ISize64 := ⟨BitVec.ofInt 64 i⟩

/-- Converts a natural number to `ISize64`, wrapping around to negative numbers on overflow. -/
def ISize64.ofNat (n : @& Nat) : ISize64 := ⟨BitVec.ofNat 64 n⟩

abbrev Int.toISize64 := ISize64.ofInt

abbrev Nat.toISize64 := ISize64.ofNat

/-- Converts an `ISize64` to an arbitrary-precision integer that denotes the same number. -/
def ISize64.toInt (i : ISize64) : Int := i.toBitVec.toInt

/-- Converts an `ISize64` to a natural number, mapping all negative numbers to `0`. -/
@[suggest_for ISize64.toNat, inline] def ISize64.toNatClampNeg (i : ISize64) : Nat := i.toInt.toNat

/-- Converts an `ISize64` to an 8-bit signed integer by truncating its bitvector representation. -/
def ISize64.toInt8 (a : ISize64) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩

/-- Converts an `ISize64` to a 16-bit signed integer by truncating its bitvector representation. -/
def ISize64.toInt16 (a : ISize64) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩

/-- Converts an `ISize64` to a 32-bit signed integer by truncating its bitvector representation. -/
def ISize64.toInt32 (a : ISize64) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩

/-- Converts an `ISize64` to a 64-bit signed integer. -/
def ISize64.toInt64 (a : ISize64) : Int64 := ⟨⟨a.toBitVec⟩⟩

/-- Converts an `ISize64` to a word-sized signed integer. -/
def ISize64.toISize (a : ISize64) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩

/-- Converts an 8-bit signed integer to `ISize64`. -/
def Int8.toISize64 (a : Int8) : ISize64 := ⟨a.toBitVec.signExtend 64⟩

/-- Converts a 16-bit signed integer to `ISize64`. -/
def Int16.toISize64 (a : Int16) : ISize64 := ⟨a.toBitVec.signExtend 64⟩

/-- Converts a 32-bit signed integer to `ISize64`. -/
def Int32.toISize64 (a : Int32) : ISize64 := ⟨a.toBitVec.signExtend 64⟩

/-- Converts a 64-bit signed integer to `ISize64`. -/
def Int64.toISize64 (a : Int64) : ISize64 := ⟨a.toBitVec⟩

/-- Converts a word-sized signed integer to `ISize64`. -/
def ISize.toISize64 (a : ISize) : ISize64 := ⟨a.toBitVec.signExtend 64⟩

/-- Negates an `ISize64`. Usually accessed via the `-` prefix operator. -/
def ISize64.neg (i : ISize64) : ISize64 := ⟨-i.toBitVec⟩

instance : ToString ISize64 where
  toString i := toString i.toInt
instance : Repr ISize64 where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom ISize64 := ⟨⟩

instance : Hashable ISize64 where
  hash i := UInt64.ofInt i.toInt

instance ISize64.instOfNat {n} : OfNat ISize64 n := ⟨ISize64.ofNat n⟩
instance ISize64.instNeg : Neg ISize64 where
  neg := ISize64.neg

/-- The largest number that `ISize64` can represent: `2^63 - 1 = 9223372036854775807`. -/
abbrev ISize64.maxValue : ISize64 := 9223372036854775807

/-- The smallest number that `ISize64` can represent: `-2^63 = -9223372036854775808`. -/
abbrev ISize64.minValue : ISize64 := -9223372036854775808

/-- Constructs an `ISize64` from an `Int` that is known to be in bounds. -/
@[inline]
def ISize64.ofIntLE (i : Int) (_hl : ISize64.minValue.toInt ≤ i) (_hr : i ≤ ISize64.maxValue.toInt) : ISize64 :=
  ISize64.ofInt i

/-- Constructs an `ISize64` from an `Int`, clamping if the value is too small or too large. -/
def ISize64.ofIntTruncate (i : Int) : ISize64 :=
  if hl : ISize64.minValue.toInt ≤ i then
    if hr : i ≤ ISize64.maxValue.toInt then
      ISize64.ofIntLE i hl hr
    else
      ISize64.minValue
  else
    ISize64.minValue

protected def ISize64.add (a b : ISize64) : ISize64 := ⟨a.toBitVec + b.toBitVec⟩
protected def ISize64.sub (a b : ISize64) : ISize64 := ⟨a.toBitVec - b.toBitVec⟩
protected def ISize64.mul (a b : ISize64) : ISize64 := ⟨a.toBitVec * b.toBitVec⟩
protected def ISize64.div (a b : ISize64) : ISize64 := ⟨BitVec.sdiv a.toBitVec b.toBitVec⟩
protected def ISize64.pow (x : ISize64) (n : Nat) : ISize64 :=
  match n with
  | 0 => 1
  | n + 1 => ISize64.mul (ISize64.pow x n) x
protected def ISize64.mod (a b : ISize64) : ISize64 := ⟨BitVec.srem a.toBitVec b.toBitVec⟩

protected def ISize64.land (a b : ISize64) : ISize64 := ⟨a.toBitVec &&& b.toBitVec⟩
protected def ISize64.lor (a b : ISize64) : ISize64 := ⟨a.toBitVec ||| b.toBitVec⟩
protected def ISize64.xor (a b : ISize64) : ISize64 := ⟨a.toBitVec ^^^ b.toBitVec⟩
protected def ISize64.shiftLeft (a b : ISize64) : ISize64 := ⟨a.toBitVec <<< (b.toBitVec.smod 64)⟩
protected def ISize64.shiftRight (a b : ISize64) : ISize64 := ⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 64)⟩
protected def ISize64.complement (a : ISize64) : ISize64 := ⟨~~~a.toBitVec⟩
protected def ISize64.abs (a : ISize64) : ISize64 := ⟨a.toBitVec.abs⟩

def ISize64.decEq (a b : ISize64) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m)
      (fun h => isTrue (h ▸ rfl))
      (fun h => isFalse (fun h' => ISize64.noConfusion h' (fun h' => absurd h' h)))

protected def ISize64.lt (a b : ISize64) : Prop := a.toBitVec.slt b.toBitVec
protected def ISize64.le (a b : ISize64) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited ISize64 where
  default := 0

instance : Add ISize64         := ⟨ISize64.add⟩
instance : Sub ISize64         := ⟨ISize64.sub⟩
instance : Mul ISize64         := ⟨ISize64.mul⟩
instance : Pow ISize64 Nat     := ⟨ISize64.pow⟩
instance : Mod ISize64         := ⟨ISize64.mod⟩
instance : Div ISize64         := ⟨ISize64.div⟩
instance : LT ISize64          := ⟨ISize64.lt⟩
instance : LE ISize64          := ⟨ISize64.le⟩
instance : Complement ISize64  := ⟨ISize64.complement⟩
instance : AndOp ISize64       := ⟨ISize64.land⟩
instance : OrOp ISize64        := ⟨ISize64.lor⟩
instance : XorOp ISize64         := ⟨ISize64.xor⟩
instance : ShiftLeft ISize64   := ⟨ISize64.shiftLeft⟩
instance : ShiftRight ISize64  := ⟨ISize64.shiftRight⟩
instance : DecidableEq ISize64 := ISize64.decEq

/-- Converts `true` to `1` and `false` to `0`. -/
def Bool.toISize64 (b : Bool) : ISize64 := if b then 1 else 0

def ISize64.decLt (a b : ISize64) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

def ISize64.decLe (a b : ISize64) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

attribute [instance_reducible, instance] ISize64.decLt ISize64.decLe

instance : Max ISize64 := maxOfLe
instance : Min ISize64 := minOfLe

/-- Converts an `ISize64` to a `UInt8`. -/
def ISize64.toUInt8 (a : ISize64) : UInt8 := a.toNatClampNeg.toUInt8

/-- Converts an `ISize64` to a `UInt16`. -/
def ISize64.toUInt16 (a : ISize64) : UInt16 := a.toNatClampNeg.toUInt16

/-- Converts an `ISize64` to a `UInt32`. -/
def ISize64.toUInt32 (a : ISize64) : UInt32 := a.toNatClampNeg.toUInt32

/-- Converts an `ISize64` to a `UInt64`. -/
def ISize64.toUInt64 (a : ISize64) : UInt64 := ⟨a.toBitVec⟩

/-- Converts an `ISize64` to a `USize`. -/
def ISize64.toUSize (a : ISize64) : USize := a.toNatClampNeg.toUSize

/-- Converts a `UInt8` to `ISize64`. -/
def UInt8.toISize64 (a : UInt8) : ISize64 := ISize64.ofInt a.toNat

/-- Converts a `UInt16` to `ISize64`. -/
def UInt16.toISize64 (a : UInt16) : ISize64 := ISize64.ofInt a.toNat

/-- Converts a `UInt32` to `ISize64`. -/
def UInt32.toISize64 (a : UInt32) : ISize64 := ISize64.ofInt a.toNat

/-- Converts a `UInt64` to `ISize64`. -/
def UInt64.toISize64 (a : UInt64) : ISize64 := ⟨a.toBitVec⟩

/-- Converts a `USize` to `ISize64`. -/
def USize.toISize64 (a : USize) : ISize64 := ISize64.ofInt a.toNat

/-- Converts an `ISize64` to a `USize64`. -/
def ISize64.toUSize64 (a : ISize64) : USize64 := USize64.ofInt a.toInt

/-- Converts a `USize64` to `ISize64`. -/
def USize64.toISize64 (a : USize64) : ISize64 := ⟨a.toBitVec⟩

/-!
## Theorems from `declare_int_theorems`
-/

open Std Lean in
set_option autoImplicit true in
declare_int_theorems ISize64 64
