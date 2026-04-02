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

/-!
## Lemmas from `Init.Data.SInt.Lemmas` (up to line 725)
-/

theorem ISize64.toInt.inj {x y : ISize64} (h : x.toInt = y.toInt) : x = y :=
  ISize64.toBitVec.inj (BitVec.eq_of_toInt_eq h)
theorem ISize64.toInt_inj {x y : ISize64} : x.toInt = y.toInt ↔ x = y :=
  ⟨ISize64.toInt.inj, fun h => h ▸ rfl⟩

@[simp, int_toBitVec] theorem ISize64.toBitVec_neg (x : ISize64) : (-x).toBitVec = -x.toBitVec := (rfl)

@[simp] theorem ISize64.toBitVec_zero : toBitVec 0 = 0#64 := (rfl)

theorem ISize64.toBitVec_one : (1 : ISize64).toBitVec = 1#64 := (rfl)

@[simp, int_toBitVec] theorem ISize64.toBitVec_ofInt (i : Int) : (ofInt i).toBitVec = BitVec.ofInt _ i := (rfl)

@[simp] protected theorem ISize64.neg_zero : -(0 : ISize64) = 0 := (rfl)

@[simp] theorem ISize64.toInt_ofInt {n : Int} : toInt (ofInt n) = n.bmod ISize64.size := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt]

@[simp] theorem ISize64.toInt_ofNat' {n : Nat} : toInt (ofNat n) = (n : Int).bmod ISize64.size := by
  rw [toInt, toBitVec_ofNat', BitVec.toInt_ofNat']

theorem ISize64.toInt_ofNat {n : Nat} : toInt (no_index (OfNat.ofNat n)) = (n : Int).bmod ISize64.size := by
  rw [toInt, toBitVec_ofNat, BitVec.toInt_ofNat]

theorem ISize64.toInt_ofInt_of_le {n : Int} (hn : -2^63 ≤ n) (hn' : n < 2^63) : toInt (ofInt n) = n := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt_eq_self (by decide) hn hn']

theorem ISize64.neg_ofInt {n : Int} : -ofInt n = ofInt (-n) :=
  toBitVec.inj (by simp [BitVec.ofInt_neg])

theorem ISize64.ofInt_eq_ofNat {n : Nat} : ofInt n = ofNat n := toBitVec.inj (by simp)

theorem ISize64.neg_ofNat {n : Nat} : -ofNat n = ofInt (-n) := by
  rw [← neg_ofInt, ofInt_eq_ofNat]

theorem ISize64.toNatClampNeg_ofNat_of_lt {n : Nat} (h : n < 2 ^ 63) : toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, ← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega), Int.toNat_natCast]

theorem ISize64.toInt_ofNat_of_lt {n : Nat} (h : n < 2 ^ 63) : toInt (ofNat n) = n := by
  rw [← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega)]

theorem ISize64.toInt_neg_ofNat_of_le {n : Nat} (h : n ≤ 2^63) : toInt (-ofNat n) = -n := by
  rw [← ofInt_eq_ofNat, neg_ofInt, toInt_ofInt_of_le (by omega) (by omega)]

theorem ISize64.toInt_zero : toInt 0 = 0 := by
  rw [toInt_ofNat, ISize64.size]; decide

theorem ISize64.toInt_minValue : ISize64.minValue.toInt = -2^63 := (rfl)

theorem ISize64.toInt_maxValue : ISize64.maxValue.toInt = 2 ^ 63 - 1 := (rfl)

@[simp] theorem ISize64.toNatClampNeg_minValue : ISize64.minValue.toNatClampNeg = 0 := (rfl)

@[simp] theorem ISize64.toNat_toInt (x : ISize64) : x.toInt.toNat = x.toNatClampNeg := (rfl)

@[simp] theorem ISize64.toInt_toBitVec (x : ISize64) : x.toBitVec.toInt = x.toInt := (rfl)

@[simp, int_toBitVec] theorem ISize64.toBitVec_toInt8 (x : ISize64) :
    x.toInt8.toBitVec = x.toBitVec.signExtend 8 := (rfl)
@[simp, int_toBitVec] theorem ISize64.toBitVec_toInt16 (x : ISize64) :
    x.toInt16.toBitVec = x.toBitVec.signExtend 16 := (rfl)
@[simp, int_toBitVec] theorem ISize64.toBitVec_toInt32 (x : ISize64) :
    x.toInt32.toBitVec = x.toBitVec.signExtend 32 := (rfl)
@[simp, int_toBitVec] theorem ISize64.toBitVec_toInt64 (x : ISize64) :
    x.toInt64.toBitVec = x.toBitVec := (rfl)
@[simp, int_toBitVec] theorem ISize64.toBitVec_toISize (x : ISize64) :
    x.toISize.toBitVec = x.toBitVec.signExtend System.Platform.numBits := (rfl)

theorem ISize64.toInt_lt (x : ISize64) : x.toInt < 2 ^ 63 :=
  Int.lt_of_mul_lt_mul_left BitVec.two_mul_toInt_lt (by decide)

theorem ISize64.le_toInt (x : ISize64) : -2 ^ 63 ≤ x.toInt :=
  Int.le_of_mul_le_mul_left BitVec.le_two_mul_toInt (by decide)

theorem ISize64.toInt_le (x : ISize64) : x.toInt ≤ ISize64.maxValue.toInt :=
  Int.le_of_lt_add_one x.toInt_lt

theorem ISize64.minValue_le_toInt (x : ISize64) : ISize64.minValue.toInt ≤ x.toInt := x.le_toInt

theorem ISize64.toNatClampNeg_lt (x : ISize64) : x.toNatClampNeg < 2 ^ 63 :=
  (Int.toNat_lt' (by decide)).2 x.toInt_lt

@[simp] theorem ISize64.toInt_toInt8 (x : ISize64) : x.toInt8.toInt = x.toInt.bmod (2 ^ 8) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem ISize64.toInt_toInt16 (x : ISize64) : x.toInt16.toInt = x.toInt.bmod (2 ^ 16) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem ISize64.toInt_toInt32 (x : ISize64) : x.toInt32.toInt = x.toInt.bmod (2 ^ 32) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem ISize64.toInt_toInt64 (x : ISize64) : x.toInt64.toInt = x.toInt := (rfl)
@[simp] theorem ISize64.toInt_toISize (x : ISize64) :
    x.toISize.toInt = x.toInt.bmod (2 ^ System.Platform.numBits) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem ISize64.ofBitVec_toBitVec (x : ISize64) : ISize64.ofBitVec x.toBitVec = x := (rfl)

@[simp] theorem ISize64.ofBitVec_int8ToBitVec (x : Int8) :
    ISize64.ofBitVec (x.toBitVec.signExtend 64) = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofBitVec_int16ToBitVec (x : Int16) :
    ISize64.ofBitVec (x.toBitVec.signExtend 64) = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofBitVec_int32ToBitVec (x : Int32) :
    ISize64.ofBitVec (x.toBitVec.signExtend 64) = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofBitVec_int64ToBitVec (x : Int64) :
    ISize64.ofBitVec x.toBitVec = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofBitVec_iSizeToBitVec (x : ISize) :
    ISize64.ofBitVec (x.toBitVec.signExtend 64) = x.toISize64 := (rfl)

@[simp] theorem ISize64.toBitVec_ofIntLE (x : Int) (h₁ h₂) :
    (ISize64.ofIntLE x h₁ h₂).toBitVec = BitVec.ofInt 64 x := (rfl)

@[simp] theorem ISize64.toInt_bmod (x : ISize64) :
    x.toInt.bmod 18446744073709551616 = x.toInt :=
  Int.bmod_eq_of_le x.le_toInt x.toInt_lt

-- Alias used by simp in other contexts
@[simp] theorem ISize64.toInt_bmod_size (x : ISize64) :
    x.toInt.bmod ISize64.size = x.toInt :=
  ISize64.toInt_bmod x

@[simp] theorem BitVec.ofInt_iSize64ToInt (x : ISize64) :
    BitVec.ofInt 64 x.toInt = x.toBitVec :=
  BitVec.eq_of_toInt_eq (by simp)

@[simp] theorem ISize64.ofIntLE_toInt (x : ISize64) :
    ISize64.ofIntLE x.toInt x.minValue_le_toInt x.toInt_le = x :=
  ISize64.toBitVec.inj (by simp)

@[simp] theorem ISize64.ofInt_toInt (x : ISize64) : ISize64.ofInt x.toInt = x :=
  ISize64.toBitVec.inj (by simp)

@[simp] theorem ISize64.ofInt_int8ToInt (x : Int8) : ISize64.ofInt x.toInt = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofInt_int16ToInt (x : Int16) : ISize64.ofInt x.toInt = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofInt_int32ToInt (x : Int32) : ISize64.ofInt x.toInt = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofInt_int64ToInt (x : Int64) : ISize64.ofInt x.toInt = x.toISize64 := by
  show ISize64.ofBitVec (BitVec.ofInt 64 x.toBitVec.toInt) = ⟨x.toBitVec⟩
  congr 1; exact BitVec.ofInt_toInt ..
@[simp] theorem ISize64.ofInt_iSizeToInt (x : ISize) : ISize64.ofInt x.toInt = x.toISize64 := (rfl)

@[simp] theorem ISize64.toInt_ofIntLE {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂).toInt = x := by
  rw [ofIntLE, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]

theorem ISize64.ofIntLE_eq_ofIntTruncate {x : Int} {h₁ h₂} :
    (ofIntLE x h₁ h₂) = ofIntTruncate x := by
  rw [ofIntTruncate, dif_pos h₁, dif_pos h₂]

theorem ISize64.ofIntLE_eq_ofInt {n : Int} (h₁ h₂) : ISize64.ofIntLE n h₁ h₂ = ISize64.ofInt n := (rfl)

theorem ISize64.toInt_ofIntTruncate {x : Int} (h₁ : ISize64.minValue.toInt ≤ x)
    (h₂ : x ≤ ISize64.maxValue.toInt) : (ISize64.ofIntTruncate x).toInt = x := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toInt_ofIntLE]

@[simp] theorem ISize64.ofIntTruncate_toInt (x : ISize64) : ISize64.ofIntTruncate x.toInt = x :=
  ISize64.toInt.inj (toInt_ofIntTruncate x.minValue_le_toInt x.toInt_le)

theorem ISize64.ofInt_eq_iff_bmod_eq_toInt (a : Int) (b : ISize64) :
    ISize64.ofInt a = b ↔ a.bmod (2 ^ 64) = b.toInt := by
  simp [← ISize64.toInt_inj]
