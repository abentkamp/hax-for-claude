-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Prelude.lean
-- Target: Hax/MissingLean/Init/Prelude.lean
-- ──────────────────────────────────────────────────────────────────────

abbrev USize64.size : Nat := 18446744073709551616

structure USize64 where
  /--
  Creates a `USize64` from a `BitVec 64`. This function is overridden with a native implementation.
  -/
  ofBitVec ::
  /--
  Unpacks a `USize64` into a `BitVec 64`. This function is overridden with a native implementation.
  -/
  toBitVec : BitVec 64

def USize64.ofNatLT (n : @& Nat) (h : LT.lt n USize64.size) : USize64 where
  toBitVec := BitVec.ofNatLT n h

def USize64.decEq (a b : USize64) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m)
      (fun h => isTrue (h ▸ rfl))
      (fun h => isFalse (fun h' => USize64.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq USize64 := USize64.decEq

instance : Inhabited USize64 where
  default := USize64.ofNatLT 0 (of_decide_eq_true rfl)

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/UInt/BasicAux.lean
-- Target: Hax/MissingLean/Init/Data/UInt/BasicAux.lean
-- ──────────────────────────────────────────────────────────────────────

def USize64.toFin (x : USize64) : Fin USize64.size := x.toBitVec.toFin

def USize64.ofNat (n : @& Nat) : USize64 := ⟨BitVec.ofNat 64 n⟩

def USize64.ofNatTruncate (n : Nat) : USize64 :=
  if h : n < USize64.size then
    USize64.ofNatLT n h
  else
    USize64.ofNatLT (USize64.size - 1) (by decide)

abbrev Nat.toUSize64 := USize64.ofNat

def USize64.toNat (n : USize64) : Nat := n.toBitVec.toNat

def USize64.toUInt8 (a : USize64) : UInt8 := a.toNat.toUInt8

def USize64.toUInt16 (a : USize64) : UInt16 := a.toNat.toUInt16

def USize64.toUInt32 (a : USize64) : UInt32 := a.toNat.toUInt32

def UInt8.toUSize64 (a : UInt8) : USize64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

def UInt16.toUSize64 (a : UInt16) : USize64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

def UInt32.toUSize64 (a : UInt32) : USize64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

instance USize64.instOfNat : OfNat USize64 n := ⟨USize64.ofNat n⟩

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/UInt/Basic.lean
-- Target: Hax/MissingLean/Init/Data/UInt/Basic.lean
-- ──────────────────────────────────────────────────────────────────────

@[inline] def USize64.ofFin (a : Fin USize64.size) : USize64 := ⟨⟨a⟩⟩

def USize64.ofInt (x : Int) : USize64 := ofNat (x % 2 ^ 64).toNat

protected def USize64.add (a b : USize64) : USize64 := ⟨a.toBitVec + b.toBitVec⟩

protected def USize64.sub (a b : USize64) : USize64 := ⟨a.toBitVec - b.toBitVec⟩

protected def USize64.mul (a b : USize64) : USize64 := ⟨a.toBitVec * b.toBitVec⟩

protected def USize64.div (a b : USize64) : USize64 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩

protected def USize64.pow (x : USize64) (n : Nat) : USize64 :=
  match n with
  | 0 => 1
  | n + 1 => USize64.mul (USize64.pow x n) x

protected def USize64.mod (a b : USize64) : USize64 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩

@[deprecated USize64.mod (since := "2024-09-23")]
protected def USize64.modn (a : USize64) (n : Nat) : USize64 := ⟨Fin.modn a.toFin n⟩

protected def USize64.land (a b : USize64) : USize64 := ⟨a.toBitVec &&& b.toBitVec⟩

protected def USize64.lor (a b : USize64) : USize64 := ⟨a.toBitVec ||| b.toBitVec⟩

protected def USize64.xor (a b : USize64) : USize64 := ⟨a.toBitVec ^^^ b.toBitVec⟩

protected def USize64.shiftLeft (a b : USize64) : USize64 := ⟨a.toBitVec <<< (USize64.mod b 64).toBitVec⟩

protected def USize64.shiftRight (a b : USize64) : USize64 := ⟨a.toBitVec >>> (USize64.mod b 64).toBitVec⟩

protected def USize64.lt (a b : USize64) : Prop := a.toBitVec < b.toBitVec

protected def USize64.le (a b : USize64) : Prop := a.toBitVec ≤ b.toBitVec

instance : Add USize64       := ⟨USize64.add⟩

instance : Sub USize64       := ⟨USize64.sub⟩

instance : Mul USize64       := ⟨USize64.mul⟩

instance : Pow USize64 Nat   := ⟨USize64.pow⟩

instance : Mod USize64       := ⟨USize64.mod⟩

instance : HMod USize64 Nat USize64 := ⟨USize64.modn⟩

instance : Div USize64       := ⟨USize64.div⟩

instance : LT USize64        := ⟨USize64.lt⟩

instance : LE USize64        := ⟨USize64.le⟩

protected def USize64.complement (a : USize64) : USize64 := ⟨~~~a.toBitVec⟩

protected def USize64.neg (a : USize64) : USize64 := ⟨-a.toBitVec⟩

instance : Complement USize64 := ⟨USize64.complement⟩

instance : Neg USize64 := ⟨USize64.neg⟩

instance : AndOp USize64     := ⟨USize64.land⟩

instance : OrOp USize64      := ⟨USize64.lor⟩

instance : XorOp USize64       := ⟨USize64.xor⟩

instance : ShiftLeft USize64  := ⟨USize64.shiftLeft⟩

instance : ShiftRight USize64 := ⟨USize64.shiftRight⟩

def Bool.toUSize64 (b : Bool) : USize64 := if b then 1 else 0

@[instance_reducible]
def USize64.decLt (a b : USize64) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))

@[instance_reducible]
def USize64.decLe (a b : USize64) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))

attribute [instance] USize64.decLt USize64.decLe

instance : Max USize64 := maxOfLe

instance : Min USize64 := minOfLe

def USize64.toUSize (a : USize64) : USize := a.toNat.toUSize

def USize.toUSize64 (a : USize) : USize64 :=
  USize64.ofNatLT a.toBitVec.toNat (Nat.lt_of_lt_of_le a.toBitVec.isLt USize.size_le)

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/SInt/Basic.lean
-- Target: Hax/MissingLean/Init/Data/SInt/Basic_Int128.lean
-- ──────────────────────────────────────────────────────────────────────

set_option autoImplicit true

structure ISize64 where
  ofUSize64 ::
  /--
  Converts an 64-bit signed integer into the 64-bit unsigned integer that is its two's complement
  encoding.
  -/
  toUSize64 : USize64

instance : Hashable Int8 where
  hash i := i.toUInt8.toUSize64

instance : Hashable Int16 where
  hash i := i.toUInt16.toUSize64

instance : Hashable Int32 where
  hash i := i.toUInt32.toUSize64

abbrev ISize64.size : Nat := 18446744073709551616

@[inline] def ISize64.toBitVec (x : ISize64) : BitVec 64 := x.toUSize64.toBitVec

theorem ISize64.toBitVec.inj : {x y : ISize64} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

@[inline] def USize64.toISize64 (i : USize64) : ISize64 := ISize64.ofUSize64 i

def ISize64.ofInt (i : @& Int) : ISize64 := ⟨⟨BitVec.ofInt 64 i⟩⟩

def ISize64.ofNat (n : @& Nat) : ISize64 := ⟨⟨BitVec.ofNat 64 n⟩⟩

abbrev Int.toISize64 := ISize64.ofInt

abbrev Nat.toISize64 := ISize64.ofNat

def ISize64.toInt (i : ISize64) : Int := i.toBitVec.toInt

@[suggest_for ISize64.toNat, inline] def ISize64.toNatClampNeg (i : ISize64) : Nat := i.toInt.toNat

@[inline] def ISize64.ofBitVec (b : BitVec 64) : ISize64 := ⟨⟨b⟩⟩

def ISize64.toInt8 (a : ISize64) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩

def ISize64.toInt16 (a : ISize64) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩

def ISize64.toInt32 (a : ISize64) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩

def Int8.toISize64 (a : Int8) : ISize64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩

def Int16.toISize64 (a : Int16) : ISize64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩

def Int32.toISize64 (a : Int32) : ISize64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩

def ISize64.neg (i : ISize64) : ISize64 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString ISize64 where
  toString i := toString i.toInt

instance : Repr ISize64 where
  reprPrec i prec := reprPrec i.toInt prec

instance : ReprAtom ISize64 := ⟨⟩

instance : Hashable ISize64 where
  hash i := i.toUSize64

instance ISize64.instOfNat : OfNat ISize64 n := ⟨ISize64.ofNat n⟩

instance ISize64.instNeg : Neg ISize64 where
  neg := ISize64.neg

abbrev ISize64.maxValue : ISize64 := 9223372036854775807

abbrev ISize64.minValue : ISize64 := -9223372036854775808

@[inline]
def ISize64.ofIntLE (i : Int) (_hl : ISize64.minValue.toInt ≤ i) (_hr : i ≤ ISize64.maxValue.toInt) : ISize64 :=
  ISize64.ofInt i

def ISize64.ofIntTruncate (i : Int) : ISize64 :=
  if hl : ISize64.minValue.toInt ≤ i then
    if hr : i ≤ ISize64.maxValue.toInt then
      ISize64.ofIntLE i hl hr
    else
      ISize64.minValue
  else
    ISize64.minValue

protected def ISize64.add (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩

protected def ISize64.sub (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩

protected def ISize64.mul (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩

protected def ISize64.div (a b : ISize64) : ISize64 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩

protected def ISize64.pow (x : ISize64) (n : Nat) : ISize64 :=
  match n with
  | 0 => 1
  | n + 1 => ISize64.mul (ISize64.pow x n) x

protected def ISize64.mod (a b : ISize64) : ISize64 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩

protected def ISize64.land (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩

protected def ISize64.lor (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩

protected def ISize64.xor (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩

protected def ISize64.shiftLeft (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 64)⟩⟩

protected def ISize64.shiftRight (a b : ISize64) : ISize64 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 64)⟩⟩

protected def ISize64.complement (a : ISize64) : ISize64 := ⟨⟨~~~a.toBitVec⟩⟩

protected def ISize64.abs (a : ISize64) : ISize64 := ⟨⟨a.toBitVec.abs⟩⟩

def ISize64.decEq (a b : ISize64) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => ISize64.noConfusion h' (fun h' => absurd h' h))

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

def Bool.toISize64 (b : Bool) : ISize64 := if b then 1 else 0

@[instance_reducible]
def ISize64.decLt (a b : ISize64) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

@[instance_reducible]
def ISize64.decLe (a b : ISize64) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

attribute [instance] ISize64.decLt ISize64.decLe

instance : Max ISize64 := maxOfLe

instance : Min ISize64 := minOfLe

def ISize.toISize64 (a : ISize) : ISize64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩

def ISize64.toISize (a : ISize64) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩

instance : Hashable ISize where
  hash i := i.toUSize.toUSize64

-- ──────────────────────────────────────────────────────────────────────
-- Source: Lean/ToExpr.lean
-- Target: Hax/MissingLean/Lean/ToExpr.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean

instance : ToExpr USize64 where
  toTypeExpr := mkConst ``USize64
  toExpr a :=
    let r := mkRawNatLit a.toNat
    mkApp3 (.const ``OfNat.ofNat [0]) (mkConst ``USize64) r
      (.app (.const ``USize64.instOfNat []) r)

instance : ToExpr ISize64 where
  toTypeExpr := mkConst ``ISize64
  toExpr i := if 0 ≤ i then
    mkNat i.toNatClampNeg
  else
    mkApp3 (.const ``Neg.neg [0]) (.const ``ISize64 []) (.const ``ISize64.instNeg [])
      (mkNat (-(i.toInt)).toNat)
where
  mkNat (n : Nat) : Expr :=
    let r := mkRawNatLit n
    mkApp3 (.const ``OfNat.ofNat [0]) (.const ``ISize64 []) r
        (.app (.const ``ISize64.instOfNat []) r)

-- ──────────────────────────────────────────────────────────────────────
-- Source: Lean/Meta/Tactic/Simp/BuiltinSimprocs/UInt.lean
-- Target: Hax/MissingLean/Lean/Tactic/Simp/BuiltinSimpProcs/UInt.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean Meta Simp

macro "declare_uint_simprocs_ext" typeName:ident : command =>
let ofNat := typeName.getId ++ `ofNat
let ofNatLT := mkIdent (typeName.getId ++ `ofNatLT)
let toNat := mkIdent (typeName.getId ++ `toNat)
let fromExpr := mkIdent `fromExpr
`(
namespace $typeName

def $fromExpr (e : Expr) : SimpM (Option $typeName) := do
  let some (n, _) ← getOfNatValue? e $(quote typeName.getId) | return none
  return $(mkIdent ofNat) n

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : $typeName → $typeName → $typeName) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : $typeName → $typeName → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : $typeName → $typeName → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

dsimproc [simp, seval] $(mkIdent `reduceAdd):ident ((_ + _ : $typeName)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, seval] $(mkIdent `reduceMul):ident ((_ * _ : $typeName)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, seval] $(mkIdent `reduceSub):ident ((_ - _ : $typeName)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, seval] $(mkIdent `reduceDiv):ident ((_ / _ : $typeName)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, seval] $(mkIdent `reduceMod):ident ((_ % _ : $typeName)) := reduceBin ``HMod.hMod 6 (· % ·)

simproc [simp, seval] $(mkIdent `reduceLT):ident  (( _ : $typeName) < _)  := reduceBinPred ``LT.lt 4 (. < .)
simproc [simp, seval] $(mkIdent `reduceLE):ident  (( _ : $typeName) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] $(mkIdent `reduceGT):ident  (( _ : $typeName) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] $(mkIdent `reduceGE):ident  (( _ : $typeName) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
simproc [simp, seval] reduceEq  (( _ : $typeName) = _)  := reduceBinPred ``Eq 3 (. = .)
simproc [simp, seval] reduceNe  (( _ : $typeName) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
dsimproc [simp, seval] reduceBEq  (( _ : $typeName) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
dsimproc [simp, seval] reduceBNe  (( _ : $typeName) != _)  := reduceBoolPred ``bne 4 (. != .)

dsimproc [simp, seval] $(mkIdent `reduceOfNatLT):ident ($ofNatLT _ _) := fun e => do
  unless e.isAppOfArity $(quote ofNatLT.getId) 2 do return .continue
  let some value ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let value := $(mkIdent ofNat) value
  return .done <| toExpr value

dsimproc [simp, seval] $(mkIdent `reduceOfNat):ident ($(mkIdent ofNat) _) := fun e => do
  unless e.isAppOfArity $(quote ofNat) 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := $(mkIdent ofNat) value
  return .done <| toExpr value

dsimproc [simp, seval] $(mkIdent `reduceToNat):ident ($toNat _) := fun e => do
  unless e.isAppOfArity $(quote toNat.getId) 1 do return .continue
  let some v ← ($fromExpr e.appArg!) | return .continue
  let n := $toNat v
  return .done <| toExpr n

/-- Return `.done` for UInt values. We don't want to unfold in the symbolic evaluator. -/
dsimproc [seval] isValue ((OfNat.ofNat _ : $typeName)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end $typeName
)

-- declare_uint_simprocs_ext USize64 -- macro call replaced with direct inline (macros don't handle dsimproc correctly)
namespace USize64

def fromExpr (e : Expr) : SimpM (Option USize64) := do
  let some (n, _) ← getOfNatValue? e ``USize64 | return none
  return ofNat n

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : USize64 → USize64 → USize64) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : USize64 → USize64 → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : USize64 → USize64 → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

dsimproc [simp, seval] reduceAdd ((_ + _ : USize64)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, seval] reduceMul ((_ * _ : USize64)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, seval] reduceSub ((_ - _ : USize64)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, seval] reduceDiv ((_ / _ : USize64)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, seval] reduceMod ((_ % _ : USize64)) := reduceBin ``HMod.hMod 6 (· % ·)

simproc [simp, seval] reduceLT  (( _ : USize64) < _)  := reduceBinPred ``LT.lt 4 (. < .)
simproc [simp, seval] reduceLE  (( _ : USize64) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] reduceGT  (( _ : USize64) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] reduceGE  (( _ : USize64) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
simproc [simp, seval] reduceEq  (( _ : USize64) = _)  := reduceBinPred ``Eq 3 (. = .)
simproc [simp, seval] reduceNe  (( _ : USize64) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
dsimproc [simp, seval] reduceBEq  (( _ : USize64) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
dsimproc [simp, seval] reduceBNe  (( _ : USize64) != _)  := reduceBoolPred ``bne 4 (. != .)

dsimproc [simp, seval] reduceOfNatLT (ofNatLT _ _) := fun e => do
  unless e.isAppOfArity ``USize64.ofNatLT 2 do return .continue
  let some value ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let value := ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfNat (ofNat _) := fun e => do
  unless e.isAppOfArity ``USize64.ofNat 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceToNat (toNat _) := fun e => do
  unless e.isAppOfArity ``USize64.toNat 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := toNat v
  return .done <| toExpr n

/-- Return `.done` for UInt values. We don't want to unfold in the symbolic evaluator. -/
dsimproc [seval] isValue ((OfNat.ofNat _ : USize64)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end USize64

-- ──────────────────────────────────────────────────────────────────────
-- Source: Lean/Meta/Tactic/Simp/BuiltinSimprocs/SInt.lean
-- Target: Hax/MissingLean/Lean/Tactic/Simp/BuiltinSimpProcs/SInt.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean Meta Simp

macro "declare_sint_simprocs_ext" typeName:ident : command =>
let ofNat := typeName.getId ++ `ofNat
let ofInt := typeName.getId ++ `ofInt
let ofIntLE := mkIdent (typeName.getId ++ `ofIntLE)
let toInt := mkIdent (typeName.getId ++ `toInt)
let toNatClampNeg := mkIdent (typeName.getId ++ `toNatClampNeg)
let fromExpr := mkIdent `fromExpr
`(
namespace $typeName

def $fromExpr (e : Expr) : SimpM (Option $typeName) := do
  if let some (n, _) ← getOfNatValue? e $(quote typeName.getId) then
    return some ($(mkIdent ofNat) n)
  let_expr Neg.neg _ _ a ← e | return none
  let some (n, _) ← getOfNatValue? a $(quote typeName.getId) | return none
  return some ($(mkIdent ofInt) (- n))

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : $typeName → $typeName → $typeName) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : $typeName → $typeName → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : $typeName → $typeName → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

dsimproc [simp, seval] reduceNeg ((- _ : $typeName)) := fun e => do
  let_expr Neg.neg _ _ arg ← e | return .continue
  if arg.isAppOfArity ``OfNat.ofNat 3 then
    -- We return .done to ensure `Neg.neg` is not unfolded even when `ground := true`.
    return .done e
  else
    let some v ← ($fromExpr arg) | return .continue
    return .done <| toExpr (- v)

dsimproc [simp, seval] $(mkIdent `reduceAdd):ident ((_ + _ : $typeName)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, seval] $(mkIdent `reduceMul):ident ((_ * _ : $typeName)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, seval] $(mkIdent `reduceSub):ident ((_ - _ : $typeName)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, seval] $(mkIdent `reduceDiv):ident ((_ / _ : $typeName)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, seval] $(mkIdent `reduceMod):ident ((_ % _ : $typeName)) := reduceBin ``HMod.hMod 6 (· % ·)

simproc [simp, seval] $(mkIdent `reduceLT):ident  (( _ : $typeName) < _)  := reduceBinPred ``LT.lt 4 (. < .)
simproc [simp, seval] $(mkIdent `reduceLE):ident  (( _ : $typeName) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] $(mkIdent `reduceGT):ident  (( _ : $typeName) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] $(mkIdent `reduceGE):ident  (( _ : $typeName) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
simproc [simp, seval] reduceEq  (( _ : $typeName) = _)  := reduceBinPred ``Eq 3 (. = .)
simproc [simp, seval] reduceNe  (( _ : $typeName) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
dsimproc [simp, seval] reduceBEq  (( _ : $typeName) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
dsimproc [simp, seval] reduceBNe  (( _ : $typeName) != _)  := reduceBoolPred ``bne 4 (. != .)

dsimproc [simp, seval] $(mkIdent `reduceOfIntLE):ident ($ofIntLE _ _ _) := fun e => do
  unless e.isAppOfArity $(quote ofIntLE.getId) 3 do return .continue
  let some value ← Int.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  let value := $(mkIdent ofInt) value
  return .done <| toExpr value

dsimproc [simp, seval] $(mkIdent `reduceOfNat):ident ($(mkIdent ofNat) _) := fun e => do
  unless e.isAppOfArity $(quote ofNat) 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := $(mkIdent ofNat) value
  return .done <| toExpr value

dsimproc [simp, seval] $(mkIdent `reduceOfInt):ident ($(mkIdent ofInt) _) := fun e => do
  unless e.isAppOfArity $(quote ofInt) 1 do return .continue
  let some value ← Int.fromExpr? e.appArg! | return .continue
  let value := $(mkIdent ofInt) value
  return .done <| toExpr value

dsimproc [simp, seval] $(mkIdent `reduceToInt):ident ($toInt _) := fun e => do
  unless e.isAppOfArity $(quote toInt.getId) 1 do return .continue
  let some v ← ($fromExpr e.appArg!) | return .continue
  let n := $toInt v
  return .done <| toExpr n

dsimproc [simp, seval] $(mkIdent `reduceToNatClampNeg):ident ($toNatClampNeg _) := fun e => do
  unless e.isAppOfArity $(quote toNatClampNeg.getId) 1 do return .continue
  let some v ← ($fromExpr e.appArg!) | return .continue
  let n := $toNatClampNeg v
  return .done <| toExpr n

/-- Return `.done` for Int values. We don't want to unfold in the symbolic evaluator. -/
dsimproc [seval] isValue ((OfNat.ofNat _ : $typeName)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end $typeName
)

-- declare_sint_simprocs_ext ISize64 -- macro call replaced with direct inline
namespace ISize64

def fromExpr (e : Expr) : SimpM (Option ISize64) := do
  if let some (n, _) ← getOfNatValue? e ``ISize64 then
    return some (ofNat n)
  let_expr Neg.neg _ _ a ← e | return none
  let some (n, _) ← getOfNatValue? a ``ISize64 | return none
  return some (ofInt (- n))

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : ISize64 → ISize64 → ISize64) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : ISize64 → ISize64 → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : ISize64 → ISize64 → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

dsimproc [simp, seval] reduceNeg ((- _ : ISize64)) := fun e => do
  let_expr Neg.neg _ _ arg ← e | return .continue
  if arg.isAppOfArity ``OfNat.ofNat 3 then
    -- We return .done to ensure `Neg.neg` is not unfolded even when `ground := true`.
    return .done e
  else
    let some v ← (fromExpr arg) | return .continue
    return .done <| toExpr (- v)

dsimproc [simp, seval] reduceAdd ((_ + _ : ISize64)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, seval] reduceMul ((_ * _ : ISize64)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, seval] reduceSub ((_ - _ : ISize64)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, seval] reduceDiv ((_ / _ : ISize64)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, seval] reduceMod ((_ % _ : ISize64)) := reduceBin ``HMod.hMod 6 (· % ·)

simproc [simp, seval] reduceLT  (( _ : ISize64) < _)  := reduceBinPred ``LT.lt 4 (. < .)
simproc [simp, seval] reduceLE  (( _ : ISize64) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] reduceGT  (( _ : ISize64) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] reduceGE  (( _ : ISize64) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
simproc [simp, seval] reduceEq  (( _ : ISize64) = _)  := reduceBinPred ``Eq 3 (. = .)
simproc [simp, seval] reduceNe  (( _ : ISize64) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
dsimproc [simp, seval] reduceBEq  (( _ : ISize64) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
dsimproc [simp, seval] reduceBNe  (( _ : ISize64) != _)  := reduceBoolPred ``bne 4 (. != .)

dsimproc [simp, seval] reduceOfIntLE (ofIntLE _ _ _) := fun e => do
  unless e.isAppOfArity ``ISize64.ofIntLE 3 do return .continue
  let some value ← Int.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  let value := ofInt value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfNat (ofNat _) := fun e => do
  unless e.isAppOfArity ``ISize64.ofNat 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfInt (ofInt _) := fun e => do
  unless e.isAppOfArity ``ISize64.ofInt 1 do return .continue
  let some value ← Int.fromExpr? e.appArg! | return .continue
  let value := ofInt value
  return .done <| toExpr value

dsimproc [simp, seval] reduceToInt (toInt _) := fun e => do
  unless e.isAppOfArity ``ISize64.toInt 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := toInt v
  return .done <| toExpr n

dsimproc [simp, seval] reduceToNatClampNeg (toNatClampNeg _) := fun e => do
  unless e.isAppOfArity ``ISize64.toNatClampNeg 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := toNatClampNeg v
  return .done <| toExpr n

/-- Return `.done` for Int values. We don't want to unfold in the symbolic evaluator. -/
dsimproc [seval] isValue ((OfNat.ofNat _ : ISize64)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end ISize64

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/UInt/Lemmas.lean
-- Target: Hax/MissingLean/Init/Data/UInt/Lemmas_UInt128.lean
-- ──────────────────────────────────────────────────────────────────────

set_option autoImplicit true
open Std

declare_uint_theorems USize64 64

@[simp] theorem USize.toNat_toUSize64 (x : USize) : x.toUSize64.toNat = x.toNat := (rfl)

theorem USize64.ofNat_mod_size : ofNat (x % 2 ^ 64) = ofNat x := by
  simp [ofNat, BitVec.ofNat, Fin.ofNat]

theorem USize64.ofNat_size : ofNat size = 0 := by decide

theorem USize64.lt_ofNat_iff {n : USize64} {m : Nat} (h : m < size) : n < ofNat m ↔ n.toNat < m := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]

theorem USize64.ofNat_lt_iff {n : USize64} {m : Nat} (h : m < size) : ofNat m < n ↔ m < n.toNat := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]

theorem USize64.le_ofNat_iff {n : USize64} {m : Nat} (h : m < size) : n ≤ ofNat m ↔ n.toNat ≤ m := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]

theorem USize64.ofNat_le_iff {n : USize64} {m : Nat} (h : m < size) : ofNat m ≤ n ↔ m ≤ n.toNat := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]

protected theorem USize64.mod_eq_of_lt {a b : USize64} (h : a < b) : a % b = a := USize64.toNat_inj.1 (Nat.mod_eq_of_lt h)

@[simp] theorem USize64.toNat_lt (n : USize64) : n.toNat < 2 ^ 64 := n.toFin.isLt

theorem USize.size_le_uisize64Size : USize.size ≤ USize64.size := by
  cases USize.size_eq <;> simp_all +decide

theorem USize.size_dvd_uISize64Size : USize.size ∣ USize64.size := by cases USize.size_eq <;> simp_all +decide

@[simp] theorem mod_uISize64Size_uSizeSize (n : Nat) : n % USize64.size % USize.size = n % USize.size :=
  Nat.mod_mod_of_dvd _ USize.size_dvd_uISize64Size

@[simp] theorem USize64.size_sub_one_mod_uSizeSize : 18446744073709551615 % USize.size = USize.size - 1 := by
  cases USize.size_eq <;> simp_all +decide

@[simp] theorem UInt8.toNat_mod_uISize64Size (n : UInt8) : n.toNat % USize64.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))

@[simp] theorem UInt16.toNat_mod_uISize64Size (n : UInt16) : n.toNat % USize64.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))

@[simp] theorem UInt32.toNat_mod_uISize64Size (n : UInt32) : n.toNat % USize64.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))

@[simp] theorem USize64.toNat_mod_size (n : USize64) : n.toNat % USize64.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt

@[simp] theorem USize.toNat_mod_uISize64Size (n : USize) : n.toNat % USize64.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt

@[simp] theorem UInt8.toUSize64_mod_256 (n : UInt8) : n.toUSize64 % 256 = n.toUSize64 := USize64.toNat.inj (by simp)

@[simp] theorem UInt16.toUSize64_mod_65536 (n : UInt16) : n.toUSize64 % 65536 = n.toUSize64 := USize64.toNat.inj (by simp)

@[simp] theorem UInt32.toUSize64_mod_4294967296 (n : UInt32) : n.toUSize64 % 4294967296 = n.toUSize64 := USize64.toNat.inj (by simp)

@[simp] theorem Fin.mk_uISize64ToNat (n : USize64) : Fin.mk n.toNat (by exact n.toFin.isLt) = n.toFin := (rfl)

@[simp] theorem BitVec.ofNatLT_uISize64ToNat (n : USize64) : BitVec.ofNatLT n.toNat (by exact n.toFin.isLt) = n.toBitVec := (rfl)

@[simp] theorem BitVec.ofFin_uISize64ToFin (n : USize64) : BitVec.ofFin n.toFin = n.toBitVec := (rfl)

@[simp] theorem UInt8.toFin_toUSize64 (n : UInt8) : n.toUSize64.toFin = n.toFin.castLE (by decide) := (rfl)

@[simp] theorem UInt16.toFin_toUSize64 (n : UInt16) : n.toUSize64.toFin = n.toFin.castLE (by decide) := (rfl)

@[simp] theorem UInt32.toFin_toUSize64 (n : UInt32) : n.toUSize64.toFin = n.toFin.castLE (by decide) := (rfl)

@[simp] theorem USize.toFin_toUSize64 (n : USize) : n.toUSize64.toFin = n.toFin.castLE size_le_uisize64Size := (rfl)

@[simp, int_toBitVec] theorem USize64.toBitVec_toUInt8 (n : USize64) : n.toUInt8.toBitVec = n.toBitVec.setWidth 8 := (rfl)

@[simp, int_toBitVec] theorem USize64.toBitVec_toUInt16 (n : USize64) : n.toUInt16.toBitVec = n.toBitVec.setWidth 16 := (rfl)

@[simp, int_toBitVec] theorem USize64.toBitVec_toUInt32 (n : USize64) : n.toUInt32.toBitVec = n.toBitVec.setWidth 32 := (rfl)

@[simp, int_toBitVec] theorem UInt8.toBitVec_toUSize64 (n : UInt8) : n.toUSize64.toBitVec = n.toBitVec.setWidth 64 := (rfl)

@[simp, int_toBitVec] theorem UInt16.toBitVec_toUSize64 (n : UInt16) : n.toUSize64.toBitVec = n.toBitVec.setWidth 64 := (rfl)

@[simp, int_toBitVec] theorem UInt32.toBitVec_toUSize64 (n : UInt32) : n.toUSize64.toBitVec = n.toBitVec.setWidth 64 := (rfl)

@[simp, int_toBitVec] theorem USize.toBitVec_toUSize64 (n : USize) : n.toUSize64.toBitVec = n.toBitVec.setWidth 64 :=
  BitVec.eq_of_toNat_eq (by simp)

@[simp, int_toBitVec] theorem USize64.toBitVec_toUSize (n : USize64) : n.toUSize.toBitVec = n.toBitVec.setWidth System.Platform.numBits :=
  BitVec.eq_of_toNat_eq (by simp)

@[simp] theorem USize64.ofNatLT_uInt8ToNat (n : UInt8) : USize64.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUSize64 := (rfl)

@[simp] theorem USize64.ofNatLT_uInt16ToNat (n : UInt16) : USize64.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUSize64 := (rfl)

@[simp] theorem USize64.ofNatLT_uInt32ToNat (n : UInt32) : USize64.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUSize64 := (rfl)

@[simp] theorem USize64.ofNatLT_toNat (n : USize64) : USize64.ofNatLT n.toNat n.toNat_lt = n := (rfl)

@[simp] theorem USize64.ofNatLT_uSizeToNat (n : USize) : USize64.ofNatLT n.toNat n.toNat_lt = n.toUSize64 := (rfl)

theorem UInt8.ofNatLT_uISize64ToNat (n : USize64) (h) : UInt8.ofNatLT n.toNat h = n.toUInt8 :=
  UInt8.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem UInt16.ofNatLT_uISize64ToNat (n : USize64) (h) : UInt16.ofNatLT n.toNat h = n.toUInt16 :=
  UInt16.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem UInt32.ofNatLT_uISize64ToNat (n : USize64) (h) : UInt32.ofNatLT n.toNat h = n.toUInt32 :=
  UInt32.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem USize.ofNatLT_uISize64ToNat (n : USize64) (h) : USize.ofNatLT n.toNat h = n.toUSize :=
  USize.toNat.inj (by simp [Nat.mod_eq_of_lt h])

@[simp] theorem USize64.ofFin_toFin (n : USize64) : USize64.ofFin n.toFin = n := (rfl)

@[simp] theorem USize64.toFin_ofFin (n : Fin USize64.size) : (USize64.ofFin n).toFin = n := (rfl)

@[simp] theorem USize64.ofFin_uint8ToFin (n : UInt8) : USize64.ofFin (n.toFin.castLE (by decide)) = n.toUSize64 := (rfl)

@[simp] theorem USize64.ofFin_uint16ToFin (n : UInt16) : USize64.ofFin (n.toFin.castLE (by decide)) = n.toUSize64 := (rfl)

@[simp] theorem USize64.ofFin_uint32ToFin (n : UInt32) : USize64.ofFin (n.toFin.castLE (by decide)) = n.toUSize64 := (rfl)

@[simp] theorem Nat.toUSize64_eq {n : Nat} : n.toUSize64 = USize64.ofNat n := (rfl)

@[simp] theorem UInt8.ofBitVec_uISize64ToBitVec (n : USize64) :
    UInt8.ofBitVec (n.toBitVec.setWidth 8) = n.toUInt8 := (rfl)

@[simp] theorem UInt16.ofBitVec_uISize64ToBitVec (n : USize64) :
    UInt16.ofBitVec (n.toBitVec.setWidth 16) = n.toUInt16 := (rfl)

@[simp] theorem UInt32.ofBitVec_uISize64ToBitVec (n : USize64) :
    UInt32.ofBitVec (n.toBitVec.setWidth 32) = n.toUInt32 := (rfl)

@[simp] theorem USize64.ofBitVec_uInt8ToBitVec (n : UInt8) :
    USize64.ofBitVec (n.toBitVec.setWidth 64) = n.toUSize64 := (rfl)

@[simp] theorem USize64.ofBitVec_uInt16ToBitVec (n : UInt16) :
    USize64.ofBitVec (n.toBitVec.setWidth 64) = n.toUSize64 := (rfl)

@[simp] theorem USize64.ofBitVec_uInt32ToBitVec (n : UInt32) :
    USize64.ofBitVec (n.toBitVec.setWidth 64) = n.toUSize64 := (rfl)

@[simp] theorem USize64.ofBitVec_uSizeToBitVec (n : USize) :
    USize64.ofBitVec (n.toBitVec.setWidth 64) = n.toUSize64 :=
  USize64.toNat.inj (by simp)

@[simp] theorem USize.ofBitVec_uISize64ToBitVec (n : USize64) :
    USize.ofBitVec (n.toBitVec.setWidth System.Platform.numBits) = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt8.ofNat_uISize64ToNat (n : USize64) : UInt8.ofNat n.toNat = n.toUInt8 := (rfl)

@[simp] theorem UInt16.ofNat_uISize64ToNat (n : USize64) : UInt16.ofNat n.toNat = n.toUInt16 := (rfl)

@[simp] theorem UInt32.ofNat_uISize64ToNat (n : USize64) : UInt32.ofNat n.toNat = n.toUInt32 := (rfl)

@[simp] theorem USize64.ofNat_uInt8ToNat (n : UInt8) : USize64.ofNat n.toNat = n.toUSize64 :=
  USize64.toNat.inj (by simp)

@[simp] theorem USize64.ofNat_uInt16ToNat (n : UInt16) : USize64.ofNat n.toNat = n.toUSize64 :=
  USize64.toNat.inj (by simp)

@[simp] theorem USize64.ofNat_uInt32ToNat (n : UInt32) : USize64.ofNat n.toNat = n.toUSize64 :=
  USize64.toNat.inj (by simp)

@[simp] theorem USize64.ofNat_uSizeToNat (n : USize) : USize64.ofNat n.toNat = n.toUSize64 :=
  USize64.toNat.inj (by simp)

@[simp] theorem USize.ofNat_uISize64ToNat (n : USize64) : USize.ofNat n.toNat = n.toUSize :=
  USize.toNat.inj (by simp)

theorem USize64.ofNatLT_eq_ofNat (n : Nat) {h} : USize64.ofNatLT n h = USize64.ofNat n :=
  USize64.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem USize64.ofNatTruncate_eq_ofNat (n : Nat) (hn : n < USize64.size) :
    USize64.ofNatTruncate n = USize64.ofNat n := by
  simp [ofNatTruncate, hn, USize64.ofNatLT_eq_ofNat]

@[simp] theorem USize64.ofNatTruncate_uInt8ToNat (n : UInt8) : USize64.ofNatTruncate n.toNat = n.toUSize64 := by
  rw [USize64.ofNatTruncate_eq_ofNat, ofNat_uInt8ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)

@[simp] theorem USize64.ofNatTruncate_uInt16ToNat (n : UInt16) : USize64.ofNatTruncate n.toNat = n.toUSize64 := by
  rw [USize64.ofNatTruncate_eq_ofNat, ofNat_uInt16ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)

@[simp] theorem USize64.ofNatTruncate_uInt32ToNat (n : UInt32) : USize64.ofNatTruncate n.toNat = n.toUSize64 := by
  rw [USize64.ofNatTruncate_eq_ofNat, ofNat_uInt32ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)

@[simp] theorem USize64.ofNatTruncate_toNat (n : USize64) : USize64.ofNatTruncate n.toNat = n := by
  rw [USize64.ofNatTruncate_eq_ofNat] <;> simp [n.toNat_lt]

@[simp] theorem USize64.ofNatTruncate_uSizeToNat (n : USize) : USize64.ofNatTruncate n.toNat = n.toUSize64 := by
  rw [USize64.ofNatTruncate_eq_ofNat, ofNat_uSizeToNat]
  exact n.toNat_lt

@[simp] theorem UInt8.toUInt8_toUSize64 (n : UInt8) : n.toUSize64.toUInt8 = n :=
  UInt8.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt16_toUSize64 (n : UInt8) : n.toUSize64.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt32_toUSize64 (n : UInt8) : n.toUSize64.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt8.toUSize64_toUInt16 (n : UInt8) : n.toUInt16.toUSize64 = n.toUSize64 := (rfl)

@[simp] theorem UInt8.toUSize64_toUInt32 (n : UInt8) : n.toUInt32.toUSize64 = n.toUSize64 := (rfl)

@[simp] theorem UInt8.toUSize64_toUSize (n : UInt8) : n.toUSize.toUSize64 = n.toUSize64 := (rfl)

@[simp] theorem UInt8.toUSize_toUSize64 (n : UInt8) : n.toUSize64.toUSize = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt8_toUSize64 (n : UInt16) : n.toUSize64.toUInt8 = n.toUInt8 := (rfl)

@[simp] theorem UInt16.toUInt16_toUSize64 (n : UInt16) : n.toUSize64.toUInt16 = n :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt32_toUSize64 (n : UInt16) : n.toUSize64.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt16.toUSize64_toUInt8 (n : UInt16) : n.toUInt8.toUSize64 = n.toUSize64 % 256 := (rfl)

@[simp] theorem UInt16.toUSize64_toUInt32 (n : UInt16) : n.toUInt32.toUSize64 = n.toUSize64 := (rfl)

@[simp] theorem UInt16.toUSize64_toUSize (n : UInt16) : n.toUSize.toUSize64 = n.toUSize64 := (rfl)

@[simp] theorem UInt16.toUSize_toUSize64 (n : UInt16) : n.toUSize64.toUSize = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt8_toUSize64 (n : UInt32) : n.toUSize64.toUInt8 = n.toUInt8 := (rfl)

@[simp] theorem UInt32.toUInt16_toUSize64 (n : UInt32) : n.toUSize64.toUInt16 = n.toUInt16 := (rfl)

@[simp] theorem UInt32.toUInt32_toUSize64 (n : UInt32) : n.toUSize64.toUInt32 = n :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt32.toUSize64_toUInt8 (n : UInt32) : n.toUInt8.toUSize64 = n.toUSize64 % 256 := (rfl)

@[simp] theorem UInt32.toUSize64_toUInt16 (n : UInt32) : n.toUInt16.toUSize64 = n.toUSize64 % 65536 := (rfl)

@[simp] theorem UInt32.toUSize64_toUSize (n : UInt32) : n.toUSize.toUSize64 = n.toUSize64 := (rfl)

@[simp] theorem UInt32.toUSize_toUSize64 (n : UInt32) : n.toUSize64.toUSize = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem USize64.toUInt8_toUInt16 (n : USize64) : n.toUInt16.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)

@[simp] theorem USize64.toUInt8_toUInt32 (n : USize64) : n.toUInt32.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)

@[simp] theorem USize64.toUInt8_toUSize (n : USize64) : n.toUSize.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)

@[simp] theorem USize64.toUInt16_toUInt8 (n : USize64) : n.toUInt8.toUInt16 = n.toUInt16 % 256 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem USize64.toUInt16_toUInt32 (n : USize64) : n.toUInt32.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem USize64.toUInt16_toUSize (n : USize64) : n.toUSize.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem USize64.toUInt32_toUInt8 (n : USize64) : n.toUInt8.toUInt32 = n.toUInt32 % 256 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem USize64.toUInt32_toUInt16 (n : USize64) : n.toUInt16.toUInt32 = n.toUInt32 % 65536 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem USize64.toUInt32_toUSize (n : USize64) : n.toUSize.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem USize64.toUSize64_toUInt8 (n : USize64) : n.toUInt8.toUSize64 = n % 256 := (rfl)

@[simp] theorem USize64.toUSize64_toUInt16 (n : USize64) : n.toUInt16.toUSize64 = n % 65536 := (rfl)

@[simp] theorem USize64.toUSize64_toUInt32 (n : USize64) : n.toUInt32.toUSize64 = n % 4294967296 := (rfl)

@[simp] theorem USize64.toUSize_toUInt8 (n : USize64) : n.toUInt8.toUSize = n.toUSize % 256 :=
  USize.toNat.inj (by simp)

@[simp] theorem USize64.toUSize_toUInt16 (n : USize64) : n.toUInt16.toUSize = n.toUSize % 65536 :=
  USize.toNat.inj (by simp)

@[simp] theorem USize.toUInt8_toUSize64 (n : USize) : n.toUSize64.toUInt8 = n.toUInt8 := (rfl)

@[simp] theorem USize.toUInt16_toUSize64 (n : USize) : n.toUSize64.toUInt16 = n.toUInt16 := (rfl)

@[simp] theorem USize.toUSize64_toUInt8 (n : USize) : n.toUInt8.toUSize64 = n.toUSize64 % 256 := (rfl)

@[simp] theorem USize.toUSize64_toUInt16 (n : USize) : n.toUInt16.toUSize64 = n.toUSize64 % 65536 := (rfl)

@[simp] theorem USize.toUInt32_toUSize64 (n : USize) : n.toUSize64.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem USize.toUSize_toUSize64 (n : USize) : n.toUSize64.toUSize = n :=
  USize.toNat.inj (by simp)

@[simp] theorem USize64.toNat_ofFin (x : Fin USize64.size) : (USize64.ofFin x).toNat = x.val := (rfl)

theorem USize64.toNat_ofNatTruncate_of_lt {n : Nat} (hn : n < USize64.size) :
    (USize64.ofNatTruncate n).toNat = n := by rw [USize64.ofNatTruncate, dif_pos hn, toNat_ofNatLT]

theorem USize64.toNat_ofNatTruncate_of_le {n : Nat} (hn : USize64.size ≤ n) :
    (USize64.ofNatTruncate n).toNat = USize64.size - 1 := by rw [ofNatTruncate, dif_neg (by omega), toNat_ofNatLT]

@[simp] theorem USize64.toFin_ofNatLT {n : Nat} (hn) : (USize64.ofNatLT n hn).toFin = ⟨n, hn⟩ := (rfl)

@[simp] theorem USize64.toFin.ofNat {n : Nat} : (USize64.ofNat n).toFin = Fin.ofNat _ n := (rfl)

@[simp] theorem USize64.toFin_ofBitVec {b} : (USize64.ofBitVec b).toFin = b.toFin := (rfl)

theorem USize64.toFin_ofNatTruncate_of_lt {n : Nat} (hn : n < USize64.size) :
    (USize64.ofNatTruncate n).toFin = ⟨n, hn⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_lt hn])

theorem USize64.toFin_ofNatTruncate_of_le {n : Nat} (hn : USize64.size ≤ n) :
    (USize64.ofNatTruncate n).toFin = ⟨USize64.size - 1, by decide⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_le hn])

@[simp, int_toBitVec] theorem USize64.toBitVec_ofNatLT {n : Nat} (hn : n < USize64.size) :
    (USize64.ofNatLT n hn).toBitVec = BitVec.ofNatLT n hn := (rfl)

@[simp, int_toBitVec] theorem USize64.toBitVec_ofFin (n : Fin USize64.size) : (USize64.ofFin n).toBitVec = BitVec.ofFin n := (rfl)

@[simp, int_toBitVec] theorem USize64.toBitVec_ofBitVec (n) : (USize64.ofBitVec n).toBitVec = n := (rfl)

theorem USize64.toBitVec_ofNatTruncate_of_lt {n : Nat} (hn : n < USize64.size) :
    (USize64.ofNatTruncate n).toBitVec = BitVec.ofNatLT n hn :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_lt hn])

theorem USize64.toBitVec_ofNatTruncate_of_le {n : Nat} (hn : USize64.size ≤ n) :
    (USize64.ofNatTruncate n).toBitVec = BitVec.ofNatLT (USize64.size - 1) (by decide) :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem USize64.toUInt8_ofNatLT {n : Nat} (hn) : (USize64.ofNatLT n hn).toUInt8 = UInt8.ofNat n := (rfl)

@[simp] theorem USize64.toUInt8_ofFin (n) : (USize64.ofFin n).toUInt8 = UInt8.ofNat n.val := (rfl)

@[simp] theorem USize64.toUInt8_ofBitVec (b) : (USize64.ofBitVec b).toUInt8 = UInt8.ofBitVec (b.setWidth _) := (rfl)

@[simp] theorem USize64.toUInt8_ofNat' (n : Nat) : (USize64.ofNat n).toUInt8 = UInt8.ofNat n := UInt8.toNat.inj (by simp)

@[simp] theorem USize64.toUInt8_ofNat {n : Nat} : toUInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toUInt8_ofNat' _

theorem USize64.toUInt8_ofNatTruncate_of_lt {n : Nat} (hn : n < USize64.size) :
    (USize64.ofNatTruncate n).toUInt8 = UInt8.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt8_ofNatLT]

theorem USize64.toUInt8_ofNatTruncate_of_le {n : Nat} (hn : USize64.size ≤ n) :
    (USize64.ofNatTruncate n).toUInt8 = UInt8.ofNatLT (UInt8.size - 1) (by decide) :=
  UInt8.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem USize64.toUInt16_ofNatLT {n : Nat} (hn) : (USize64.ofNatLT n hn).toUInt16 = UInt16.ofNat n := (rfl)

@[simp] theorem USize64.toUInt16_ofFin (n) : (USize64.ofFin n).toUInt16 = UInt16.ofNat n.val := (rfl)

@[simp] theorem USize64.toUInt16_ofBitVec (b) : (USize64.ofBitVec b).toUInt16 = UInt16.ofBitVec (b.setWidth _) := (rfl)

@[simp] theorem USize64.toUInt16_ofNat' (n : Nat) : (USize64.ofNat n).toUInt16 = UInt16.ofNat n := UInt16.toNat.inj (by simp)

@[simp] theorem USize64.toUInt16_ofNat {n : Nat} : toUInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := USize64.toUInt16_ofNat' _

theorem USize64.toUInt16_ofNatTruncate_of_lt {n : Nat} (hn : n < USize64.size) :
    (USize64.ofNatTruncate n).toUInt16 = UInt16.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt16_ofNatLT]

theorem USize64.toUInt16_ofNatTruncate_of_le {n : Nat} (hn : USize64.size ≤ n) :
    (USize64.ofNatTruncate n).toUInt16 = UInt16.ofNatLT (UInt16.size - 1) (by decide) :=
  UInt16.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem USize64.toUInt32_ofNatLT {n : Nat} (hn) : (USize64.ofNatLT n hn).toUInt32 = UInt32.ofNat n := (rfl)

@[simp] theorem USize64.toUInt32_ofFin (n) : (USize64.ofFin n).toUInt32 = UInt32.ofNat n.val := (rfl)

@[simp] theorem USize64.toUInt32_ofBitVec (b) : (USize64.ofBitVec b).toUInt32 = UInt32.ofBitVec (b.setWidth _) := (rfl)

@[simp] theorem USize64.toUInt32_ofNat' (n : Nat) : (USize64.ofNat n).toUInt32 = UInt32.ofNat n := UInt32.toNat.inj (by simp)

@[simp] theorem USize64.toUInt32_ofNat {n : Nat} : toUInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := USize64.toUInt32_ofNat' _

theorem USize64.toUInt32_ofNatTruncate_of_lt {n : Nat} (hn : n < USize64.size) :
    (USize64.ofNatTruncate n).toUInt32 = UInt32.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt32_ofNatLT]

theorem USize64.toUInt32_ofNatTruncate_of_le {n : Nat} (hn : USize64.size ≤ n) :
    (USize64.ofNatTruncate n).toUInt32 = UInt32.ofNatLT (UInt32.size - 1) (by decide) :=
  UInt32.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem USize64.toUSize_ofNatLT {n : Nat} (hn) : (USize64.ofNatLT n hn).toUSize = USize.ofNat n := (rfl)

@[simp] theorem USize64.toUSize_ofFin (n) : (USize64.ofFin n).toUSize = USize.ofNat n.val := (rfl)

@[simp] theorem USize64.toUSize_ofBitVec (b) : (USize64.ofBitVec b).toUSize = USize.ofBitVec (b.setWidth _) :=
  USize.toNat.inj (by simp)

@[simp] theorem USize64.toUSize_ofNat' (n : Nat) : (USize64.ofNat n).toUSize = USize.ofNat n := USize.toNat.inj (by simp)

@[simp] theorem USize64.toUSize_ofNat {n : Nat} : toUSize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := USize64.toUSize_ofNat' _

theorem USize64.toUSize_ofNatTruncate_of_lt {n : Nat} (hn : n < USize64.size) :
    (USize64.ofNatTruncate n).toUSize = USize.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUSize_ofNatLT]

theorem USize64.toUSize_ofNatTruncate_of_le {n : Nat} (hn : USize64.size ≤ n) :
    (USize64.ofNatTruncate n).toUSize = USize.ofNatLT (USize.size - 1) (by cases USize.size_eq <;> simp_all) :=
  USize.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt8.toUSize64_ofNatLT {n : Nat} (h) :
    (UInt8.ofNatLT n h).toUSize64 = USize64.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := (rfl)

theorem UInt8.toUSize64_ofFin {n} :
  (UInt8.ofFin n).toUSize64 = USize64.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := (rfl)

@[simp] theorem UInt8.toUSize64_ofBitVec {b} : (UInt8.ofBitVec b).toUSize64 = USize64.ofBitVec (b.setWidth _) := (rfl)

theorem UInt8.toUSize64_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt8.size) :
    (UInt8.ofNatTruncate n).toUSize64 = USize64.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  USize64.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt8.toUSize64_ofNatTruncate_of_le {n : Nat} (hn : UInt8.size ≤ n) :
    (UInt8.ofNatTruncate n).toUSize64 = USize64.ofNatLT (UInt8.size - 1) (by decide) :=
  USize64.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt16.toUSize64_ofNatLT {n : Nat} (h) :
    (UInt16.ofNatLT n h).toUSize64 = USize64.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := (rfl)

theorem UInt16.toUSize64_ofFin {n} :
  (UInt16.ofFin n).toUSize64 = USize64.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := (rfl)

@[simp] theorem UInt16.toUSize64_ofBitVec {b} : (UInt16.ofBitVec b).toUSize64 = USize64.ofBitVec (b.setWidth _) := (rfl)

theorem UInt16.toUSize64_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt16.size) :
    (UInt16.ofNatTruncate n).toUSize64 = USize64.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  USize64.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt16.toUSize64_ofNatTruncate_of_le {n : Nat} (hn : UInt16.size ≤ n) :
    (UInt16.ofNatTruncate n).toUSize64 = USize64.ofNatLT (UInt16.size - 1) (by decide) :=
  USize64.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt32.toUSize64_ofNatLT {n : Nat} (h) :
    (UInt32.ofNatLT n h).toUSize64 = USize64.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := (rfl)

theorem UInt32.toUSize64_ofFin {n} :
  (UInt32.ofFin n).toUSize64 = USize64.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := (rfl)

@[simp] theorem UInt32.toUSize64_ofBitVec {b} : (UInt32.ofBitVec b).toUSize64 = USize64.ofBitVec (b.setWidth _) := (rfl)

theorem UInt32.toUSize64_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt32.size) :
    (UInt32.ofNatTruncate n).toUSize64 = USize64.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  USize64.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt32.toUSize64_ofNatTruncate_of_le {n : Nat} (hn : UInt32.size ≤ n) :
    (UInt32.ofNatTruncate n).toUSize64 = USize64.ofNatLT (UInt32.size - 1) (by decide) :=
  USize64.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem USize.toUSize64_ofNatLT {n : Nat} (h) :
    (USize.ofNatLT n h).toUSize64 = USize64.ofNatLT n (Nat.lt_of_lt_of_le h size_le_uisize64Size) := (rfl)

theorem USize.toUSize64_ofFin {n} :
  (USize.ofFin n).toUSize64 = USize64.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt size_le_uisize64Size) := (rfl)

@[simp] theorem USize.toUSize64_ofBitVec {b} : (USize.ofBitVec b).toUSize64 = USize64.ofBitVec (b.setWidth _) :=
  USize64.toBitVec_inj.1 (by simp)

theorem USize.toUSize64_ofNatTruncate_of_lt {n : Nat} (hn : n < USize.size) :
    (USize.ofNatTruncate n).toUSize64 = USize64.ofNatLT n (Nat.lt_of_lt_of_le hn size_le_uisize64Size) :=
  USize64.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem USize.toUSize64_ofNatTruncate_of_le {n : Nat} (hn : USize.size ≤ n) :
    (USize.ofNatTruncate n).toUSize64 = USize64.ofNatLT (USize.size - 1) (by cases USize.size_eq <;> simp_all +decide) :=
  USize64.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt8.toUSize64_ofNat' {n : Nat} (hn : n < UInt8.size) : (UInt8.ofNat n).toUSize64 = USize64.ofNat n := by
  rw [← UInt8.ofNatLT_eq_ofNat (h := hn), toUSize64_ofNatLT, USize64.ofNatLT_eq_ofNat]

@[simp] theorem UInt16.toUSize64_ofNat' {n : Nat} (hn : n < UInt16.size) : (UInt16.ofNat n).toUSize64 = USize64.ofNat n := by
  rw [← UInt16.ofNatLT_eq_ofNat (h := hn), toUSize64_ofNatLT, USize64.ofNatLT_eq_ofNat]

@[simp] theorem UInt32.toUSize64_ofNat' {n : Nat} (hn : n < UInt32.size) : (UInt32.ofNat n).toUSize64 = USize64.ofNat n := by
  rw [← UInt32.ofNatLT_eq_ofNat (h := hn), toUSize64_ofNatLT, USize64.ofNatLT_eq_ofNat]

@[simp] theorem USize.toUSize64_ofNat' {n : Nat} (hn : n < USize.size) : (USize.ofNat n).toUSize64 = USize64.ofNat n := by
  rw [← USize.ofNatLT_eq_ofNat (h := hn), toUSize64_ofNatLT, USize64.ofNatLT_eq_ofNat]

@[simp] theorem UInt8.toUSize64_ofNat {n : Nat} (hn : n < 256) : toUSize64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt8.toUSize64_ofNat' hn

@[simp] theorem UInt16.toUSize64_ofNat {n : Nat} (hn : n < 65536) : toUSize64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt16.toUSize64_ofNat' hn

@[simp] theorem UInt32.toUSize64_ofNat {n : Nat} (hn : n < 4294967296) : toUSize64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt32.toUSize64_ofNat' hn

@[simp] theorem USize.toUSize64_ofNat {n : Nat} (hn : n < 4294967296) : toUSize64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  USize.toUSize64_ofNat' (Nat.lt_of_lt_of_le hn UInt32.size_le_usizeSize)

@[simp] theorem USize64.ofNatLT_finVal (n : Fin USize64.size) : USize64.ofNatLT n.val n.isLt = USize64.ofFin n := (rfl)

@[simp] theorem USize64.ofNatLT_bitVecToNat (n : BitVec 64) : USize64.ofNatLT n.toNat n.isLt = USize64.ofBitVec n := (rfl)

@[simp] theorem USize64.ofNat_finVal (n : Fin USize64.size) : USize64.ofNat n.val = USize64.ofFin n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_finVal]

@[simp] theorem USize64.ofNat_bitVecToNat (n : BitVec 64) : USize64.ofNat n.toNat = USize64.ofBitVec n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_bitVecToNat]

@[simp] theorem USize64.ofNatTruncate_finVal (n : Fin USize64.size) : USize64.ofNatTruncate n.val = USize64.ofFin n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, USize64.ofNat_finVal]

@[simp] theorem USize64.ofNatTruncate_bitVecToNat (n : BitVec 64) : USize64.ofNatTruncate n.toNat = USize64.ofBitVec n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, ofNat_bitVecToNat]

@[simp] theorem USize64.ofFin_mk {n : Nat} (hn) : USize64.ofFin (Fin.mk n hn) = USize64.ofNatLT n hn := (rfl)

@[simp] theorem USize64.ofFin_bitVecToFin (n : BitVec 64) : USize64.ofFin n.toFin = USize64.ofBitVec n := (rfl)

@[simp] theorem USize64.ofBitVec_ofNatLT {n : Nat} (hn) : USize64.ofBitVec (BitVec.ofNatLT n hn) = USize64.ofNatLT n hn := (rfl)

@[simp] theorem USize64.ofBitVec_ofFin (n) : USize64.ofBitVec (BitVec.ofFin n) = USize64.ofFin n := (rfl)

@[simp] theorem BitVec.ofNat_uISize64ToNat (n : USize64) : BitVec.ofNat 64 n.toNat = n.toBitVec :=
  BitVec.eq_of_toNat_eq (by simp)

@[simp] protected theorem USize64.toFin_div (a b : USize64) : (a / b).toFin = a.toFin / b.toFin := (rfl)

@[simp] theorem UInt8.toUSize64_div (a b : UInt8) : (a / b).toUSize64 = a.toUSize64 / b.toUSize64 := (rfl)

@[simp] theorem UInt16.toUSize64_div (a b : UInt16) : (a / b).toUSize64 = a.toUSize64 / b.toUSize64 := (rfl)

@[simp] theorem UInt32.toUSize64_div (a b : UInt32) : (a / b).toUSize64 = a.toUSize64 / b.toUSize64 := (rfl)

@[simp] theorem USize.toUSize64_div (a b : USize) : (a / b).toUSize64 = a.toUSize64 / b.toUSize64 := (rfl)

theorem USize64.toUInt8_div (a b : USize64) (ha : a < 256) (hb : b < 256) : (a / b).toUInt8 = a.toUInt8 / b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem USize64.toUInt16_div (a b : USize64) (ha : a < 65536) (hb : b < 65536) : (a / b).toUInt16 = a.toUInt16 / b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem USize64.toUInt32_div (a b : USize64) (ha : a < 4294967296) (hb : b < 4294967296) : (a / b).toUInt32 = a.toUInt32 / b.toUInt32 :=
  UInt32.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem USize64.toUSize_div (a b : USize64) (ha : a < 4294967296) (hb : b < 4294967296) : (a / b).toUSize = a.toUSize / b.toUSize :=
  USize.toNat.inj (Nat.div_mod_eq_mod_div_mod (Nat.lt_of_lt_of_le ha UInt32.size_le_usizeSize) (Nat.lt_of_lt_of_le hb UInt32.size_le_usizeSize))

theorem USize64.toUSize_div_of_toNat_lt (a b : USize64) (ha : a.toNat < USize.size) (hb : b.toNat < USize.size) :
    (a / b).toUSize = a.toUSize / b.toUSize :=
  USize.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

@[simp] protected theorem USize64.toFin_mod (a b : USize64) : (a % b).toFin = a.toFin % b.toFin := (rfl)

@[simp] theorem UInt8.toUSize64_mod (a b : UInt8) : (a % b).toUSize64 = a.toUSize64 % b.toUSize64 := (rfl)

@[simp] theorem UInt16.toUSize64_mod (a b : UInt16) : (a % b).toUSize64 = a.toUSize64 % b.toUSize64 := (rfl)

@[simp] theorem UInt32.toUSize64_mod (a b : UInt32) : (a % b).toUSize64 = a.toUSize64 % b.toUSize64 := (rfl)

@[simp] theorem USize.toUSize64_mod (a b : USize) : (a % b).toUSize64 = a.toUSize64 % b.toUSize64 := (rfl)

theorem USize64.toUInt8_mod (a b : USize64) (ha : a < 256) (hb : b < 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem USize64.toUInt16_mod (a b : USize64) (ha : a < 65536) (hb : b < 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem USize64.toUInt32_mod (a b : USize64) (ha : a < 4294967296) (hb : b < 4294967296) : (a % b).toUInt32 = a.toUInt32 % b.toUInt32 :=
  UInt32.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem USize64.toUSize_mod (a b : USize64) (ha : a < 4294967296) (hb : b < 4294967296) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (Nat.mod_mod_eq_mod_mod_mod (Nat.lt_of_lt_of_le ha UInt32.size_le_usizeSize) (Nat.lt_of_lt_of_le hb UInt32.size_le_usizeSize))

theorem USize64.toUSize_mod_of_toNat_lt (a b : USize64) (ha : a.toNat < USize.size) (hb : b.toNat < USize.size) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem USize64.toUInt8_mod_of_dvd (a b : USize64) (hb : b.toNat ∣ 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem USize64.toUInt16_mod_of_dvd (a b : USize64)(hb : b.toNat ∣ 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem USize64.toUInt32_mod_of_dvd (a b : USize64) (hb : b.toNat ∣ 4294967296) : (a % b).toUInt32 = a.toUInt32 % b.toUInt32 :=
  UInt32.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem USize64.toUSize_mod_of_dvd (a b : USize64) (hb : b.toNat ∣ 4294967296) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (Nat.mod_mod_eq_mod_mod_mod_of_dvd (Nat.dvd_trans hb UInt32.size_dvd_usizeSize))

theorem USize64.toUSize_mod_of_dvd_usizeSize (a b : USize64) (hb : b.toNat ∣ USize.size) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

@[simp] protected theorem USize64.toFin_add (a b : USize64) : (a + b).toFin = a.toFin + b.toFin := (rfl)

@[simp] theorem USize64.toUInt8_add (a b : USize64) : (a + b).toUInt8 = a.toUInt8 + b.toUInt8 := UInt8.toNat.inj (by simp)

@[simp] theorem USize64.toUInt16_add (a b : USize64) : (a + b).toUInt16 = a.toUInt16 + b.toUInt16 := UInt16.toNat.inj (by simp)

@[simp] theorem USize64.toUInt32_add (a b : USize64) : (a + b).toUInt32 = a.toUInt32 + b.toUInt32 := UInt32.toNat.inj (by simp)

@[simp] theorem USize64.toUSize_add (a b : USize64) : (a + b).toUSize = a.toUSize + b.toUSize := USize.toNat.inj (by simp)

@[simp] theorem UInt8.toUSize64_add (a b : UInt8) : (a + b).toUSize64 = (a.toUSize64 + b.toUSize64) % 256 := USize64.toNat.inj (by simp)

@[simp] theorem UInt16.toUSize64_add (a b : UInt16) : (a + b).toUSize64 = (a.toUSize64 + b.toUSize64) % 65536 := USize64.toNat.inj (by simp)

@[simp] theorem UInt32.toUSize64_add (a b : UInt32) : (a + b).toUSize64 = (a.toUSize64 + b.toUSize64) % 4294967296 := USize64.toNat.inj (by simp)

@[simp] protected theorem USize64.toFin_sub (a b : USize64) : (a - b).toFin = a.toFin - b.toFin := (rfl)

@[simp] protected theorem USize64.toFin_mul (a b : USize64) : (a * b).toFin = a.toFin * b.toFin := (rfl)

@[simp] theorem USize64.toUInt8_mul (a b : USize64) : (a * b).toUInt8 = a.toUInt8 * b.toUInt8 := UInt8.toNat.inj (by simp)

@[simp] theorem USize64.toUInt16_mul (a b : USize64) : (a * b).toUInt16 = a.toUInt16 * b.toUInt16 := UInt16.toNat.inj (by simp)

@[simp] theorem USize64.toUInt32_mul (a b : USize64) : (a * b).toUInt32 = a.toUInt32 * b.toUInt32 := UInt32.toNat.inj (by simp)

@[simp] theorem USize64.toUSize_mul (a b : USize64) : (a * b).toUSize = a.toUSize * b.toUSize := USize.toNat.inj (by simp)

@[simp] theorem UInt8.toUSize64_mul (a b : UInt8) : (a * b).toUSize64 = (a.toUSize64 * b.toUSize64) % 256 := USize64.toNat.inj (by simp)

@[simp] theorem UInt16.toUSize64_mul (a b : UInt16) : (a * b).toUSize64 = (a.toUSize64 * b.toUSize64) % 65536 := USize64.toNat.inj (by simp)

@[simp] theorem UInt32.toUSize64_mul (a b : UInt32) : (a * b).toUSize64 = (a.toUSize64 * b.toUSize64) % 4294967296 := USize64.toNat.inj (by simp)

theorem USize64.toUInt8_eq (a b : USize64) : a.toUInt8 = b.toUInt8 ↔ a % 256 = b % 256 := by
  simp [← UInt8.toNat_inj, ← USize64.toNat_inj]

theorem USize64.toUInt16_eq (a b : USize64) : a.toUInt16 = b.toUInt16 ↔ a % 65536 = b % 65536 := by
  simp [← UInt16.toNat_inj, ← USize64.toNat_inj]

theorem USize64.toUInt32_eq (a b : USize64) : a.toUInt32 = b.toUInt32 ↔ a % 4294967296 = b % 4294967296 := by
  simp [← UInt32.toNat_inj, ← USize64.toNat_inj]

theorem UInt8.toUSize64_eq_mod_256_iff (a : UInt8) (b : USize64) : a.toUSize64 = b % 256 ↔ a = b.toUInt8 := by
  simp [← UInt8.toNat_inj, ← USize64.toNat_inj]

theorem UInt16.toUSize64_eq_mod_65536_iff (a : UInt16) (b : USize64) : a.toUSize64 = b % 65536 ↔ a = b.toUInt16 := by
  simp [← UInt16.toNat_inj, ← USize64.toNat_inj]

theorem UInt32.toUSize64_eq_mod_4294967296_iff (a : UInt32) (b : USize64) : a.toUSize64 = b % 4294967296 ↔ a = b.toUInt32 := by
  simp [← UInt32.toNat_inj, ← USize64.toNat_inj]

theorem USize.toUSize64_eq_mod_usizeSize_iff (a : USize) (b : USize64) : a.toUSize64 = b % USize64.ofNat USize.size ↔ a = b.toUSize := by
  simp [← USize.toNat_inj, ← USize64.toNat_inj, USize.size_eq_two_pow]
  cases System.Platform.numBits_eq <;> simp_all

theorem UInt8.toUSize64_inj {a b : UInt8} : a.toUSize64 = b.toUSize64 ↔ a = b :=
  ⟨fun h => by rw [← toUInt8_toUSize64 a, h, toUInt8_toUSize64], by rintro rfl; rfl⟩

theorem UInt16.toUSize64_inj {a b : UInt16} : a.toUSize64 = b.toUSize64 ↔ a = b :=
  ⟨fun h => by rw [← toUInt16_toUSize64 a, h, toUInt16_toUSize64], by rintro rfl; rfl⟩

theorem UInt32.toUSize64_inj {a b : UInt32} : a.toUSize64 = b.toUSize64 ↔ a = b :=
  ⟨fun h => by rw [← toUInt32_toUSize64 a, h, toUInt32_toUSize64], by rintro rfl; rfl⟩

theorem USize.toUSize64_inj {a b : USize} : a.toUSize64 = b.toUSize64 ↔ a = b :=
  ⟨fun h => by rw [← toUSize_toUSize64 a, h, toUSize_toUSize64], by rintro rfl; rfl⟩

theorem USize64.lt_iff_toFin_lt {a b : USize64} : a < b ↔ a.toFin < b.toFin := Iff.rfl

theorem USize64.le_iff_toFin_le {a b : USize64} : a ≤ b ↔ a.toFin ≤ b.toFin := Iff.rfl

@[simp] theorem UInt8.toUSize64_lt {a b : UInt8} : a.toUSize64 < b.toUSize64 ↔ a < b := by
  simp [lt_iff_toNat_lt, USize64.lt_iff_toNat_lt]

@[simp] theorem UInt16.toUSize64_lt {a b : UInt16} : a.toUSize64 < b.toUSize64 ↔ a < b := by
  simp [lt_iff_toNat_lt, USize64.lt_iff_toNat_lt]

@[simp] theorem UInt32.toUSize64_lt {a b : UInt32} : a.toUSize64 < b.toUSize64 ↔ a < b := by
  simp [lt_iff_toNat_lt, USize64.lt_iff_toNat_lt]

@[simp] theorem USize.toUSize64_lt {a b : USize} : a.toUSize64 < b.toUSize64 ↔ a < b := by
  simp [lt_iff_toNat_lt, USize64.lt_iff_toNat_lt]

@[simp] theorem USize64.toUInt8_lt {a b : USize64} : a.toUInt8 < b.toUInt8 ↔ a % 256 < b % 256 := by
  simp [lt_iff_toNat_lt, UInt8.lt_iff_toNat_lt]

@[simp] theorem USize64.toUInt16_lt {a b : USize64} : a.toUInt16 < b.toUInt16 ↔ a % 65536 < b % 65536 := by
  simp [lt_iff_toNat_lt, UInt16.lt_iff_toNat_lt]

@[simp] theorem USize64.toUInt32_lt {a b : USize64} : a.toUInt32 < b.toUInt32 ↔ a % 4294967296 < b % 4294967296 := by
  simp [lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt]

@[simp] theorem USize64.toUSize_lt {a b : USize64} : a.toUSize < b.toUSize ↔ a % USize64.ofNat USize.size < b % USize64.ofNat USize.size := by
  simp only [USize.lt_iff_toNat_lt, toNat_toUSize, lt_iff_toNat_lt, USize64.toNat_mod, toNat_ofNat', Nat.reducePow]
  cases System.Platform.numBits_eq <;> simp_all [USize.size]

@[simp] theorem UInt8.toUSize64_le {a b : UInt8} : a.toUSize64 ≤ b.toUSize64 ↔ a ≤ b := by
  simp [le_iff_toNat_le, USize64.le_iff_toNat_le]

@[simp] theorem UInt16.toUSize64_le {a b : UInt16} : a.toUSize64 ≤ b.toUSize64 ↔ a ≤ b := by
  simp [le_iff_toNat_le, USize64.le_iff_toNat_le]

@[simp] theorem UInt32.toUSize64_le {a b : UInt32} : a.toUSize64 ≤ b.toUSize64 ↔ a ≤ b := by
  simp [le_iff_toNat_le, USize64.le_iff_toNat_le]

@[simp] theorem USize.toUSize64_le {a b : USize} : a.toUSize64 ≤ b.toUSize64 ↔ a ≤ b := by
  simp [le_iff_toNat_le, USize64.le_iff_toNat_le]

@[simp] theorem USize64.toUInt8_le {a b : USize64} : a.toUInt8 ≤ b.toUInt8 ↔ a % 256 ≤ b % 256 := by
  simp [le_iff_toNat_le, UInt8.le_iff_toNat_le]

@[simp] theorem USize64.toUInt16_le {a b : USize64} : a.toUInt16 ≤ b.toUInt16 ↔ a % 65536 ≤ b % 65536 := by
  simp [le_iff_toNat_le, UInt16.le_iff_toNat_le]

@[simp] theorem USize64.toUInt32_le {a b : USize64} : a.toUInt32 ≤ b.toUInt32 ↔ a % 4294967296 ≤ b % 4294967296 := by
  simp [le_iff_toNat_le, UInt32.le_iff_toNat_le]

@[simp] theorem USize64.toUSize_le {a b : USize64} : a.toUSize ≤ b.toUSize ↔ a % USize64.ofNat USize.size ≤ b % USize64.ofNat USize.size := by
  simp only [USize.le_iff_toNat_le, toNat_toUSize, le_iff_toNat_le, USize64.toNat_mod]
  cases System.Platform.numBits_eq <;> simp_all [USize.size]

@[simp] theorem USize64.toUInt8_neg (a : USize64) : (-a).toUInt8 = -a.toUInt8 := UInt8.toBitVec_inj.1 (by simp)

@[simp] theorem USize64.toUInt16_neg (a : USize64) : (-a).toUInt16 = -a.toUInt16 := UInt16.toBitVec_inj.1 (by simp)

@[simp] theorem USize64.toUInt32_neg (a : USize64) : (-a).toUInt32 = -a.toUInt32 := UInt32.toBitVec_inj.1 (by simp)

@[simp] theorem USize64.toUSize_neg (a : USize64) : (-a).toUSize = -a.toUSize := USize.toBitVec_inj.1 (by simp)

@[simp] theorem UInt8.toUSize64_neg (a : UInt8) : (-a).toUSize64 = -a.toUSize64 % 256 := by
  simp [UInt8.toUSize64_eq_mod_256_iff]

@[simp] theorem UInt16.toUSize64_neg (a : UInt16) : (-a).toUSize64 = -a.toUSize64 % 65536 := by
  simp [UInt16.toUSize64_eq_mod_65536_iff]

@[simp] theorem UInt32.toUSize64_neg (a : UInt32) : (-a).toUSize64 = -a.toUSize64 % 4294967296 := by
  simp [UInt32.toUSize64_eq_mod_4294967296_iff]

@[simp] theorem USize.toUSize64_neg (a : USize) : (-a).toUSize64 = -a.toUSize64 % USize64.ofNat USize.size := by
  simp [USize.toUSize64_eq_mod_usizeSize_iff]

@[simp] theorem USize64.toNat_neg (a : USize64) : (-a).toNat = (USize64.size - a.toNat) % USize64.size := (rfl)

protected theorem USize64.sub_eq_add_neg (a b : USize64) : a - b = a + (-b) := USize64.toBitVec_inj.1 (BitVec.sub_eq_add_neg _ _)

protected theorem USize64.add_neg_eq_sub {a b : USize64} : a + -b = a - b := USize64.toBitVec_inj.1 BitVec.add_neg_eq_sub

theorem USize64.neg_one_eq : (-1 : USize64) = 18446744073709551615 := (rfl)

theorem USize64.toBitVec_zero : toBitVec 0 = 0#64 := (rfl)

theorem USize64.toBitVec_one : toBitVec 1 = 1#64 := (rfl)

theorem USize64.neg_eq_neg_one_mul (a : USize64) : -a = -1 * a := by
  apply USize64.toBitVec_inj.1
  rw [USize64.toBitVec_neg, USize64.toBitVec_mul, USize64.toBitVec_neg, USize64.toBitVec_one, BitVec.neg_eq_neg_one_mul]

theorem USize64.sub_eq_add_mul (a b : USize64) : a - b = a + 18446744073709551615 * b := by
  rw [USize64.sub_eq_add_neg, neg_eq_neg_one_mul, neg_one_eq]

@[simp] theorem USize.ofNat_uISize64Size_sub_one : USize.ofNat (USize64.size - 1) = USize.ofNatLT (USize.size - 1) (Nat.sub_one_lt (Nat.pos_iff_ne_zero.1 size_pos)) :=
  USize.toNat.inj (by simp)

@[simp] theorem USize64.toUInt8_sub (a b : USize64) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := by
  simp [USize64.sub_eq_add_neg, UInt8.sub_eq_add_neg]

@[simp] theorem USize64.toUInt16_sub (a b : USize64) : (a - b).toUInt16 = a.toUInt16 - b.toUInt16 := by
  simp [USize64.sub_eq_add_neg, UInt16.sub_eq_add_neg]

@[simp] theorem USize64.toUInt32_sub (a b : USize64) : (a - b).toUInt32 = a.toUInt32 - b.toUInt32 := by
  simp [USize64.sub_eq_add_neg, UInt32.sub_eq_add_neg]

@[simp] theorem USize64.toUSize_sub (a b : USize64) : (a - b).toUSize = a.toUSize - b.toUSize := by
  simp [USize64.sub_eq_add_neg, USize.sub_eq_add_neg]

@[simp] theorem UInt8.toUSize64_sub (a b : UInt8) : (a - b).toUSize64 = (a.toUSize64 - b.toUSize64) % 256 := by
  simp [UInt8.toUSize64_eq_mod_256_iff]

@[simp] theorem UInt16.toUSize64_sub (a b : UInt16) : (a - b).toUSize64 = (a.toUSize64 - b.toUSize64) % 65536 := by
  simp [UInt16.toUSize64_eq_mod_65536_iff]

@[simp] theorem UInt32.toUSize64_sub (a b : UInt32) : (a - b).toUSize64 = (a.toUSize64 - b.toUSize64) % 4294967296 := by
  simp [UInt32.toUSize64_eq_mod_4294967296_iff]

@[simp] theorem USize.toUSize64_sub (a b : USize) : (a - b).toUSize64 = (a.toUSize64 - b.toUSize64) % USize64.ofNat USize.size := by
  simp [USize.toUSize64_eq_mod_usizeSize_iff]

@[simp] theorem USize64.ofBitVec_neg (b : BitVec 64) : USize64.ofBitVec (-b) = -USize64.ofBitVec b := (rfl)

@[simp] theorem USize64.ofFin_div (a b : Fin USize64.size) : USize64.ofFin (a / b) = USize64.ofFin a / USize64.ofFin b := (rfl)

@[simp] theorem USize64.ofBitVec_div (a b : BitVec 64) : USize64.ofBitVec (a / b) = USize64.ofBitVec a / USize64.ofBitVec b := (rfl)

@[simp] theorem USize64.ofFin_mod (a b : Fin USize64.size) : USize64.ofFin (a % b) = USize64.ofFin a % USize64.ofFin b := (rfl)

@[simp] theorem USize64.ofBitVec_mod (a b : BitVec 64) : USize64.ofBitVec (a % b) = USize64.ofBitVec a % USize64.ofBitVec b := (rfl)

theorem USize64.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : USize64) : USize64.ofNat a = b ↔ a % 2 ^ 64 = b.toNat := by
  simp [← USize64.toNat_inj]

@[simp] theorem USize64.ofNat_div {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    USize64.ofNat (a / b) = USize64.ofNat a / USize64.ofNat b := by
  simp [USize64.ofNat_eq_iff_mod_eq_toNat, Nat.div_mod_eq_mod_div_mod ha hb]

@[simp] theorem USize64.ofNatLT_div {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    USize64.ofNatLT (a / b) (Nat.div_lt_of_lt ha) = USize64.ofNatLT a ha / USize64.ofNatLT b hb := by
  simp [USize64.ofNatLT_eq_ofNat, USize64.ofNat_div ha hb]

@[simp] theorem USize64.ofNat_mod {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    USize64.ofNat (a % b) = USize64.ofNat a % USize64.ofNat b := by
  simp [USize64.ofNat_eq_iff_mod_eq_toNat, Nat.mod_mod_eq_mod_mod_mod ha hb]

@[simp] theorem USize64.ofNatLT_mod {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    USize64.ofNatLT (a % b) (Nat.mod_lt_of_lt ha) = USize64.ofNatLT a ha % USize64.ofNatLT b hb := by
  simp [USize64.ofNatLT_eq_ofNat, USize64.ofNat_mod ha hb]

@[simp] theorem USize64.ofInt_one : ofInt 1 = 1 := (rfl)

@[simp] theorem USize64.ofInt_neg_one : ofInt (-1) = -1 := (rfl)

@[simp] theorem USize64.ofNat_add (a b : Nat) : USize64.ofNat (a + b) = USize64.ofNat a + USize64.ofNat b := by
  simp [USize64.ofNat_eq_iff_mod_eq_toNat]

@[simp] theorem USize64.ofInt_add (x y : Int) : USize64.ofInt (x + y) = USize64.ofInt x + USize64.ofInt y := by
  dsimp only [USize64.ofInt]
  rw [Int.add_emod]
  have h₁ : 0 ≤ x % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ x % 2 ^ 64 + y % 2 ^ 64 := Int.add_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_add h₁ h₂]
  have : (2 ^ 64 : Int).toNat = 2 ^ 64 := (rfl)
  rw [this, USize64.ofNat_mod_size, USize64.ofNat_add]

@[simp] theorem USize64.ofNatLT_add {a b : Nat} (hab : a + b < 2 ^ 64) :
    USize64.ofNatLT (a + b) hab = USize64.ofNatLT a (Nat.lt_of_add_right_lt hab) + USize64.ofNatLT b (Nat.lt_of_add_left_lt hab) := by
  simp [USize64.ofNatLT_eq_ofNat]

@[simp] theorem USize64.ofFin_add (a b : Fin USize64.size) : USize64.ofFin (a + b) = USize64.ofFin a + USize64.ofFin b := (rfl)

@[simp] theorem USize64.ofBitVec_add (a b : BitVec 64) : USize64.ofBitVec (a + b) = USize64.ofBitVec a + USize64.ofBitVec b := (rfl)

@[simp] theorem USize64.ofFin_sub (a b : Fin USize64.size) : USize64.ofFin (a - b) = USize64.ofFin a - USize64.ofFin b := (rfl)

@[simp] theorem USize64.ofBitVec_sub (a b : BitVec 64) : USize64.ofBitVec (a - b) = USize64.ofBitVec a - USize64.ofBitVec b := (rfl)

@[simp] protected theorem USize64.add_sub_cancel (a b : USize64) : a + b - b = a := USize64.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)

theorem USize64.ofNat_sub {a b : Nat} (hab : b ≤ a) : USize64.ofNat (a - b) = USize64.ofNat a - USize64.ofNat b := by
  rw [(Nat.sub_add_cancel hab ▸ USize64.ofNat_add (a - b) b :), USize64.add_sub_cancel]

theorem USize64.ofNatLT_sub {a b : Nat} (ha : a < 2 ^ 64) (hab : b ≤ a) :
    USize64.ofNatLT (a - b) (Nat.sub_lt_of_lt ha) = USize64.ofNatLT a ha - USize64.ofNatLT b (Nat.lt_of_le_of_lt hab ha) := by
  simp [USize64.ofNatLT_eq_ofNat, USize64.ofNat_sub hab]

@[simp] theorem USize64.ofNat_mul (a b : Nat) : USize64.ofNat (a * b) = USize64.ofNat a * USize64.ofNat b := by
  simp [USize64.ofNat_eq_iff_mod_eq_toNat]

@[simp] theorem USize64.ofInt_mul (x y : Int) : ofInt (x * y) = ofInt x * ofInt y := by
  dsimp only [USize64.ofInt]
  rw [Int.mul_emod]
  have h₁ : 0 ≤ x % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ (x % 2 ^ 64) * (y % 2 ^ 64) := Int.mul_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_mul h₁ h₂]
  have : (2 ^ 64 : Int).toNat = 2 ^ 64 := (rfl)
  rw [this, USize64.ofNat_mod_size, USize64.ofNat_mul]

@[simp] theorem USize64.ofNatLT_mul {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hab : a * b < 2 ^ 64) :
    USize64.ofNatLT (a * b) hab = USize64.ofNatLT a ha * USize64.ofNatLT b hb := by
  simp [USize64.ofNatLT_eq_ofNat]

@[simp] theorem USize64.ofFin_mul (a b : Fin USize64.size) : USize64.ofFin (a * b) = USize64.ofFin a * USize64.ofFin b := (rfl)

@[simp] theorem USize64.ofBitVec_mul (a b : BitVec 64) : USize64.ofBitVec (a * b) = USize64.ofBitVec a * USize64.ofBitVec b := (rfl)

theorem USize64.ofFin_lt_iff_lt {a b : Fin USize64.size} : USize64.ofFin a < USize64.ofFin b ↔ a < b := Iff.rfl

theorem USize64.ofFin_le_iff_le {a b : Fin USize64.size} : USize64.ofFin a ≤ USize64.ofFin b ↔ a ≤ b := Iff.rfl

theorem USize64.ofBitVec_lt_iff_lt {a b : BitVec 64} : USize64.ofBitVec a < USize64.ofBitVec b ↔ a < b := Iff.rfl

theorem USize64.ofBitVec_le_iff_le {a b : BitVec 64} : USize64.ofBitVec a ≤ USize64.ofBitVec b ↔ a ≤ b := Iff.rfl

theorem USize64.ofNatLT_lt_iff_lt {a b : Nat} (ha : a < USize64.size) (hb : b < USize64.size) :
    USize64.ofNatLT a ha < USize64.ofNatLT b hb ↔ a < b := Iff.rfl

theorem USize64.ofNatLT_le_iff_le {a b : Nat} (ha : a < USize64.size) (hb : b < USize64.size) :
    USize64.ofNatLT a ha ≤ USize64.ofNatLT b hb ↔ a ≤ b := Iff.rfl

theorem USize64.ofNat_lt_iff_lt {a b : Nat} (ha : a < USize64.size) (hb : b < USize64.size) :
    USize64.ofNat a < USize64.ofNat b ↔ a < b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_lt_iff_lt]

theorem USize64.ofNat_le_iff_le {a b : Nat} (ha : a < USize64.size) (hb : b < USize64.size) :
    USize64.ofNat a ≤ USize64.ofNat b ↔ a ≤ b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_le_iff_le]

theorem USize64.toNat_one : (1 : USize64).toNat = 1 := (rfl)

theorem USize64.zero_lt_one : (0 : USize64) < 1 := by simp

theorem USize64.zero_ne_one : (0 : USize64) ≠ 1 := by simp

protected theorem USize64.add_assoc (a b c : USize64) : a + b + c = a + (b + c) :=
  USize64.toBitVec_inj.1 (BitVec.add_assoc _ _ _)

instance : Std.Associative (α := USize64) (· + ·) := ⟨USize64.add_assoc⟩

protected theorem USize64.add_comm (a b : USize64) : a + b = b + a := USize64.toBitVec_inj.1 (BitVec.add_comm _ _)

instance : Std.Commutative (α := USize64) (· + ·) := ⟨USize64.add_comm⟩

@[simp] protected theorem USize64.add_zero (a : USize64) : a + 0 = a := USize64.toBitVec_inj.1 (BitVec.add_zero _)

@[simp] protected theorem USize64.zero_add (a : USize64) : 0 + a = a := USize64.toBitVec_inj.1 (BitVec.zero_add _)

instance : Std.LawfulIdentity (α := USize64) (· + ·) 0 where
  left_id := USize64.zero_add
  right_id := USize64.add_zero

@[simp] protected theorem USize64.sub_zero (a : USize64) : a - 0 = a := USize64.toBitVec_inj.1 (BitVec.sub_zero _)

@[simp] protected theorem USize64.zero_sub (a : USize64) : 0 - a = -a := USize64.toBitVec_inj.1 (BitVec.zero_sub _)

@[simp] protected theorem USize64.sub_self (a : USize64) : a - a = 0 := USize64.toBitVec_inj.1 (BitVec.sub_self _)

protected theorem USize64.add_left_neg (a : USize64) : -a + a = 0 := USize64.toBitVec_inj.1 (BitVec.add_left_neg _)

protected theorem USize64.add_right_neg (a : USize64) : a + -a = 0 := USize64.toBitVec_inj.1 (BitVec.add_right_neg _)

@[simp] protected theorem USize64.neg_zero : -(0 : USize64) = 0 := (rfl)

@[simp] protected theorem USize64.sub_add_cancel (a b : USize64) : a - b + b = a :=
  USize64.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)

protected theorem USize64.eq_sub_iff_add_eq {a b c : USize64} : a = c - b ↔ a + b = c := by
  simpa [← USize64.toBitVec_inj] using BitVec.eq_sub_iff_add_eq

protected theorem USize64.sub_eq_iff_eq_add {a b c : USize64} : a - b = c ↔ a = c + b := by
  simpa [← USize64.toBitVec_inj] using BitVec.sub_eq_iff_eq_add

@[simp] protected theorem USize64.neg_neg {a : USize64} : - -a = a := USize64.toBitVec_inj.1 BitVec.neg_neg

@[simp] protected theorem UInt32.neg_inj {a b : UInt32} : -a = -b ↔ a = b := by simp [← UInt32.toBitVec_inj]
@[simp] protected theorem USize64.neg_inj {a b : USize64} : -a = -b ↔ a = b := by simp [← USize64.toBitVec_inj]

@[simp] protected theorem UInt32.neg_ne_zero {a : UInt32} : -a ≠ 0 ↔ a ≠ 0 := by simp [← UInt32.toBitVec_inj]
@[simp] protected theorem USize64.neg_ne_zero {a : USize64} : -a ≠ 0 ↔ a ≠ 0 := by simp [← USize64.toBitVec_inj]

protected theorem USize64.neg_add {a b : USize64} : - (a + b) = -a - b := USize64.toBitVec_inj.1 BitVec.neg_add

@[simp] protected theorem USize64.sub_neg {a b : USize64} : a - -b = a + b := USize64.toBitVec_inj.1 BitVec.sub_neg

@[simp] protected theorem USize64.neg_sub {a b : USize64} : -(a - b) = b - a := by
  rw [USize64.sub_eq_add_neg, USize64.neg_add, USize64.sub_neg, USize64.add_comm, ← USize64.sub_eq_add_neg]

@[simp] protected theorem USize64.ofInt_neg (x : Int) : ofInt (-x) = -ofInt x := by
  rw [Int.neg_eq_neg_one_mul, ofInt_mul, ofInt_neg_one, ← USize64.neg_eq_neg_one_mul]

@[simp] protected theorem USize64.add_left_inj {a b : USize64} (c : USize64) : (a + c = b + c) ↔ a = b := by
  simp [← USize64.toBitVec_inj]

@[simp] protected theorem USize64.add_right_inj {a b : USize64} (c : USize64) : (c + a = c + b) ↔ a = b := by
  simp [← USize64.toBitVec_inj]

@[simp] protected theorem USize64.sub_left_inj {a b : USize64} (c : USize64) : (a - c = b - c) ↔ a = b := by
  simp [← USize64.toBitVec_inj]

@[simp] protected theorem USize64.sub_right_inj {a b : USize64} (c : USize64) : (c - a = c - b) ↔ a = b := by
  simp [← USize64.toBitVec_inj]

@[simp] theorem USize64.add_eq_right {a b : USize64} : a + b = b ↔ a = 0 := by
  simp [← USize64.toBitVec_inj]

@[simp] theorem USize64.add_eq_left {a b : USize64} : a + b = a ↔ b = 0 := by
  simp [← USize64.toBitVec_inj]

@[simp] theorem USize64.right_eq_add {a b : USize64} : b = a + b ↔ a = 0 := by
  simp [← USize64.toBitVec_inj]

@[simp] theorem USize64.left_eq_add {a b : USize64} : a = a + b ↔ b = 0 := by
  simp [← USize64.toBitVec_inj]

protected theorem USize64.mul_comm (a b : USize64) : a * b = b * a := USize64.toBitVec_inj.1 (BitVec.mul_comm _ _)

instance : Std.Commutative (α := USize64) (· * ·) := ⟨USize64.mul_comm⟩

protected theorem USize64.mul_assoc (a b c : USize64) : a * b * c = a * (b * c) := USize64.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)

instance : Std.Associative (α := USize64) (· * ·) := ⟨USize64.mul_assoc⟩

@[simp] theorem USize64.mul_one (a : USize64) : a * 1 = a := USize64.toBitVec_inj.1 (BitVec.mul_one _)

@[simp] theorem USize64.one_mul (a : USize64) : 1 * a = a := USize64.toBitVec_inj.1 (BitVec.one_mul _)

instance : Std.LawfulCommIdentity (α := USize64) (· * ·) 1 where
  right_id := USize64.mul_one

@[simp] theorem USize64.mul_zero {a : USize64} : a * 0 = 0 := USize64.toBitVec_inj.1 BitVec.mul_zero

@[simp] theorem USize64.zero_mul {a : USize64} : 0 * a = 0 := USize64.toBitVec_inj.1 BitVec.zero_mul

@[simp] protected theorem USize64.pow_zero (x : USize64) : x ^ 0 = 1 := (rfl)

protected theorem USize64.pow_succ (x : USize64) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)

@[simp, int_toBitVec] protected theorem USize64.toBitVec_pow (a : USize64) (n : Nat) : (a ^ n).toBitVec = a.toBitVec ^ n := by
  induction n <;> simp [*, USize64.pow_succ, BitVec.pow_succ]

@[simp] protected theorem USize64.ofBitVec_pow (a : BitVec 64) (n : Nat) : ofBitVec (a ^ n) = ofBitVec a ^ n := by
  induction n <;> simp [*, USize64.pow_succ, BitVec.pow_succ]

protected theorem USize64.mul_add {a b c : USize64} : a * (b + c) = a * b + a * c :=
    USize64.toBitVec_inj.1 BitVec.mul_add

protected theorem USize64.add_mul {a b c : USize64} : (a + b) * c = a * c + b * c := by
  rw [USize64.mul_comm, USize64.mul_add, USize64.mul_comm a c, USize64.mul_comm c b]

protected theorem USize64.mul_succ {a b : USize64} : a * (b + 1) = a * b + a := by simp [USize64.mul_add]

protected theorem USize64.succ_mul {a b : USize64} : (a + 1) * b = a * b + b := by simp [USize64.add_mul]

protected theorem USize64.two_mul {a : USize64} : 2 * a = a + a := USize64.toBitVec_inj.1 BitVec.two_mul

protected theorem USize64.mul_two {a : USize64} : a * 2 = a + a := USize64.toBitVec_inj.1 BitVec.mul_two

protected theorem USize64.neg_mul (a b : USize64) : -a * b = -(a * b) := USize64.toBitVec_inj.1 (BitVec.neg_mul _ _)

protected theorem USize64.mul_neg (a b : USize64) : a * -b = -(a * b) := USize64.toBitVec_inj.1 (BitVec.mul_neg _ _)

protected theorem USize64.neg_mul_neg (a b : USize64) : -a * -b = a * b := USize64.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)

protected theorem USize64.neg_mul_comm (a b : USize64) : -a * b = a * -b := USize64.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)

protected theorem USize64.mul_sub {a b c : USize64} : a * (b - c) = a * b - a * c := USize64.toBitVec_inj.1 BitVec.mul_sub

protected theorem USize64.sub_mul {a b c : USize64} : (a - b) * c = a * c - b * c := by
  rw [USize64.mul_comm, USize64.mul_sub, USize64.mul_comm, USize64.mul_comm c]

theorem USize64.neg_add_mul_eq_mul_not {a b : USize64} : -(a + a * b) = a * ~~~b :=
  USize64.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not

theorem USize64.neg_mul_not_eq_add_mul {a b : USize64} : -(a * ~~~b) = a + a * b :=
  USize64.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul

protected theorem USize64.le_of_lt {a b : USize64} : a < b → a ≤ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le] using Nat.le_of_lt

protected theorem USize64.lt_of_le_of_ne {a b : USize64} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← USize64.toNat_inj] using Nat.lt_of_le_of_ne

protected theorem USize64.lt_iff_le_and_ne {a b : USize64} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← USize64.toNat_inj] using Nat.lt_iff_le_and_ne

@[simp] protected theorem UInt32.not_lt_zero {a : UInt32} : ¬a < 0 := by simp [UInt32.lt_iff_toBitVec_lt]
@[simp] protected theorem USize64.not_lt_zero {a : USize64} : ¬a < 0 := by simp [USize64.lt_iff_toBitVec_lt]

@[simp] protected theorem UInt32.zero_le {a : UInt32} : 0 ≤ a := by simp [← UInt32.not_lt]
@[simp] protected theorem USize64.zero_le {a : USize64} : 0 ≤ a := by simp [← USize64.not_lt]

@[simp] protected theorem USize64.le_zero_iff {a : USize64} : a ≤ 0 ↔ a = 0 := by
  simp [USize64.le_iff_toBitVec_le, ← USize64.toBitVec_inj]

@[simp] protected theorem USize64.lt_one_iff {a : USize64} : a < 1 ↔ a = 0 := by
  simp [USize64.lt_iff_toBitVec_lt, ← USize64.toBitVec_inj]

@[simp] protected theorem USize64.zero_div {a : USize64} : 0 / a = 0 := USize64.toBitVec_inj.1 BitVec.zero_udiv

@[simp] protected theorem USize64.div_zero {a : USize64} : a / 0 = 0 := USize64.toBitVec_inj.1 BitVec.udiv_zero

@[simp] protected theorem USize64.div_one {a : USize64} : a / 1 = a := USize64.toBitVec_inj.1 BitVec.udiv_one

protected theorem USize64.div_self {a : USize64} : a / a = if a = 0 then 0 else 1 := by
  simp [← USize64.toBitVec_inj, apply_ite]

@[simp] protected theorem USize64.mod_zero {a : USize64} : a % 0 = a := USize64.toBitVec_inj.1 BitVec.umod_zero

@[simp] protected theorem USize64.zero_mod {a : USize64} : 0 % a = 0 := USize64.toBitVec_inj.1 BitVec.zero_umod

@[simp] protected theorem USize64.mod_one {a : USize64} : a % 1 = 0 := USize64.toBitVec_inj.1 BitVec.umod_one

@[simp] protected theorem USize64.mod_self {a : USize64} : a % a = 0 := USize64.toBitVec_inj.1 BitVec.umod_self

protected theorem USize64.pos_iff_ne_zero {a : USize64} : 0 < a ↔ a ≠ 0 := by simp [USize64.lt_iff_le_and_ne, Eq.comm]

protected theorem USize64.lt_of_le_of_lt {a b c : USize64} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_le_of_lt

protected theorem USize64.lt_of_lt_of_le {a b c : USize64} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_lt_of_le

protected theorem USize64.lt_or_lt_of_ne {a b : USize64} : a ≠ b → a < b ∨ b < a := by
  simpa [lt_iff_toNat_lt, ← USize64.toNat_inj] using Nat.lt_or_lt_of_ne

protected theorem USize64.lt_or_le (a b : USize64) : a < b ∨ b ≤ a := by
  simp [lt_iff_toNat_lt, le_iff_toNat_le]; omega

protected theorem USize64.le_or_lt (a b : USize64) : a ≤ b ∨ b < a := (b.lt_or_le a).symm

protected theorem USize64.le_of_eq {a b : USize64} : a = b → a ≤ b := (· ▸ USize64.le_rfl)

protected theorem USize64.le_iff_lt_or_eq {a b : USize64} : a ≤ b ↔ a < b ∨ a = b := by
  simpa [← USize64.toNat_inj, le_iff_toNat_le, lt_iff_toNat_lt] using Nat.le_iff_lt_or_eq

protected theorem USize64.lt_or_eq_of_le {a b : USize64} : a ≤ b → a < b ∨ a = b := USize64.le_iff_lt_or_eq.mp

protected theorem USize64.sub_le {a b : USize64} (hab : b ≤ a) : a - b ≤ a := by
  simp [le_iff_toNat_le, USize64.toNat_sub_of_le _ _ hab]

protected theorem USize64.sub_lt {a b : USize64} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  rw [lt_iff_toNat_lt, USize64.toNat_sub_of_le _ _ hab]
  refine Nat.sub_lt ?_ (USize64.lt_iff_toNat_lt.1 hb)
  exact USize64.lt_iff_toNat_lt.1 (USize64.lt_of_lt_of_le hb hab)

theorem USize64.lt_add_one {c : USize64} (h : c ≠ -1) : c < c + 1 :=
  USize64.lt_iff_toBitVec_lt.2 (BitVec.lt_add_one (by simpa [← USize64.toBitVec_inj] using h))

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/SInt/Lemmas.lean
-- Target: Hax/MissingLean/Init/Data/SInt/Lemmas_Int128.lean
-- ──────────────────────────────────────────────────────────────────────

set_option maxRecDepth 4000

declare_int_theorems ISize64 64

theorem ISize64.toInt.inj {x y : ISize64} (h : x.toInt = y.toInt) : x = y := ISize64.toBitVec.inj (BitVec.eq_of_toInt_eq h)

theorem ISize64.toInt_inj {x y : ISize64} : x.toInt = y.toInt ↔ x = y := ⟨ISize64.toInt.inj, fun h => h ▸ rfl⟩

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

theorem ISize64.toInt_zero : toInt 0 = 0 := by simp

theorem ISize64.toInt_minValue : ISize64.minValue.toInt = -2^63 := (rfl)

theorem ISize64.toInt_maxValue : ISize64.maxValue.toInt = 2 ^ 63 - 1 := (rfl)

@[simp] theorem ISize64.toNatClampNeg_minValue : ISize64.minValue.toNatClampNeg = 0 := (rfl)

@[simp, int_toBitVec] theorem USize64.toBitVec_toISize64 (x : USize64) : x.toISize64.toBitVec = x.toBitVec := (rfl)

@[simp] theorem ISize64.ofBitVec_uISize64ToBitVec (x : USize64) : ISize64.ofBitVec x.toBitVec = x.toISize64 := (rfl)

@[simp] theorem USize64.toUSize64_toISize64 (x : USize64) : x.toISize64.toUSize64 = x := (rfl)

@[simp] theorem ISize64.toNat_toInt (x : ISize64) : x.toInt.toNat = x.toNatClampNeg := (rfl)

@[simp] theorem ISize64.toInt_toBitVec (x : ISize64) : x.toBitVec.toInt = x.toInt := (rfl)

@[simp, int_toBitVec] theorem Int8.toBitVec_toISize64 (x : Int8) : x.toISize64.toBitVec = x.toBitVec.signExtend 64 := (rfl)

@[simp, int_toBitVec] theorem Int16.toBitVec_toISize64 (x : Int16) : x.toISize64.toBitVec = x.toBitVec.signExtend 64 := (rfl)

@[simp, int_toBitVec] theorem Int32.toBitVec_toISize64 (x : Int32) : x.toISize64.toBitVec = x.toBitVec.signExtend 64 := (rfl)

@[simp, int_toBitVec] theorem ISize64.toBitVec_toInt8 (x : ISize64) : x.toInt8.toBitVec = x.toBitVec.signExtend 8 := (rfl)

@[simp, int_toBitVec] theorem ISize64.toBitVec_toInt16 (x : ISize64) : x.toInt16.toBitVec = x.toBitVec.signExtend 16 := (rfl)

@[simp, int_toBitVec] theorem ISize64.toBitVec_toInt32 (x : ISize64) : x.toInt32.toBitVec = x.toBitVec.signExtend 32 := (rfl)

@[simp, int_toBitVec] theorem ISize64.toBitVec_toISize (x : ISize64) : x.toISize.toBitVec = x.toBitVec.signExtend System.Platform.numBits := (rfl)

@[simp, int_toBitVec] theorem ISize.toBitVec_toISize64 (x : ISize) : x.toISize64.toBitVec = x.toBitVec.signExtend 64 := (rfl)

theorem ISize64.toInt_lt (x : ISize64) : x.toInt < 2 ^ 63 := Int.lt_of_mul_lt_mul_left BitVec.two_mul_toInt_lt (by decide)

theorem ISize64.le_toInt (x : ISize64) : -2 ^ 63 ≤ x.toInt := Int.le_of_mul_le_mul_left BitVec.le_two_mul_toInt (by decide)

theorem ISize64.toInt_le (x : ISize64) : x.toInt ≤ ISize64.maxValue.toInt := Int.le_of_lt_add_one x.toInt_lt

theorem ISize64.minValue_le_toInt (x : ISize64) : ISize64.minValue.toInt ≤ x.toInt := x.le_toInt

theorem ISize.isize64MinValue_le_toInt (x : ISize) : ISize64.minValue.toInt ≤ x.toInt :=
  Int.le_trans (by decide) x.le_toInt

theorem ISize.toInt_le_isize64MaxValue (x : ISize) : x.toInt ≤ ISize64.maxValue.toInt :=
  Int.le_of_lt_add_one x.toInt_lt

theorem ISize64.toNatClampNeg_lt (x : ISize64) : x.toNatClampNeg < 2 ^ 63 := (Int.toNat_lt' (by decide)).2 x.toInt_lt

@[simp] theorem Int8.toInt_toISize64 (x : Int8) : x.toISize64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)

@[simp] theorem Int16.toInt_toISize64 (x : Int16) : x.toISize64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)

@[simp] theorem Int32.toInt_toISize64 (x : Int32) : x.toISize64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)

@[simp] theorem ISize64.toInt_toInt8 (x : ISize64) : x.toInt8.toInt = x.toInt.bmod (2 ^ 8) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)

@[simp] theorem ISize64.toInt_toInt16 (x : ISize64) : x.toInt16.toInt = x.toInt.bmod (2 ^ 16) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)

@[simp] theorem ISize64.toInt_toInt32 (x : ISize64) : x.toInt32.toInt = x.toInt.bmod (2 ^ 32) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)

@[simp] theorem ISize64.toInt_toISize (x : ISize64) : x.toISize.toInt = x.toInt.bmod (2 ^ System.Platform.numBits) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem ISize.toInt_toISize64 (x : ISize) : x.toISize64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem Int8.toNatClampNeg_toISize64 (x : Int8) : x.toISize64.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toISize64

@[simp] theorem Int16.toNatClampNeg_toISize64 (x : Int16) : x.toISize64.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toISize64

@[simp] theorem Int32.toNatClampNeg_toISize64 (x : Int32) : x.toISize64.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toISize64

@[simp] theorem ISize.toNatClampNeg_toISize64 (x : ISize) : x.toISize64.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toISize64

@[simp] theorem ISize64.toISize64_toUSize64 (x : ISize64) : x.toUSize64.toISize64 = x := (rfl)

theorem ISize64.toNat_toBitVec (x : ISize64) : x.toBitVec.toNat = x.toUSize64.toNat := (rfl)

theorem ISize64.toNat_toBitVec_of_le {x : ISize64} (hx : 0 ≤ x) : x.toBitVec.toNat = x.toNatClampNeg :=
  (x.toBitVec.toNat_toInt_of_sle hx).symm

theorem ISize64.toNat_toUSize64_of_le {x : ISize64} (hx : 0 ≤ x) : x.toUSize64.toNat = x.toNatClampNeg := by
  rw [← toNat_toBitVec, toNat_toBitVec_of_le hx]

theorem ISize64.toFin_toBitVec (x : ISize64) : x.toBitVec.toFin = x.toUSize64.toFin := (rfl)

@[simp, int_toBitVec] theorem ISize64.toBitVec_toUSize64 (x : ISize64) : x.toUSize64.toBitVec = x.toBitVec := (rfl)

@[simp] theorem USize64.ofBitVec_isize64ToBitVec (x : ISize64) : USize64.ofBitVec x.toBitVec = x.toUSize64 := (rfl)

@[simp] theorem ISize64.ofBitVec_toBitVec (x : ISize64) : ISize64.ofBitVec x.toBitVec = x := (rfl)

@[simp] theorem Int8.ofBitVec_isize64ToBitVec (x : ISize64) : Int8.ofBitVec (x.toBitVec.signExtend 8) = x.toInt8 := (rfl)

@[simp] theorem Int16.ofBitVec_isize64ToBitVec (x : ISize64) : Int16.ofBitVec (x.toBitVec.signExtend 16) = x.toInt16 := (rfl)

@[simp] theorem Int32.ofBitVec_isize64ToBitVec (x : ISize64) : Int32.ofBitVec (x.toBitVec.signExtend 32) = x.toInt32 := (rfl)

@[simp] theorem ISize64.ofBitVec_int8ToBitVec (x : Int8) : ISize64.ofBitVec (x.toBitVec.signExtend 64) = x.toISize64 := (rfl)

@[simp] theorem ISize64.ofBitVec_int16ToBitVec (x : Int16) : ISize64.ofBitVec (x.toBitVec.signExtend 64) = x.toISize64 := (rfl)

@[simp] theorem ISize64.ofBitVec_int32ToBitVec (x : Int32) : ISize64.ofBitVec (x.toBitVec.signExtend 64) = x.toISize64 := (rfl)

@[simp] theorem ISize64.ofBitVec_iSizeToBitVec (x : ISize) : ISize64.ofBitVec (x.toBitVec.signExtend 64) = x.toISize64 := (rfl)

@[simp] theorem ISize.ofBitVec_isize64ToBitVec (x : ISize64) : ISize.ofBitVec (x.toBitVec.signExtend System.Platform.numBits) = x.toISize := (rfl)

@[simp] theorem ISize64.toBitVec_ofIntLE (x : Int) (h₁ h₂) : (ISize64.ofIntLE x h₁ h₂).toBitVec = BitVec.ofInt 64 x := (rfl)

@[simp] theorem ISize64.toInt_bmod (x : ISize64) : x.toInt.bmod 18446744073709551616 = x.toInt := Int.bmod_eq_of_le x.le_toInt x.toInt_lt

@[simp] theorem BitVec.ofInt_isize64ToInt (x : ISize64) : BitVec.ofInt 64 x.toInt = x.toBitVec := BitVec.eq_of_toInt_eq (by simp)

@[simp] theorem ISize64.ofIntLE_toInt (x : ISize64) : ISize64.ofIntLE x.toInt x.minValue_le_toInt x.toInt_le = x := ISize64.toBitVec.inj (by simp)

theorem Int8.ofIntLE_isize64ToInt (x : ISize64) {h₁ h₂} : Int8.ofIntLE x.toInt h₁ h₂ = x.toInt8 := (rfl)

theorem Int16.ofIntLE_isize64ToInt (x : ISize64) {h₁ h₂} : Int16.ofIntLE x.toInt h₁ h₂ = x.toInt16 := (rfl)

theorem Int32.ofIntLE_isize64ToInt (x : ISize64) {h₁ h₂} : Int32.ofIntLE x.toInt h₁ h₂ = x.toInt32 := (rfl)

@[simp] theorem ISize64.ofIntLE_int8ToInt (x : Int8) :
    ISize64.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toISize64 := (rfl)

@[simp] theorem ISize64.ofIntLE_int16ToInt (x : Int16) :
    ISize64.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toISize64 := (rfl)

@[simp] theorem ISize64.ofIntLE_int32ToInt (x : Int32) :
    ISize64.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toISize64 := (rfl)

@[simp] theorem ISize64.ofIntLE_iSizeToInt (x : ISize) :
    ISize64.ofIntLE x.toInt x.isize64MinValue_le_toInt x.toInt_le_isize64MaxValue = x.toISize64 := (rfl)

theorem ISize.ofIntLE_isize64ToInt (x : ISize64) {h₁ h₂} : ISize.ofIntLE x.toInt h₁ h₂ = x.toISize := (rfl)

@[simp] theorem ISize64.ofInt_toInt (x : ISize64) : ISize64.ofInt x.toInt = x := ISize64.toBitVec.inj (by simp)

@[simp] theorem Int8.ofInt_isize64ToInt (x : ISize64) : Int8.ofInt x.toInt = x.toInt8 := (rfl)

@[simp] theorem Int16.ofInt_isize64ToInt (x : ISize64) : Int16.ofInt x.toInt = x.toInt16 := (rfl)

@[simp] theorem Int32.ofInt_isize64ToInt (x : ISize64) : Int32.ofInt x.toInt = x.toInt32 := (rfl)

@[simp] theorem ISize64.ofInt_int8ToInt (x : Int8) : ISize64.ofInt x.toInt = x.toISize64 := (rfl)

@[simp] theorem ISize64.ofInt_int16ToInt (x : Int16) : ISize64.ofInt x.toInt = x.toISize64 := (rfl)

@[simp] theorem ISize64.ofInt_int32ToInt (x : Int32) : ISize64.ofInt x.toInt = x.toISize64 := (rfl)

@[simp] theorem ISize64.ofInt_iSizeToInt (x : ISize) : ISize64.ofInt x.toInt = x.toISize64 := (rfl)

@[simp] theorem ISize.ofInt_isize64ToInt (x : ISize64) : ISize.ofInt x.toInt = x.toISize := (rfl)

@[simp] theorem ISize64.toInt_ofIntLE {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂).toInt = x := by
  rw [ofIntLE, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]

theorem ISize64.ofIntLE_eq_ofIntTruncate {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂) = ofIntTruncate x := by
  rw [ofIntTruncate, dif_pos h₁, dif_pos h₂]

theorem ISize64.ofIntLE_eq_ofInt {n : Int} (h₁ h₂) : ISize64.ofIntLE n h₁ h₂ = ISize64.ofInt n := (rfl)

theorem ISize64.toInt_ofIntTruncate {x : Int} (h₁ : ISize64.minValue.toInt ≤ x)
    (h₂ : x ≤ ISize64.maxValue.toInt) : (ISize64.ofIntTruncate x).toInt = x := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toInt_ofIntLE]

@[simp] theorem ISize64.ofIntTruncate_toInt (x : ISize64) : ISize64.ofIntTruncate x.toInt = x :=
  ISize64.toInt.inj (toInt_ofIntTruncate x.minValue_le_toInt x.toInt_le)

@[simp] theorem ISize64.ofIntTruncate_int8ToInt (x : Int8) : ISize64.ofIntTruncate x.toInt = x.toISize64 :=
  ISize64.toInt.inj (by
    rw [toInt_ofIntTruncate, Int8.toInt_toISize64]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))

@[simp] theorem ISize64.ofIntTruncate_int16ToInt (x : Int16) : ISize64.ofIntTruncate x.toInt = x.toISize64 :=
  ISize64.toInt.inj (by
    rw [toInt_ofIntTruncate, Int16.toInt_toISize64]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))

@[simp] theorem ISize64.ofIntTruncate_int32ToInt (x : Int32) : ISize64.ofIntTruncate x.toInt = x.toISize64 :=
  ISize64.toInt.inj (by
    rw [toInt_ofIntTruncate, Int32.toInt_toISize64]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))

@[simp] theorem ISize64.ofIntTruncate_iSizeToInt (x : ISize) : ISize64.ofIntTruncate x.toInt = x.toISize64 :=
  ISize64.toInt.inj (by
    rw [toInt_ofIntTruncate, ISize.toInt_toISize64]
    · exact x.isize64MinValue_le_toInt
    · exact x.toInt_le_isize64MaxValue)

theorem ISize64.le_iff_toInt_le {x y : ISize64} : x ≤ y ↔ x.toInt ≤ y.toInt := BitVec.sle_iff_toInt_le

theorem ISize64.lt_iff_toInt_lt {x y : ISize64} : x < y ↔ x.toInt < y.toInt := BitVec.slt_iff_toInt_lt

theorem ISize64.cast_toNatClampNeg (x : ISize64) (hx : 0 ≤ x) : x.toNatClampNeg = x.toInt := by
  rw [toNatClampNeg, toInt, Int.toNat_of_nonneg (by simpa using le_iff_toInt_le.1 hx)]

theorem ISize64.ofNat_toNatClampNeg (x : ISize64) (hx : 0 ≤ x) : ISize64.ofNat x.toNatClampNeg = x :=
  ISize64.toInt.inj (by rw [ISize64.toInt_ofNat_of_lt x.toNatClampNeg_lt, cast_toNatClampNeg _ hx])

theorem ISize64.ofNat_int8ToNatClampNeg (x : Int8) (hx : 0 ≤ x) : ISize64.ofNat x.toNatClampNeg = x.toISize64 :=
  ISize64.toInt.inj (by rw [ISize64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int8.cast_toNatClampNeg _ hx, Int8.toInt_toISize64])

theorem ISize64.ofNat_int16ToNatClampNeg (x : Int16) (hx : 0 ≤ x) : ISize64.ofNat x.toNatClampNeg = x.toISize64 :=
  ISize64.toInt.inj (by rw [ISize64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int16.cast_toNatClampNeg _ hx, Int16.toInt_toISize64])

theorem ISize64.ofNat_int32ToNatClampNeg (x : Int32) (hx : 0 ≤ x) : ISize64.ofNat x.toNatClampNeg = x.toISize64 :=
  ISize64.toInt.inj (by rw [ISize64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int32.cast_toNatClampNeg _ hx, Int32.toInt_toISize64])

@[simp] theorem Int8.toInt8_toISize64 (n : Int8) : n.toISize64.toInt8 = n :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int8.toInt16_toISize64 (n : Int8) : n.toISize64.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int8.toInt32_toISize64 (n : Int8) : n.toISize64.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)

@[simp] theorem Int8.toISize64_toInt16 (n : Int8) : n.toInt16.toISize64 = n.toISize64 :=
  ISize64.toInt.inj (by simp)

@[simp] theorem Int8.toISize64_toInt32 (n : Int8) : n.toInt32.toISize64 = n.toISize64 :=
  ISize64.toInt.inj (by simp)

@[simp] theorem Int8.toISize64_toISize (n : Int8) : n.toISize.toISize64 = n.toISize64 :=
  ISize64.toInt.inj (by simp)

@[simp] theorem Int8.toISize_toISize64 (n : Int8) : n.toISize64.toISize = n.toISize :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int16.toInt8_toISize64 (n : Int16) : n.toISize64.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int16.toInt16_toISize64 (n : Int16) : n.toISize64.toInt16 = n :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int16.toInt32_toISize64 (n : Int16) : n.toISize64.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)

@[simp] theorem Int16.toISize64_toInt32 (n : Int16) : n.toInt32.toISize64 = n.toISize64 :=
  ISize64.toInt.inj (by simp)

@[simp] theorem Int16.toISize64_toISize (n : Int16) : n.toISize.toISize64 = n.toISize64 :=
  ISize64.toInt.inj (by simp)

@[simp] theorem Int16.toISize_toISize64 (n : Int16) : n.toISize64.toISize = n.toISize :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int32.toInt8_toISize64 (n : Int32) : n.toISize64.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int32.toInt16_toISize64 (n : Int32) : n.toISize64.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int32.toInt32_toISize64 (n : Int32) : n.toISize64.toInt32 = n :=
  Int32.toInt.inj (by simp)

@[simp] theorem Int32.toISize64_toISize (n : Int32) : n.toISize.toISize64 = n.toISize64 :=
  ISize64.toInt.inj (by simp)

@[simp] theorem Int32.toISize_toISize64 (n : Int32) : n.toISize64.toISize = n.toISize :=
  ISize.toInt.inj (by simp)

@[simp] theorem ISize64.toInt8_toInt16 (n : ISize64) : n.toInt16.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem ISize64.toInt8_toInt32 (n : ISize64) : n.toInt32.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem ISize64.toInt8_toISize (n : ISize64) : n.toISize.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem ISize64.toInt16_toInt32 (n : ISize64) : n.toInt32.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem ISize64.toInt16_toISize (n : ISize64) : n.toISize.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem ISize64.toInt32_toISize (n : ISize64) : n.toISize.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem ISize.toInt8_toISize64 (n : ISize) : n.toISize64.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem ISize.toInt16_toISize64 (n : ISize) : n.toISize64.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem ISize.toInt32_toISize64 (n : ISize) : n.toISize64.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)

@[simp] theorem ISize.toISize_toISize64 (n : ISize) : n.toISize64.toISize = n :=
  ISize.toInt.inj (by simp)

theorem USize64.toISize64_ofNatLT {n : Nat} (hn) : (USize64.ofNatLT n hn).toISize64 = ISize64.ofNat n :=
  ISize64.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat])

@[simp] theorem USize64.toISize64_ofNat' {n : Nat} : (USize64.ofNat n).toISize64 = ISize64.ofNat n := (rfl)

@[simp] theorem USize64.toISize64_ofNat {n : Nat} : toISize64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := (rfl)

@[simp] theorem USize64.toISize64_ofBitVec (b) : (USize64.ofBitVec b).toISize64 = ISize64.ofBitVec b := (rfl)

@[simp, int_toBitVec] theorem ISize64.toBitVec_ofBitVec (b) : (ISize64.ofBitVec b).toBitVec = b := (rfl)

theorem ISize64.toBitVec_ofIntTruncate {n : Int} (h₁ : ISize64.minValue.toInt ≤ n) (h₂ : n ≤ ISize64.maxValue.toInt) :
    (ISize64.ofIntTruncate n).toBitVec = BitVec.ofInt _ n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toBitVec_ofIntLE]

@[simp] theorem ISize64.toInt_ofBitVec (b) : (ISize64.ofBitVec b).toInt = b.toInt := (rfl)

@[simp] theorem ISize64.toNatClampNeg_ofIntLE {n : Int} (h₁ h₂) : (ISize64.ofIntLE n h₁ h₂).toNatClampNeg = n.toNat := by
  rw [ofIntLE, toNatClampNeg, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]

@[simp] theorem ISize64.toNatClampNeg_ofBitVec (b) : (ISize64.ofBitVec b).toNatClampNeg = b.toInt.toNat := (rfl)

theorem ISize64.toNatClampNeg_ofInt_of_le {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (ISize64.ofInt n).toNatClampNeg = n.toNat := by rw [toNatClampNeg, toInt_ofInt_of_le h₁ h₂]

theorem ISize64.toNatClampNeg_ofIntTruncate_of_lt {n : Int} (h₁ : n < 2 ^ 63) :
    (ISize64.ofIntTruncate n).toNatClampNeg = n.toNat := by
  rw [ofIntTruncate]
  split
  · rw [dif_pos (by rw [toInt_maxValue]; omega), toNatClampNeg_ofIntLE]
  next h =>
    rw [toNatClampNeg_minValue, eq_comm, Int.toNat_eq_zero]
    rw [toInt_minValue] at h
    omega

@[simp] theorem ISize64.toUSize64_ofBitVec (b) : (ISize64.ofBitVec b).toUSize64 = USize64.ofBitVec b := (rfl)

@[simp] theorem ISize64.toUSize64_ofNat' {n} : (ISize64.ofNat n).toUSize64 = USize64.ofNat n := (rfl)

@[simp] theorem ISize64.toUSize64_ofNat {n} : toUSize64 (OfNat.ofNat n) = OfNat.ofNat n := (rfl)

theorem ISize64.toInt8_ofIntLE {n} (h₁ h₂) : (ISize64.ofIntLE n h₁ h₂).toInt8 = Int8.ofInt n := Int8.toInt.inj (by simp)

@[simp] theorem ISize64.toInt8_ofBitVec (b) : (ISize64.ofBitVec b).toInt8 = Int8.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem ISize64.toInt8_ofNat' {n} : (ISize64.ofNat n).toInt8 = Int8.ofNat n :=
  Int8.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem ISize64.toInt8_ofInt {n} : (ISize64.ofInt n).toInt8 = Int8.ofInt n :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem ISize64.toInt8_ofNat {n} : toInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt8_ofNat'

theorem ISize64.toInt8_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (ISize64.ofIntTruncate n).toInt8 = Int8.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt8_ofIntLE]

theorem ISize64.toInt16_ofIntLE {n} (h₁ h₂) : (ISize64.ofIntLE n h₁ h₂).toInt16 = Int16.ofInt n := Int16.toInt.inj (by simp)

@[simp] theorem ISize64.toInt16_ofBitVec (b) : (ISize64.ofBitVec b).toInt16 = Int16.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem ISize64.toInt16_ofNat' {n} : (ISize64.ofNat n).toInt16 = Int16.ofNat n :=
  Int16.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem ISize64.toInt16_ofInt {n} : (ISize64.ofInt n).toInt16 = Int16.ofInt n :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem ISize64.toInt16_ofNat {n} : toInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt16_ofNat'

theorem ISize64.toInt16_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (ISize64.ofIntTruncate n).toInt16 = Int16.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt16_ofIntLE]

theorem ISize64.toInt32_ofIntLE {n} (h₁ h₂) : (ISize64.ofIntLE n h₁ h₂).toInt32 = Int32.ofInt n := Int32.toInt.inj (by simp)

@[simp] theorem ISize64.toInt32_ofBitVec (b) : (ISize64.ofBitVec b).toInt32 = Int32.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem ISize64.toInt32_ofNat' {n} : (ISize64.ofNat n).toInt32 = Int32.ofNat n :=
  Int32.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem ISize64.toInt32_ofInt {n} : (ISize64.ofInt n).toInt32 = Int32.ofInt n :=
  Int32.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem ISize64.toInt32_ofNat {n} : toInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt32_ofNat'

theorem ISize64.toInt32_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (ISize64.ofIntTruncate n).toInt32 = Int32.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt32_ofIntLE]

theorem ISize64.toISize_ofIntLE {n} (h₁ h₂) : (ISize64.ofIntLE n h₁ h₂).toISize = ISize.ofInt n :=
  ISize.toInt.inj (by simp [ISize.toInt_ofInt])

@[simp] theorem ISize64.toISize_ofBitVec (b) : (ISize64.ofBitVec b).toISize = ISize.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem ISize64.toISize_ofNat' {n} : (ISize64.ofNat n).toISize = ISize.ofNat n :=
  ISize.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem ISize64.toISize_ofInt {n} : (ISize64.ofInt n).toISize = ISize.ofInt n :=
 ISize.toInt.inj (by simpa [ISize.toInt_ofInt] using Int.bmod_bmod_of_dvd USize.size_dvd_uISize64Size)

@[simp] theorem ISize64.toISize_ofNat {n} : toISize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toISize_ofNat'

theorem ISize64.toISize_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (ISize64.ofIntTruncate n).toISize = ISize.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toISize_ofIntLE]

@[simp, int_toBitVec] theorem ISize64.toBitVec_minValue : minValue.toBitVec = BitVec.intMin _ := (rfl)

@[simp, int_toBitVec] theorem ISize64.toBitVec_maxValue : maxValue.toBitVec = BitVec.intMax _ := (rfl)

@[simp] theorem ISize64.toInt8_neg (x : ISize64) : (-x).toInt8 = -x.toInt8 := Int8.toBitVec.inj (by simp)

@[simp] theorem ISize64.toInt16_neg (x : ISize64) : (-x).toInt16 = -x.toInt16 := Int16.toBitVec.inj (by simp)

@[simp] theorem ISize64.toInt32_neg (x : ISize64) : (-x).toInt32 = -x.toInt32 := Int32.toBitVec.inj (by simp)

@[simp] theorem ISize64.toISize_neg (x : ISize64) : (-x).toISize = -x.toISize := ISize.toBitVec.inj (by simp)

@[simp] theorem Int8.toISize64_neg_of_ne {x : Int8} (hx : x ≠ -128) : (-x).toISize64 = -x.toISize64 :=
  ISize64.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int8.toBitVec.inj h)))

@[simp] theorem Int16.toISize64_neg_of_ne {x : Int16} (hx : x ≠ -32768) : (-x).toISize64 = -x.toISize64 :=
  ISize64.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int16.toBitVec.inj h)))

@[simp] theorem Int32.toISize64_neg_of_ne {x : Int32} (hx : x ≠ -2147483648) : (-x).toISize64 = -x.toISize64 :=
  ISize64.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _  (fun h => hx (Int32.toBitVec.inj h)))

@[simp] theorem ISize.toISize64_neg_of_ne {x : ISize} (hx : x ≠ minValue) : (-x).toISize64 = -x.toISize64 :=
  ISize64.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _
    (fun h => hx (ISize.toBitVec.inj (h.trans toBitVec_minValue.symm))))

theorem Int8.toISize64_ofIntLE {n : Int} (h₁ h₂) :
    (Int8.ofIntLE n h₁ h₂).toISize64 = ISize64.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  ISize64.toInt.inj (by simp)

@[simp] theorem Int8.toISize64_ofBitVec (b) : (Int8.ofBitVec b).toISize64 = ISize64.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int8.toISize64_ofInt {n : Int} (h₁ : Int8.minValue.toInt ≤ n) (h₂ : n ≤ Int8.maxValue.toInt) :
    (Int8.ofInt n).toISize64 = ISize64.ofInt n := by rw [← Int8.ofIntLE_eq_ofInt h₁ h₂, toISize64_ofIntLE, ISize64.ofIntLE_eq_ofInt]

@[simp] theorem Int8.toISize64_ofNat' {n : Nat} (h : n ≤ Int8.maxValue.toInt) :
    (Int8.ofNat n).toISize64 = ISize64.ofNat n := by
  rw [← ofInt_eq_ofNat, toISize64_ofInt (by simp [toInt_minValue]) h, ISize64.ofInt_eq_ofNat]

@[simp] theorem Int8.toISize64_ofNat {n : Nat} (h : n ≤ 127) :
    toISize64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int8.toISize64_ofNat' (by rw [toInt_maxValue]; omega)

theorem Int16.toISize64_ofIntLE {n : Int} (h₁ h₂) :
    (Int16.ofIntLE n h₁ h₂).toISize64 = ISize64.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  ISize64.toInt.inj (by simp)

@[simp] theorem Int16.toISize64_ofBitVec (b) : (Int16.ofBitVec b).toISize64 = ISize64.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int16.toISize64_ofInt {n : Int} (h₁ : Int16.minValue.toInt ≤ n) (h₂ : n ≤ Int16.maxValue.toInt) :
    (Int16.ofInt n).toISize64 = ISize64.ofInt n := by rw [← Int16.ofIntLE_eq_ofInt h₁ h₂, toISize64_ofIntLE, ISize64.ofIntLE_eq_ofInt]

@[simp] theorem Int16.toISize64_ofNat' {n : Nat} (h : n ≤ Int16.maxValue.toInt) :
    (Int16.ofNat n).toISize64 = ISize64.ofNat n := by
  rw [← ofInt_eq_ofNat, toISize64_ofInt (by simp [toInt_minValue]) h, ISize64.ofInt_eq_ofNat]

@[simp] theorem Int16.toISize64_ofNat {n : Nat} (h : n ≤ 32767) :
    toISize64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int16.toISize64_ofNat' (by rw [toInt_maxValue]; omega)

theorem Int32.toISize64_ofIntLE {n : Int} (h₁ h₂) :
    (Int32.ofIntLE n h₁ h₂).toISize64 = ISize64.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  ISize64.toInt.inj (by simp)

@[simp] theorem Int32.toISize64_ofBitVec (b) : (Int32.ofBitVec b).toISize64 = ISize64.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int32.toISize64_ofInt {n : Int} (h₁ : Int32.minValue.toInt ≤ n) (h₂ : n ≤ Int32.maxValue.toInt) :
    (Int32.ofInt n).toISize64 = ISize64.ofInt n := by rw [← Int32.ofIntLE_eq_ofInt h₁ h₂, toISize64_ofIntLE, ISize64.ofIntLE_eq_ofInt]

@[simp] theorem Int32.toISize64_ofNat' {n : Nat} (h : n ≤ Int32.maxValue.toInt) :
    (Int32.ofNat n).toISize64 = ISize64.ofNat n := by
  rw [← ofInt_eq_ofNat, toISize64_ofInt (by simp [toInt_minValue]) h, ISize64.ofInt_eq_ofNat]

@[simp] theorem Int32.toISize64_ofNat {n : Nat} (h : n ≤ 2147483647) :
    toISize64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int32.toISize64_ofNat' (by rw [toInt_maxValue]; omega)

theorem ISize.toISize64_ofIntLE {n : Int} (h₁ h₂) :
    (ISize.ofIntLE n h₁ h₂).toISize64 = ISize64.ofIntLE n (Int.le_trans minValue.isize64MinValue_le_toInt h₁)
      (Int.le_trans h₂ maxValue.toInt_le_isize64MaxValue) :=
  ISize64.toInt.inj (by simp)

@[simp] theorem ISize.toISize64_ofBitVec (b) : (ISize.ofBitVec b).toISize64 = ISize64.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem ISize.toISize64_ofInt {n : Int} (h₁ : ISize.minValue.toInt ≤ n) (h₂ : n ≤ ISize.maxValue.toInt) :
    (ISize.ofInt n).toISize64 = ISize64.ofInt n := by rw [← ISize.ofIntLE_eq_ofInt h₁ h₂, toISize64_ofIntLE, ISize64.ofIntLE_eq_ofInt]

@[simp] theorem ISize.toISize64_ofNat' {n : Nat} (h : n ≤ ISize.maxValue.toInt) :
    (ISize.ofNat n).toISize64 = ISize64.ofNat n := by
  rw [← ofInt_eq_ofNat, toISize64_ofInt _ h, ISize64.ofInt_eq_ofNat]
  refine Int.le_trans ?_ (Int.zero_le_ofNat _)
  cases System.Platform.numBits_eq <;> simp_all [ISize.toInt_minValue]

@[simp] theorem ISize.toISize64_ofNat {n : Nat} (h : n ≤ 2147483647) :
    toISize64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  ISize.toISize64_ofNat' (by rw [toInt_maxValue]; cases System.Platform.numBits_eq <;> simp_all <;> omega)

@[simp] theorem ISize64.ofIntLE_bitVecToInt (n : BitVec 64) :
    ISize64.ofIntLE n.toInt (by exact n.le_toInt) (by exact n.toInt_le) = ISize64.ofBitVec n :=
  ISize64.toBitVec.inj (by simp)

theorem ISize64.ofBitVec_ofNatLT (n : Nat) (hn) : ISize64.ofBitVec (BitVec.ofNatLT n hn) = ISize64.ofNat n :=
  ISize64.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat hn])

@[simp] theorem ISize64.ofBitVec_ofNat (n : Nat) : ISize64.ofBitVec (BitVec.ofNat 64 n) = ISize64.ofNat n := (rfl)

@[simp] theorem ISize64.ofBitVec_ofInt (n : Int) : ISize64.ofBitVec (BitVec.ofInt 64 n) = ISize64.ofInt n := (rfl)

@[simp] theorem ISize64.ofNat_bitVecToNat (n : BitVec 64) : ISize64.ofNat n.toNat = ISize64.ofBitVec n :=
  ISize64.toBitVec.inj (by simp)

@[simp] theorem ISize64.ofInt_bitVecToInt (n : BitVec 64) : ISize64.ofInt n.toInt = ISize64.ofBitVec n :=
  ISize64.toBitVec.inj (by simp)

@[simp] theorem ISize64.ofIntTruncate_bitVecToInt (n : BitVec 64) : ISize64.ofIntTruncate n.toInt = ISize64.ofBitVec n :=
  ISize64.toBitVec.inj (by simp [toBitVec_ofIntTruncate (n.le_toInt) (n.toInt_le)])

@[simp] theorem ISize64.toInt_neg (n : ISize64) : (-n).toInt = (-n.toInt).bmod (2 ^ 64) := BitVec.toInt_neg

@[simp] theorem ISize64.toNatClampNeg_eq_zero_iff {n : ISize64} : n.toNatClampNeg = 0 ↔ n ≤ 0 := by
  rw [toNatClampNeg, Int.toNat_eq_zero, le_iff_toInt_le, toInt_zero]

@[simp] protected theorem Int32.not_le {n m : Int32} : ¬n ≤ m ↔ m < n := by simp [le_iff_toInt_le, lt_iff_toInt_lt]
@[simp] protected theorem ISize64.not_le {n m : ISize64} : ¬n ≤ m ↔ m < n := by simp [le_iff_toInt_le, lt_iff_toInt_lt]

@[simp] theorem ISize64.neg_nonpos_iff (n : ISize64) : -n ≤ 0 ↔ n = minValue ∨ 0 ≤ n := by
  rw [le_iff_toBitVec_sle, toBitVec_zero, toBitVec_neg, BitVec.neg_sle_zero (by decide)]
  simp [← toBitVec_inj, le_iff_toBitVec_sle, BitVec.intMin_eq_neg_two_pow]

@[simp] theorem Int32.toNatClampNeg_pos_iff (n : Int32) : 0 < n.toNatClampNeg ↔ 0 < n := by simp [Nat.pos_iff_ne_zero]
@[simp] theorem ISize64.toNatClampNeg_pos_iff (n : ISize64) : 0 < n.toNatClampNeg ↔ 0 < n := by simp [Nat.pos_iff_ne_zero]

@[simp] theorem ISize64.toInt_div (a b : ISize64) : (a / b).toInt = (a.toInt.tdiv b.toInt).bmod (2 ^ 64) := by
  rw [← toInt_toBitVec, ISize64.toBitVec_div, BitVec.toInt_sdiv, toInt_toBitVec, toInt_toBitVec]

theorem ISize64.toInt_div_of_ne_left (a b : ISize64) (h : a ≠ minValue) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, ISize64.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inl (by simpa [← toBitVec_inj] using h)

theorem ISize64.toInt_div_of_ne_right (a b : ISize64) (h : b ≠ -1) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, ISize64.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inr (by simpa [← toBitVec_inj] using h)

theorem Int8.toISize64_ne_minValue (a : Int8) : a.toISize64 ≠ ISize64.minValue :=
  have := a.le_toInt; by simp [← ISize64.toInt_inj]; omega

theorem Int16.toISize64_ne_minValue (a : Int16) : a.toISize64 ≠ ISize64.minValue :=
  have := a.le_toInt; by simp [← ISize64.toInt_inj]; omega

theorem Int32.toISize64_ne_minValue (a : Int32) : a.toISize64 ≠ ISize64.minValue :=
  have := a.le_toInt; by simp [← ISize64.toInt_inj]; omega

theorem ISize.toISize64_ne_minValue (a : ISize) (ha : a ≠ minValue) : a.toISize64 ≠ ISize64.minValue := by
  have := a.minValue_le_toInt
  have : -2 ^ 63 ≤ minValue.toInt := minValue.le_toInt
  simp [← ISize64.toInt_inj, ← ISize.toInt_inj] at *; omega

theorem Int8.toISize64_ne_neg_one (a : Int8) (ha : a ≠ -1) : a.toISize64 ≠ -1 :=
  ne_of_apply_ne ISize64.toInt8 (by simpa using ha)

theorem Int16.toISize64_ne_neg_one (a : Int16) (ha : a ≠ -1) : a.toISize64 ≠ -1 :=
  ne_of_apply_ne ISize64.toInt16 (by simpa using ha)

theorem Int32.toISize64_ne_neg_one (a : Int32) (ha : a ≠ -1) : a.toISize64 ≠ -1 :=
  ne_of_apply_ne ISize64.toInt32 (by simpa using ha)

theorem ISize.toISize64_ne_neg_one (a : ISize) (ha : a ≠ -1) : a.toISize64 ≠ -1 :=
  ne_of_apply_ne ISize64.toISize (by simpa using ha)

theorem Int8.toISize64_div_of_ne_left (a b : Int8) (ha : a ≠ minValue) : (a / b).toISize64 = a.toISize64 / b.toISize64 :=
  ISize64.toInt_inj.1 (by rw [toInt_toISize64, toInt_div_of_ne_left _ _ ha,
    ISize64.toInt_div_of_ne_left _ _ a.toISize64_ne_minValue, toInt_toISize64, toInt_toISize64])

theorem Int16.toISize64_div_of_ne_left (a b : Int16) (ha : a ≠ minValue) : (a / b).toISize64 = a.toISize64 / b.toISize64 :=
  ISize64.toInt_inj.1 (by rw [toInt_toISize64, toInt_div_of_ne_left _ _ ha,
    ISize64.toInt_div_of_ne_left _ _ a.toISize64_ne_minValue, toInt_toISize64, toInt_toISize64])

theorem Int32.toISize64_div_of_ne_left (a b : Int32) (ha : a ≠ minValue) : (a / b).toISize64 = a.toISize64 / b.toISize64 :=
  ISize64.toInt_inj.1 (by rw [toInt_toISize64, toInt_div_of_ne_left _ _ ha,
    ISize64.toInt_div_of_ne_left _ _ a.toISize64_ne_minValue, toInt_toISize64, toInt_toISize64])

theorem ISize.toISize64_div_of_ne_left (a b : ISize) (ha : a ≠ minValue) : (a / b).toISize64 = a.toISize64 / b.toISize64 :=
  ISize64.toInt_inj.1 (by rw [toInt_toISize64, toInt_div_of_ne_left _ _ ha,
    ISize64.toInt_div_of_ne_left _ _ (a.toISize64_ne_minValue ha), toInt_toISize64, toInt_toISize64])

theorem Int8.toISize64_div_of_ne_right (a b : Int8) (hb : b ≠ -1) : (a / b).toISize64 = a.toISize64 / b.toISize64 :=
  ISize64.toInt_inj.1 (by rw [toInt_toISize64, toInt_div_of_ne_right _ _ hb,
    ISize64.toInt_div_of_ne_right _ _ (b.toISize64_ne_neg_one hb), toInt_toISize64, toInt_toISize64])

theorem Int16.toISize64_div_of_ne_right (a b : Int16) (hb : b ≠ -1) : (a / b).toISize64 = a.toISize64 / b.toISize64 :=
  ISize64.toInt_inj.1 (by rw [toInt_toISize64, toInt_div_of_ne_right _ _ hb,
    ISize64.toInt_div_of_ne_right _ _ (b.toISize64_ne_neg_one hb), toInt_toISize64, toInt_toISize64])

theorem Int32.toISize64_div_of_ne_right (a b : Int32) (hb : b ≠ -1) : (a / b).toISize64 = a.toISize64 / b.toISize64 :=
  ISize64.toInt_inj.1 (by rw [toInt_toISize64, toInt_div_of_ne_right _ _ hb,
    ISize64.toInt_div_of_ne_right _ _ (b.toISize64_ne_neg_one hb), toInt_toISize64, toInt_toISize64])

theorem ISize.toISize64_div_of_ne_right (a b : ISize) (hb : b ≠ -1) : (a / b).toISize64 = a.toISize64 / b.toISize64 :=
  ISize64.toInt_inj.1 (by rw [toInt_toISize64, toInt_div_of_ne_right _ _ hb,
    ISize64.toInt_div_of_ne_right _ _ (b.toISize64_ne_neg_one hb), toInt_toISize64, toInt_toISize64])

@[simp] theorem ISize64.minValue_div_neg_one : minValue / -1 = minValue := (rfl)

@[simp] theorem ISize64.toInt_add (a b : ISize64) : (a + b).toInt = (a.toInt + b.toInt).bmod (2 ^ 64) := by
  rw [← toInt_toBitVec, ISize64.toBitVec_add, BitVec.toInt_add, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem ISize64.toInt8_add (a b : ISize64) : (a + b).toInt8 = a.toInt8 + b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem ISize64.toInt16_add (a b : ISize64) : (a + b).toInt16 = a.toInt16 + b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem ISize64.toInt32_add (a b : ISize64) : (a + b).toInt32 = a.toInt32 + b.toInt32 :=
  Int32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem ISize64.toISize_add (a b : ISize64) : (a + b).toISize = a.toISize + b.toISize :=
  ISize.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem ISize64.toInt_mul (a b : ISize64) : (a * b).toInt = (a.toInt * b.toInt).bmod (2 ^ 64) := by
  rw [← toInt_toBitVec, ISize64.toBitVec_mul, BitVec.toInt_mul, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem ISize64.toInt8_mul (a b : ISize64) : (a * b).toInt8 = a.toInt8 * b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

@[simp] theorem ISize64.toInt16_mul (a b : ISize64) : (a * b).toInt16 = a.toInt16 * b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

@[simp] theorem ISize64.toInt32_mul (a b : ISize64) : (a * b).toInt32 = a.toInt32 * b.toInt32 :=
  Int32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

@[simp] theorem ISize64.toISize_mul (a b : ISize64) : (a * b).toISize = a.toISize * b.toISize :=
  ISize.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

protected theorem ISize64.sub_eq_add_neg (a b : ISize64) : a - b = a + -b := ISize64.toBitVec.inj (by simp [BitVec.sub_eq_add_neg])

@[simp] theorem ISize64.toInt_sub (a b : ISize64) : (a - b).toInt = (a.toInt - b.toInt).bmod (2 ^ 64) := by
  simp [ISize64.sub_eq_add_neg, Int.sub_eq_add_neg]

@[simp] theorem ISize64.toInt8_sub (a b : ISize64) : (a - b).toInt8 = a.toInt8 - b.toInt8 := by
  simp [ISize64.sub_eq_add_neg, Int8.sub_eq_add_neg]

@[simp] theorem ISize64.toInt16_sub (a b : ISize64) : (a - b).toInt16 = a.toInt16 - b.toInt16 := by
  simp [ISize64.sub_eq_add_neg, Int16.sub_eq_add_neg]

@[simp] theorem ISize64.toInt32_sub (a b : ISize64) : (a - b).toInt32 = a.toInt32 - b.toInt32 := by
  simp [ISize64.sub_eq_add_neg, Int32.sub_eq_add_neg]

@[simp] theorem ISize64.toISize_sub (a b : ISize64) : (a - b).toISize = a.toISize - b.toISize := by
  simp [ISize64.sub_eq_add_neg, ISize.sub_eq_add_neg]

@[simp] theorem Int8.toISize64_lt {a b : Int8} : a.toISize64 < b.toISize64 ↔ a < b := by
  simp [lt_iff_toInt_lt, ISize64.lt_iff_toInt_lt]

@[simp] theorem Int16.toISize64_lt {a b : Int16} : a.toISize64 < b.toISize64 ↔ a < b := by
  simp [lt_iff_toInt_lt, ISize64.lt_iff_toInt_lt]

@[simp] theorem Int32.toISize64_lt {a b : Int32} : a.toISize64 < b.toISize64 ↔ a < b := by
  simp [lt_iff_toInt_lt, ISize64.lt_iff_toInt_lt]

@[simp] theorem ISize.toISize64_lt {a b : ISize} : a.toISize64 < b.toISize64 ↔ a < b := by
  simp [lt_iff_toInt_lt, ISize64.lt_iff_toInt_lt]

@[simp] theorem Int8.toISize64_le {a b : Int8} : a.toISize64 ≤ b.toISize64 ↔ a ≤ b := by
  simp [le_iff_toInt_le, ISize64.le_iff_toInt_le]

@[simp] theorem Int16.toISize64_le {a b : Int16} : a.toISize64 ≤ b.toISize64 ↔ a ≤ b := by
  simp [le_iff_toInt_le, ISize64.le_iff_toInt_le]

@[simp] theorem Int32.toISize64_le {a b : Int32} : a.toISize64 ≤ b.toISize64 ↔ a ≤ b := by
  simp [le_iff_toInt_le, ISize64.le_iff_toInt_le]

@[simp] theorem ISize.toISize64_le {a b : ISize} : a.toISize64 ≤ b.toISize64 ↔ a ≤ b := by
  simp [le_iff_toInt_le, ISize64.le_iff_toInt_le]

@[simp] theorem ISize64.ofBitVec_neg (a : BitVec 64) : ISize64.ofBitVec (-a) = -ISize64.ofBitVec a := (rfl)

@[simp] theorem ISize64.ofInt_neg (a : Int) : ISize64.ofInt (-a) = -ISize64.ofInt a := ISize64.toInt_inj.1 (by simp)

theorem ISize64.ofInt_eq_iff_bmod_eq_toInt (a : Int) (b : ISize64) : ISize64.ofInt a = b ↔ a.bmod (2 ^ 64) = b.toInt := by
  simp [← ISize64.toInt_inj]

@[simp] theorem ISize64.ofBitVec_add (a b : BitVec 64) : ISize64.ofBitVec (a + b) = ISize64.ofBitVec a + ISize64.ofBitVec b := (rfl)

@[simp] theorem ISize64.ofInt_add (a b : Int) : ISize64.ofInt (a + b) = ISize64.ofInt a + ISize64.ofInt b := by
  simp [ISize64.ofInt_eq_iff_bmod_eq_toInt]

@[simp] theorem ISize64.ofNat_add (a b : Nat) : ISize64.ofNat (a + b) = ISize64.ofNat a + ISize64.ofNat b := by
  simp [← ISize64.ofInt_eq_ofNat]

theorem ISize64.ofIntLE_add {a b : Int} {hab₁ hab₂} : ISize64.ofIntLE (a + b) hab₁ hab₂ = ISize64.ofInt a + ISize64.ofInt b := by
  simp [ISize64.ofIntLE_eq_ofInt]

@[simp] theorem ISize64.ofBitVec_sub (a b : BitVec 64) : ISize64.ofBitVec (a - b) = ISize64.ofBitVec a - ISize64.ofBitVec b := (rfl)

@[simp] theorem ISize64.ofInt_sub (a b : Int) : ISize64.ofInt (a - b) = ISize64.ofInt a - ISize64.ofInt b := by
  simp [ISize64.ofInt_eq_iff_bmod_eq_toInt]

@[simp] theorem ISize64.ofNat_sub (a b : Nat) (hab : b ≤ a) : ISize64.ofNat (a - b) = ISize64.ofNat a - ISize64.ofNat b := by
  simp [← ISize64.ofInt_eq_ofNat, Int.ofNat_sub hab]

theorem ISize64.ofIntLE_sub {a b : Int} {hab₁ hab₂} : ISize64.ofIntLE (a - b) hab₁ hab₂ = ISize64.ofInt a - ISize64.ofInt b := by
  simp [ISize64.ofIntLE_eq_ofInt]

@[simp] theorem ISize64.ofBitVec_mul (a b : BitVec 64) : ISize64.ofBitVec (a * b) = ISize64.ofBitVec a * ISize64.ofBitVec b := (rfl)

@[simp] theorem ISize64.ofInt_mul (a b : Int) : ISize64.ofInt (a * b) = ISize64.ofInt a * ISize64.ofInt b := by
  simp [ISize64.ofInt_eq_iff_bmod_eq_toInt]

@[simp] theorem ISize64.ofNat_mul (a b : Nat) : ISize64.ofNat (a * b) = ISize64.ofNat a * ISize64.ofNat b := by
  simp [← ISize64.ofInt_eq_ofNat]

theorem ISize64.ofIntLE_mul {a b : Int} {hab₁ hab₂} : ISize64.ofIntLE (a * b) hab₁ hab₂ = ISize64.ofInt a * ISize64.ofInt b := by
  simp [ISize64.ofIntLE_eq_ofInt]

theorem ISize64.toInt_minValue_lt_zero : minValue.toInt < 0 := by decide

theorem ISize64.toInt_maxValue_add_one : maxValue.toInt + 1 = 2 ^ 63 := (rfl)

@[simp] theorem ISize64.ofBitVec_sdiv (a b : BitVec 64) : ISize64.ofBitVec (a.sdiv b) = ISize64.ofBitVec a / ISize64.ofBitVec b := (rfl)

theorem ISize64.ofInt_tdiv {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : ISize64.ofInt (a.tdiv b) = ISize64.ofInt a / ISize64.ofInt b := by
  rw [ISize64.ofInt_eq_iff_bmod_eq_toInt, toInt_div, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂

theorem ISize64.ofInt_eq_ofIntLE_div {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize64.ofInt (a.tdiv b) = ISize64.ofIntLE a ha₁ ha₂ / ISize64.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tdiv ha₁ ha₂ hb₁ hb₂]

theorem ISize64.ofNat_div {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ISize64.ofNat (a / b) = ISize64.ofNat a / ISize64.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tdiv,
    ofInt_tdiv (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)

@[simp] theorem ISize64.ofBitVec_srem (a b : BitVec 64) : ISize64.ofBitVec (a.srem b) = ISize64.ofBitVec a % ISize64.ofBitVec b := (rfl)

@[simp] theorem ISize64.toInt_bmod_size (a : ISize64) : a.toInt.bmod size = a.toInt := BitVec.toInt_bmod_cancel _

theorem ISize64.ofIntLE_le_iff_le {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize64.ofIntLE a ha₁ ha₂ ≤ ISize64.ofIntLE b hb₁ hb₂ ↔ a ≤ b := by simp [le_iff_toInt_le]

theorem ISize64.ofInt_le_iff_le {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : ISize64.ofInt a ≤ ISize64.ofInt b ↔ a ≤ b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_le_iff_le]

theorem ISize64.ofNat_le_iff_le {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ISize64.ofNat a ≤ ISize64.ofNat b ↔ a ≤ b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_le_iff_le (by simp) _ (by simp), Int.ofNat_le]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)

theorem ISize64.ofBitVec_le_iff_sle (a b : BitVec 64) : ISize64.ofBitVec a ≤ ISize64.ofBitVec b ↔ a.sle b := Iff.rfl

theorem ISize64.ofIntLE_lt_iff_lt {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize64.ofIntLE a ha₁ ha₂ < ISize64.ofIntLE b hb₁ hb₂ ↔ a < b := by simp [lt_iff_toInt_lt]

theorem ISize64.ofInt_lt_iff_lt {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : ISize64.ofInt a < ISize64.ofInt b ↔ a < b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_lt_iff_lt]

theorem ISize64.ofNat_lt_iff_lt {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ISize64.ofNat a < ISize64.ofNat b ↔ a < b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_lt_iff_lt (by simp) _ (by simp), Int.ofNat_lt]
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 ha)

theorem ISize64.ofBitVec_lt_iff_slt (a b : BitVec 64) : ISize64.ofBitVec a < ISize64.ofBitVec b ↔ a.slt b := Iff.rfl

theorem ISize64.toNatClampNeg_one : (1 : ISize64).toNatClampNeg = 1 := (rfl)

theorem ISize64.toInt_one : (1 : ISize64).toInt = 1 := (rfl)

theorem ISize64.zero_lt_one : (0 : ISize64) < 1 := by simp

theorem ISize64.zero_ne_one : (0 : ISize64) ≠ 1 := by simp

protected theorem ISize64.add_assoc (a b c : ISize64) : a + b + c = a + (b + c) :=
  ISize64.toBitVec_inj.1 (BitVec.add_assoc _ _ _)

instance : Std.Associative (α := ISize64) (· + ·) := ⟨ISize64.add_assoc⟩

protected theorem ISize64.add_comm (a b : ISize64) : a + b = b + a := ISize64.toBitVec_inj.1 (BitVec.add_comm _ _)

instance : Std.Commutative (α := ISize64) (· + ·) := ⟨ISize64.add_comm⟩

@[simp] protected theorem ISize64.add_zero (a : ISize64) : a + 0 = a := ISize64.toBitVec_inj.1 (BitVec.add_zero _)

@[simp] protected theorem ISize64.zero_add (a : ISize64) : 0 + a = a := ISize64.toBitVec_inj.1 (BitVec.zero_add _)

instance : Std.LawfulIdentity (α := ISize64) (· + ·) 0 where
  left_id := ISize64.zero_add
  right_id := ISize64.add_zero

@[simp] protected theorem ISize64.sub_zero (a : ISize64) : a - 0 = a := ISize64.toBitVec_inj.1 (BitVec.sub_zero _)

@[simp] protected theorem ISize64.zero_sub (a : ISize64) : 0 - a = -a := ISize64.toBitVec_inj.1 (BitVec.zero_sub _)

@[simp] protected theorem ISize64.sub_self (a : ISize64) : a - a = 0 := ISize64.toBitVec_inj.1 (BitVec.sub_self _)

protected theorem ISize64.add_left_neg (a : ISize64) : -a + a = 0 := ISize64.toBitVec_inj.1 (BitVec.add_left_neg _)

protected theorem ISize64.add_right_neg (a : ISize64) : a + -a = 0 := ISize64.toBitVec_inj.1 (BitVec.add_right_neg _)

@[simp] protected theorem ISize64.sub_add_cancel (a b : ISize64) : a - b + b = a :=
  ISize64.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)

protected theorem ISize64.eq_sub_iff_add_eq {a b c : ISize64} : a = c - b ↔ a + b = c := by
  simpa [← ISize64.toBitVec_inj] using BitVec.eq_sub_iff_add_eq

protected theorem ISize64.sub_eq_iff_eq_add {a b c : ISize64} : a - b = c ↔ a = c + b := by
  simpa [← ISize64.toBitVec_inj] using BitVec.sub_eq_iff_eq_add

@[simp] protected theorem ISize64.neg_neg {a : ISize64} : - -a = a := ISize64.toBitVec_inj.1 BitVec.neg_neg

@[simp] protected theorem Int32.neg_inj {a b : Int32} : -a = -b ↔ a = b := by simp [← Int32.toBitVec_inj]
@[simp] protected theorem ISize64.neg_inj {a b : ISize64} : -a = -b ↔ a = b := by simp [← ISize64.toBitVec_inj]

@[simp] protected theorem Int32.neg_ne_zero {a : Int32} : -a ≠ 0 ↔ a ≠ 0 := by simp [← Int32.toBitVec_inj]
@[simp] protected theorem ISize64.neg_ne_zero {a : ISize64} : -a ≠ 0 ↔ a ≠ 0 := by simp [← ISize64.toBitVec_inj]

protected theorem ISize64.neg_add {a b : ISize64} : - (a + b) = -a - b := ISize64.toBitVec_inj.1 BitVec.neg_add

@[simp] protected theorem ISize64.sub_neg {a b : ISize64} : a - -b = a + b := ISize64.toBitVec_inj.1 BitVec.sub_neg

@[simp] protected theorem ISize64.neg_sub {a b : ISize64} : -(a - b) = b - a := by
  rw [ISize64.sub_eq_add_neg, ISize64.neg_add, ISize64.sub_neg, ISize64.add_comm, ← ISize64.sub_eq_add_neg]

protected theorem ISize64.sub_sub (a b c : ISize64) : a - b - c = a - (b + c) := by
  simp [ISize64.sub_eq_add_neg, ISize64.add_assoc, ISize64.neg_add]

@[simp] protected theorem ISize64.add_left_inj {a b : ISize64} (c : ISize64) : (a + c = b + c) ↔ a = b := by
  simp [← ISize64.toBitVec_inj]

@[simp] protected theorem ISize64.add_right_inj {a b : ISize64} (c : ISize64) : (c + a = c + b) ↔ a = b := by
  simp [← ISize64.toBitVec_inj]

@[simp] protected theorem ISize64.sub_left_inj {a b : ISize64} (c : ISize64) : (a - c = b - c) ↔ a = b := by
  simp [← ISize64.toBitVec_inj]

@[simp] protected theorem ISize64.sub_right_inj {a b : ISize64} (c : ISize64) : (c - a = c - b) ↔ a = b := by
  simp [← ISize64.toBitVec_inj]

@[simp] theorem ISize64.add_eq_right {a b : ISize64} : a + b = b ↔ a = 0 := by
  simp [← ISize64.toBitVec_inj]

@[simp] theorem ISize64.add_eq_left {a b : ISize64} : a + b = a ↔ b = 0 := by
  simp [← ISize64.toBitVec_inj]

@[simp] theorem ISize64.right_eq_add {a b : ISize64} : b = a + b ↔ a = 0 := by
  simp [← ISize64.toBitVec_inj]

@[simp] theorem ISize64.left_eq_add {a b : ISize64} : a = a + b ↔ b = 0 := by
  simp [← ISize64.toBitVec_inj]

protected theorem ISize64.mul_comm (a b : ISize64) : a * b = b * a := ISize64.toBitVec_inj.1 (BitVec.mul_comm _ _)

instance : Std.Commutative (α := ISize64) (· * ·) := ⟨ISize64.mul_comm⟩

protected theorem ISize64.mul_assoc (a b c : ISize64) : a * b * c = a * (b * c) := ISize64.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)

instance : Std.Associative (α := ISize64) (· * ·) := ⟨ISize64.mul_assoc⟩

@[simp] theorem ISize64.mul_one (a : ISize64) : a * 1 = a := ISize64.toBitVec_inj.1 (BitVec.mul_one _)

@[simp] theorem ISize64.one_mul (a : ISize64) : 1 * a = a := ISize64.toBitVec_inj.1 (BitVec.one_mul _)

instance : Std.LawfulCommIdentity (α := ISize64) (· * ·) 1 where
  right_id := ISize64.mul_one

@[simp] theorem ISize64.mul_zero {a : ISize64} : a * 0 = 0 := ISize64.toBitVec_inj.1 BitVec.mul_zero

@[simp] theorem ISize64.zero_mul {a : ISize64} : 0 * a = 0 := ISize64.toBitVec_inj.1 BitVec.zero_mul

@[simp] protected theorem ISize64.pow_zero (x : ISize64) : x ^ 0 = 1 := (rfl)

protected theorem ISize64.pow_succ (x : ISize64) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)

protected theorem ISize64.mul_add {a b c : ISize64} : a * (b + c) = a * b + a * c :=
    ISize64.toBitVec_inj.1 BitVec.mul_add

protected theorem ISize64.add_mul {a b c : ISize64} : (a + b) * c = a * c + b * c := by
  rw [ISize64.mul_comm, ISize64.mul_add, ISize64.mul_comm a c, ISize64.mul_comm c b]

protected theorem ISize64.mul_succ {a b : ISize64} : a * (b + 1) = a * b + a := by simp [ISize64.mul_add]

protected theorem ISize64.succ_mul {a b : ISize64} : (a + 1) * b = a * b + b := by simp [ISize64.add_mul]

protected theorem ISize64.two_mul {a : ISize64} : 2 * a = a + a := ISize64.toBitVec_inj.1 BitVec.two_mul

protected theorem ISize64.mul_two {a : ISize64} : a * 2 = a + a := ISize64.toBitVec_inj.1 BitVec.mul_two

protected theorem ISize64.neg_mul (a b : ISize64) : -a * b = -(a * b) := ISize64.toBitVec_inj.1 (BitVec.neg_mul _ _)

protected theorem ISize64.mul_neg (a b : ISize64) : a * -b = -(a * b) := ISize64.toBitVec_inj.1 (BitVec.mul_neg _ _)

protected theorem ISize64.neg_mul_neg (a b : ISize64) : -a * -b = a * b := ISize64.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)

protected theorem ISize64.neg_mul_comm (a b : ISize64) : -a * b = a * -b := ISize64.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)

protected theorem ISize64.mul_sub {a b c : ISize64} : a * (b - c) = a * b - a * c := ISize64.toBitVec_inj.1 BitVec.mul_sub

protected theorem ISize64.sub_mul {a b c : ISize64} : (a - b) * c = a * c - b * c := by
  rw [ISize64.mul_comm, ISize64.mul_sub, ISize64.mul_comm, ISize64.mul_comm c]

theorem ISize64.neg_add_mul_eq_mul_not {a b : ISize64} : -(a + a * b) = a * ~~~b :=
  ISize64.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not

theorem ISize64.neg_mul_not_eq_add_mul {a b : ISize64} : -(a * ~~~b) = a + a * b :=
  ISize64.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul

protected theorem ISize64.le_of_lt {a b : ISize64} : a < b → a ≤ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le] using Int.le_of_lt

protected theorem ISize64.lt_of_le_of_ne {a b : ISize64} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← ISize64.toInt_inj] using (Int.lt_iff_le_and_ne.2 ⟨·, ·⟩)

protected theorem ISize64.lt_iff_le_and_ne {a b : ISize64} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← ISize64.toInt_inj] using Int.lt_iff_le_and_ne

@[simp] protected theorem Int32.lt_irrefl {a : Int32} : ¬a < a := by simp [lt_iff_toInt_lt]
@[simp] protected theorem ISize64.lt_irrefl {a : ISize64} : ¬a < a := by simp [lt_iff_toInt_lt]

protected theorem ISize64.lt_of_le_of_lt {a b c : ISize64} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_le_of_lt

protected theorem ISize64.lt_of_lt_of_le {a b c : ISize64} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_lt_of_le

@[simp] theorem ISize64.minValue_le (a : ISize64) : minValue ≤ a := by simpa [le_iff_toInt_le] using a.minValue_le_toInt

@[simp] theorem ISize64.le_maxValue (a : ISize64) : a ≤ maxValue := by simpa [le_iff_toInt_le] using a.toInt_le

@[simp] theorem ISize64.not_lt_minValue {a : ISize64} : ¬a < minValue :=
  fun h => ISize64.lt_irrefl (ISize64.lt_of_le_of_lt a.minValue_le h)

@[simp] theorem ISize64.not_maxValue_lt {a : ISize64} : ¬maxValue < a :=
  fun h => ISize64.lt_irrefl (ISize64.lt_of_lt_of_le h a.le_maxValue)

@[simp] protected theorem Int32.le_refl (a : Int32) : a ≤ a := by simp [Int32.le_iff_toInt_le]
@[simp] protected theorem ISize64.le_refl (a : ISize64) : a ≤ a := by simp [ISize64.le_iff_toInt_le]

protected theorem ISize64.le_rfl {a : ISize64} : a ≤ a := ISize64.le_refl _

protected theorem ISize64.le_antisymm_iff {a b : ISize64} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨by rintro rfl; simp, by simpa [← ISize64.toInt_inj, le_iff_toInt_le] using Int.le_antisymm⟩

protected theorem ISize64.le_antisymm {a b : ISize64} : a ≤ b → b ≤ a → a = b := by simpa using ISize64.le_antisymm_iff.2

@[simp] theorem ISize64.le_minValue_iff {a : ISize64} : a ≤ minValue ↔ a = minValue :=
  ⟨fun h => ISize64.le_antisymm h a.minValue_le, by rintro rfl; simp⟩

@[simp] theorem ISize64.maxValue_le_iff {a : ISize64} : maxValue ≤ a ↔ a = maxValue :=
  ⟨fun h => ISize64.le_antisymm a.le_maxValue h, by rintro rfl; simp⟩

@[simp] protected theorem ISize64.zero_div {a : ISize64} : 0 / a = 0 := ISize64.toBitVec_inj.1 BitVec.zero_sdiv

@[simp] protected theorem ISize64.div_zero {a : ISize64} : a / 0 = 0 := ISize64.toBitVec_inj.1 BitVec.sdiv_zero

@[simp] protected theorem ISize64.div_one {a : ISize64} : a / 1 = a := ISize64.toBitVec_inj.1 BitVec.sdiv_one

protected theorem ISize64.div_self {a : ISize64} : a / a = if a = 0 then 0 else 1 := by
  simp [← ISize64.toBitVec_inj, apply_ite]

@[simp] protected theorem ISize64.mod_zero {a : ISize64} : a % 0 = a := ISize64.toBitVec_inj.1 BitVec.srem_zero

@[simp] protected theorem ISize64.zero_mod {a : ISize64} : 0 % a = 0 := ISize64.toBitVec_inj.1 BitVec.zero_srem

@[simp] protected theorem ISize64.mod_one {a : ISize64} : a % 1 = 0 := ISize64.toBitVec_inj.1 BitVec.srem_one

@[simp] protected theorem ISize64.mod_self {a : ISize64} : a % a = 0 := ISize64.toBitVec_inj.1 BitVec.srem_self

@[simp] protected theorem ISize64.not_lt {a b : ISize64} : ¬ a < b ↔ b ≤ a := by
  simp [lt_iff_toBitVec_slt, le_iff_toBitVec_sle, BitVec.sle_eq_not_slt]

protected theorem ISize64.le_trans {a b c : ISize64} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [le_iff_toInt_le] using Int.le_trans

protected theorem ISize64.lt_trans {a b c : ISize64} : a < b → b < c → a < c := by
  simpa [lt_iff_toInt_lt] using Int.lt_trans

protected theorem ISize64.le_total (a b : ISize64) : a ≤ b ∨ b ≤ a := by
  simpa [le_iff_toInt_le] using Int.le_total _ _

protected theorem ISize64.lt_asymm {a b : ISize64} : a < b → ¬b < a :=
  fun hab hba => ISize64.lt_irrefl (ISize64.lt_trans hab hba)

instance ISize64.instIsLinearOrder : IsLinearOrder ISize64 := by
  apply IsLinearOrder.of_le
  case le_antisymm => constructor; apply ISize64.le_antisymm
  case le_total => constructor; apply ISize64.le_total
  case le_trans => constructor; apply ISize64.le_trans

instance : LawfulOrderLT ISize64 where
  lt_iff := by
    simp [← ISize64.not_le, Decidable.imp_iff_not_or, Std.Total.total]

protected theorem ISize64.add_neg_eq_sub {a b : ISize64} : a + -b = a - b := ISize64.toBitVec_inj.1 BitVec.add_neg_eq_sub

theorem ISize64.neg_eq_neg_one_mul (a : ISize64) : -a = -1 * a := ISize64.toInt_inj.1 (by simp)

@[simp] protected theorem ISize64.add_sub_cancel (a b : ISize64) : a + b - b = a := ISize64.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)

protected theorem ISize64.lt_or_lt_of_ne {a b : ISize64} : a ≠ b → a < b ∨ b < a := by
  simp [lt_iff_toInt_lt, ← ISize64.toInt_inj]; omega

protected theorem ISize64.lt_or_le (a b : ISize64) : a < b ∨ b ≤ a := by
  simp [lt_iff_toInt_lt, le_iff_toInt_le]; omega

protected theorem ISize64.le_or_lt (a b : ISize64) : a ≤ b ∨ b < a := (b.lt_or_le a).symm

protected theorem ISize64.le_of_eq {a b : ISize64} : a = b → a ≤ b := (· ▸ ISize64.le_rfl)

protected theorem ISize64.le_iff_lt_or_eq {a b : ISize64} : a ≤ b ↔ a < b ∨ a = b := by
  simp [← ISize64.toInt_inj, le_iff_toInt_le, lt_iff_toInt_lt]; omega

protected theorem ISize64.lt_or_eq_of_le {a b : ISize64} : a ≤ b → a < b ∨ a = b := ISize64.le_iff_lt_or_eq.mp

theorem ISize64.toInt_eq_toNatClampNeg {a : ISize64} (ha : 0 ≤ a) : a.toInt = a.toNatClampNeg := by
  simpa only [← toNat_toInt, Int.eq_natCast_toNat, le_iff_toInt_le] using ha

@[simp] theorem USize64.toISize64_add (a b : USize64) : (a + b).toISize64 = a.toISize64 + b.toISize64 := (rfl)

@[simp] theorem USize64.toISize64_neg (a : USize64) : (-a).toISize64 = -a.toISize64 := (rfl)

@[simp] theorem USize64.toISize64_sub (a b : USize64) : (a - b).toISize64 = a.toISize64 - b.toISize64 := (rfl)

@[simp] theorem USize64.toISize64_mul (a b : USize64) : (a * b).toISize64 = a.toISize64 * b.toISize64 := (rfl)

@[simp] theorem ISize64.toUSize64_add (a b : ISize64) : (a + b).toUSize64 = a.toUSize64 + b.toUSize64 := (rfl)

@[simp] theorem ISize64.toUSize64_neg (a : ISize64) : (-a).toUSize64 = -a.toUSize64 := (rfl)

@[simp] theorem ISize64.toUSize64_sub (a b : ISize64) : (a - b).toUSize64 = a.toUSize64 - b.toUSize64 := (rfl)

@[simp] theorem ISize64.toUSize64_mul (a b : ISize64) : (a * b).toUSize64 = a.toUSize64 * b.toUSize64 := (rfl)

theorem ISize64.toNatClampNeg_le {a b : ISize64} (hab : a ≤ b) : a.toNatClampNeg ≤ b.toNatClampNeg := by
  rw [← ISize64.toNat_toInt, ← ISize64.toNat_toInt]
  exact Int.toNat_le_toNat (ISize64.le_iff_toInt_le.1 hab)

theorem ISize64.toUSize64_le {a b : ISize64} (ha : 0 ≤ a) (hab : a ≤ b) : a.toUSize64 ≤ b.toUSize64 := by
  rw [USize64.le_iff_toNat_le, toNat_toUSize64_of_le ha, toNat_toUSize64_of_le (ISize64.le_trans ha hab)]
  exact ISize64.toNatClampNeg_le hab

theorem ISize64.zero_le_ofNat_of_lt {a : Nat} (ha : a < 2 ^ 63) : 0 ≤ ISize64.ofNat a := by
  rw [le_iff_toInt_le, toInt_ofNat_of_lt ha, ISize64.toInt_zero]
  exact Int.natCast_nonneg _

protected theorem ISize64.sub_nonneg_of_le {a b : ISize64} (hb : 0 ≤ b) (hab : b ≤ a) : 0 ≤ a - b := by
  rw [← ofNat_toNatClampNeg _ hb, ← ofNat_toNatClampNeg _ (ISize64.le_trans hb hab),
    ← ofNat_sub _ _ (ISize64.toNatClampNeg_le hab)]
  exact ISize64.zero_le_ofNat_of_lt (Nat.sub_lt_of_lt a.toNatClampNeg_lt)

theorem ISize64.toNatClampNeg_sub_of_le {a b : ISize64} (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b).toNatClampNeg = a.toNatClampNeg - b.toNatClampNeg := by
  rw [← toNat_toUSize64_of_le (ISize64.sub_nonneg_of_le hb hab), toUSize64_sub,
    USize64.toNat_sub_of_le _ _ (ISize64.toUSize64_le hb hab),
    ← toNat_toUSize64_of_le (ISize64.le_trans hb hab), ← toNat_toUSize64_of_le hb]

theorem ISize64.toInt_sub_of_le (a b : ISize64) (hb : 0 ≤ b) (h : b ≤ a) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [ISize64.toInt_eq_toNatClampNeg (ISize64.sub_nonneg_of_le hb h),
    ISize64.toInt_eq_toNatClampNeg (ISize64.le_trans hb h), ISize64.toInt_eq_toNatClampNeg hb,
    ISize64.toNatClampNeg_sub_of_le hb h, Int.ofNat_sub]
  exact ISize64.toNatClampNeg_le h

protected theorem ISize64.sub_le {a b : ISize64} (hb : 0 ≤ b) (hab : b ≤ a) : a - b ≤ a := by
  simp_all [le_iff_toInt_le, ISize64.toInt_sub_of_le _ _ hb hab]; omega

protected theorem ISize64.sub_lt {a b : ISize64} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  simp_all [lt_iff_toInt_lt, ISize64.toInt_sub_of_le _ _ (ISize64.le_of_lt hb) hab]; omega

protected theorem ISize64.ne_of_lt {a b : ISize64} : a < b → a ≠ b := by
  simpa [ISize64.lt_iff_toInt_lt, ← ISize64.toInt_inj] using Int.ne_of_lt

@[simp] theorem ISize64.toInt_mod (a b : ISize64) : (a % b).toInt = a.toInt.tmod b.toInt := by
  rw [← toInt_toBitVec, ISize64.toBitVec_mod, BitVec.toInt_srem, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem Int8.toISize64_mod (a b : Int8) : (a % b).toISize64 = a.toISize64 % b.toISize64 := ISize64.toInt.inj (by simp)

@[simp] theorem Int16.toISize64_mod (a b : Int16) : (a % b).toISize64 = a.toISize64 % b.toISize64 := ISize64.toInt.inj (by simp)

@[simp] theorem Int32.toISize64_mod (a b : Int32) : (a % b).toISize64 = a.toISize64 % b.toISize64 := ISize64.toInt.inj (by simp)

@[simp] theorem ISize.toISize64_mod (a b : ISize) : (a % b).toISize64 = a.toISize64 % b.toISize64 := ISize64.toInt.inj (by simp)

theorem ISize64.ofInt_tmod {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : ISize64.ofInt (a.tmod b) = ISize64.ofInt a % ISize64.ofInt b := by
  rw [ISize64.ofInt_eq_iff_bmod_eq_toInt, ← toInt_bmod_size, toInt_mod, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂

theorem ISize64.ofInt_eq_ofIntLE_mod {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize64.ofInt (a.tmod b) = ISize64.ofIntLE a ha₁ ha₂ % ISize64.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tmod ha₁ ha₂ hb₁ hb₂]

theorem ISize64.ofNat_mod {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ISize64.ofNat (a % b) = ISize64.ofNat a % ISize64.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tmod,
    ofInt_tmod (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/GrindInstances/ToInt.lean
-- Target: Hax/MissingLean/Init/GrindInstances/ToInt.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean.Grind

instance : ToInt USize64 (.uint 64) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := private USize64.toNat_inj.mp (Int.ofNat_inj.mp w)
  toInt_mem x := by simpa using Int.lt_toNat.mp (USize64.toNat_lt x)

@[simp] theorem toInt_uisize64 (x : USize64) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Zero USize64 (.uint 64) where
  toInt_zero := by simp

instance : ToInt.OfNat USize64 (.uint 64) where
  toInt_ofNat x := by simp; rfl

instance : ToInt.Add USize64 (.uint 64) where
  toInt_add x y := by simp

instance : ToInt.Mul USize64 (.uint 64) where
  toInt_mul x y := by simp

instance : ToInt.Mod USize64 (.uint 64) where
  toInt_mod x y := by simp

instance : ToInt.Div USize64 (.uint 64) where
  toInt_div x y := by simp

instance : ToInt.LE USize64 (.uint 64) where
  le_iff x y := by simpa using USize64.le_iff_toBitVec_le

instance : ToInt.LT USize64 (.uint 64) where
  lt_iff x y := by simpa using USize64.lt_iff_toBitVec_lt

instance : ToInt ISize64 (.sint 64) where
  toInt x := x.toInt
  toInt_inj x y w := private ISize64.toInt_inj.mp w
  toInt_mem x := by simp; exact ⟨ISize64.le_toInt x, ISize64.toInt_lt x⟩

@[simp] theorem toInt_isize64 (x : ISize64) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Zero ISize64 (.sint 64) where
  toInt_zero := by
    -- simp -- FIXME: succeeds, but generates a `(kernel) application type mismatch` error!
    change (0 : ISize64).toInt = _
    rw [ISize64.toInt_zero]

instance : ToInt.OfNat ISize64 (.sint 64) where
  toInt_ofNat x := by
    rw [toInt_isize64, ISize64.toInt_ofNat, ISize64.size, Int.bmod_eq_emod, IntInterval.wrap]
    simp
    split <;> omega

instance : ToInt.Add ISize64 (.sint 64) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.Mul ISize64 (.sint 64) where
  toInt_mul x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.LE ISize64 (.sint 64) where
  le_iff x y := by simpa using ISize64.le_iff_toInt_le

instance : ToInt.LT ISize64 (.sint 64) where
  lt_iff x y := by simpa using ISize64.lt_iff_toInt_lt

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/GrindInstances/Ring/SInt.lean
-- Target: Hax/MissingLean/Init/GrindInstances/Ring/SInt.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean Grind

@[expose, instance_reducible]
def ISize64.natCast : NatCast ISize64 where
  natCast x := ISize64.ofNat x

@[expose, instance_reducible]
def ISize64.intCast : IntCast ISize64 where
  intCast x := ISize64.ofInt x

attribute [local instance] ISize64.intCast in
theorem ISize64.intCast_neg (i : Int) : ((-i : Int) : ISize64) = -(i : ISize64) :=
  ISize64.ofInt_neg _

attribute [local instance] ISize64.intCast in
theorem ISize64.intCast_ofNat (x : Nat) : (OfNat.ofNat (α := Int) x : ISize64) = OfNat.ofNat x := ISize64.ofInt_eq_ofNat

attribute [local instance] ISize64.natCast ISize64.intCast in
instance : CommRing ISize64 where
  nsmul := ⟨(· * ·)⟩
  zsmul := ⟨(· * ·)⟩
  add_assoc := ISize64.add_assoc
  add_comm := ISize64.add_comm
  add_zero := ISize64.add_zero
  neg_add_cancel := ISize64.add_left_neg
  mul_assoc := ISize64.mul_assoc
  mul_comm := ISize64.mul_comm
  mul_one := ISize64.mul_one
  one_mul := ISize64.one_mul
  left_distrib _ _ _ := ISize64.mul_add
  right_distrib _ _ _ := ISize64.add_mul
  zero_mul _ := ISize64.zero_mul
  mul_zero _ := ISize64.mul_zero
  sub_eq_add_neg := ISize64.sub_eq_add_neg
  pow_zero := ISize64.pow_zero
  pow_succ := ISize64.pow_succ
  ofNat_succ x := ISize64.ofNat_add x 1
  intCast_neg := ISize64.ofInt_neg
  neg_zsmul i x := by
    change (-i : Int) * x = - (i * x)
    simp [ISize64.intCast_neg, ISize64.neg_mul]
  zsmul_natCast_eq_nsmul n a := congrArg (· * a) (ISize64.intCast_ofNat _)

instance : IsCharP ISize64 (2 ^ 64) := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = ISize64.ofInt x := rfl
    rw [this]
    simp [ISize64.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_bmod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, Int.ofNat_dvd_right])

example : ToInt.Add ISize64 (.sint 64) := inferInstance

example : ToInt.Neg ISize64 (.sint 64) := inferInstance

example : ToInt.Sub ISize64 (.sint 64) := inferInstance

instance : ToInt.Pow ISize64 (.sint 64) := ToInt.pow_of_semiring (by simp)

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/GrindInstances/Ring/UInt.lean
-- Target: Hax/MissingLean/Init/GrindInstances/Ring/UInt.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean Grind

set_option autoImplicit true

namespace USize64

/-- Variant of `USize64.ofNat_mod_size` replacing `2 ^ 64` with `18446744073709551616`.-/
theorem ofNat_mod_size' : ofNat (x % 18446744073709551616) = ofNat x := ofNat_mod_size

@[expose, instance_reducible]
def natCast : NatCast USize64 where
  natCast x := USize64.ofNat x

@[expose, instance_reducible]
def intCast : IntCast USize64 where
  intCast x := USize64.ofInt x

attribute [local instance] natCast intCast

theorem intCast_neg (x : Int) : ((-x : Int) : USize64) = - (x : USize64) := by
  simp only [Int.cast, IntCast.intCast, USize64.ofInt_neg]

theorem intCast_ofNat (x : Nat) : (OfNat.ofNat (α := Int) x : USize64) = OfNat.ofNat x := by
    -- A better proof would be welcome!
    simp only [Int.cast, IntCast.intCast]
    rw [USize64.ofInt]
    rw [Int.toNat_emod (Int.zero_le_ofNat x) (by decide)]
    erw [Int.toNat_natCast]
    rw [Int.toNat_pow_of_nonneg (by decide)]
    simp +instances only [ofNat, BitVec.ofNat, Fin.Internal.ofNat_eq_ofNat, Fin.ofNat, Int.reduceToNat, Nat.dvd_refl,
      Nat.mod_mod_of_dvd, instOfNat]
    try rfl

end USize64

attribute [local instance] USize64.natCast USize64.intCast in
instance : CommRing USize64 where
  nsmul := ⟨(· * ·)⟩
  zsmul := ⟨(· * ·)⟩
  add_assoc := USize64.add_assoc
  add_comm := USize64.add_comm
  add_zero := USize64.add_zero
  neg_add_cancel := USize64.add_left_neg
  mul_assoc := USize64.mul_assoc
  mul_comm := USize64.mul_comm
  mul_one := USize64.mul_one
  one_mul := USize64.one_mul
  left_distrib _ _ _ := USize64.mul_add
  right_distrib _ _ _ := USize64.add_mul
  zero_mul _ := USize64.zero_mul
  mul_zero _ := USize64.mul_zero
  sub_eq_add_neg := USize64.sub_eq_add_neg
  pow_zero := USize64.pow_zero
  pow_succ := USize64.pow_succ
  ofNat_succ x := USize64.ofNat_add x 1
  intCast_neg := USize64.ofInt_neg
  intCast_ofNat := USize64.intCast_ofNat
  neg_zsmul i a := by
    change (-i : Int) * a = - (i * a)
    simp [USize64.intCast_neg, USize64.neg_mul]
  zsmul_natCast_eq_nsmul n a := congrArg (· * a) (USize64.intCast_ofNat _)

instance : IsCharP USize64 18446744073709551616 := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = USize64.ofNat x := rfl
    simp [this, USize64.ofNat_eq_iff_mod_eq_toNat])

-- Verify we can derive the instances showing how `toInt` interacts with operations:
example : ToInt.Add USize64 (.uint 64) := inferInstance
example : ToInt.Neg USize64 (.uint 64) := inferInstance
example : ToInt.Sub USize64 (.uint 64) := inferInstance

instance : ToInt.Pow USize64 (.uint 64) := ToInt.pow_of_semiring (by simp)
