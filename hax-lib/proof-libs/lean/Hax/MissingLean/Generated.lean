-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Prelude.lean
-- Target: Hax/MissingLean/Init/Prelude.lean
-- ──────────────────────────────────────────────────────────────────────

abbrev UInt128.size : Nat := 340282366920938463463374607431768211456

structure UInt128 where
  /--
  Creates a `UInt128` from a `BitVec 128`. This function is overridden with a native implementation.
  -/
  ofBitVec ::
  /--
  Unpacks a `UInt128` into a `BitVec 128`. This function is overridden with a native implementation.
  -/
  toBitVec : BitVec 128

def UInt128.ofNatLT (n : @& Nat) (h : LT.lt n UInt128.size) : UInt128 where
  toBitVec := BitVec.ofNatLT n h

def UInt128.decEq (a b : UInt128) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m)
      (fun h => isTrue (h ▸ rfl))
      (fun h => isFalse (fun h' => UInt128.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt128 := UInt128.decEq

instance : Inhabited UInt128 where
  default := UInt128.ofNatLT 0 (of_decide_eq_true rfl)

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/UInt/BasicAux.lean
-- Target: Hax/MissingLean/Init/Data/UInt/BasicAux.lean
-- ──────────────────────────────────────────────────────────────────────

def UInt128.toFin (x : UInt128) : Fin UInt128.size := x.toBitVec.toFin

def UInt128.ofNat (n : @& Nat) : UInt128 := ⟨BitVec.ofNat 128 n⟩

def UInt128.ofNatTruncate (n : Nat) : UInt128 :=
  if h : n < UInt128.size then
    UInt128.ofNatLT n h
  else
    UInt128.ofNatLT (UInt128.size - 1) (by decide)

abbrev Nat.toUInt128 := UInt128.ofNat

def UInt128.toNat (n : UInt128) : Nat := n.toBitVec.toNat

def UInt128.toUInt8 (a : UInt128) : UInt8 := a.toNat.toUInt8

def UInt128.toUInt16 (a : UInt128) : UInt16 := a.toNat.toUInt16

def UInt128.toUInt32 (a : UInt128) : UInt32 := a.toNat.toUInt32

def UInt8.toUInt128 (a : UInt8) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩

def UInt16.toUInt128 (a : UInt16) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩

def UInt32.toUInt128 (a : UInt32) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩

instance UInt128.instOfNat : OfNat UInt128 n := ⟨UInt128.ofNat n⟩

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/UInt/Basic.lean
-- Target: Hax/MissingLean/Init/Data/UInt/Basic.lean
-- ──────────────────────────────────────────────────────────────────────

@[inline] def UInt128.ofFin (a : Fin UInt128.size) : UInt128 := ⟨⟨a⟩⟩

def UInt128.ofInt (x : Int) : UInt128 := ofNat (x % 2 ^ 128).toNat

protected def UInt128.add (a b : UInt128) : UInt128 := ⟨a.toBitVec + b.toBitVec⟩

protected def UInt128.sub (a b : UInt128) : UInt128 := ⟨a.toBitVec - b.toBitVec⟩

protected def UInt128.mul (a b : UInt128) : UInt128 := ⟨a.toBitVec * b.toBitVec⟩

protected def UInt128.div (a b : UInt128) : UInt128 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩

protected def UInt128.pow (x : UInt128) (n : Nat) : UInt128 :=
  match n with
  | 0 => 1
  | n + 1 => UInt128.mul (UInt128.pow x n) x

protected def UInt128.mod (a b : UInt128) : UInt128 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩

@[deprecated UInt128.mod (since := "2024-09-23")]
protected def UInt128.modn (a : UInt128) (n : Nat) : UInt128 := ⟨Fin.modn a.toFin n⟩

protected def UInt128.land (a b : UInt128) : UInt128 := ⟨a.toBitVec &&& b.toBitVec⟩

protected def UInt128.lor (a b : UInt128) : UInt128 := ⟨a.toBitVec ||| b.toBitVec⟩

protected def UInt128.xor (a b : UInt128) : UInt128 := ⟨a.toBitVec ^^^ b.toBitVec⟩

protected def UInt128.shiftLeft (a b : UInt128) : UInt128 := ⟨a.toBitVec <<< (UInt128.mod b 128).toBitVec⟩

protected def UInt128.shiftRight (a b : UInt128) : UInt128 := ⟨a.toBitVec >>> (UInt128.mod b 128).toBitVec⟩

protected def UInt128.lt (a b : UInt128) : Prop := a.toBitVec < b.toBitVec

protected def UInt128.le (a b : UInt128) : Prop := a.toBitVec ≤ b.toBitVec

instance : Add UInt128       := ⟨UInt128.add⟩

instance : Sub UInt128       := ⟨UInt128.sub⟩

instance : Mul UInt128       := ⟨UInt128.mul⟩

instance : Pow UInt128 Nat   := ⟨UInt128.pow⟩

instance : Mod UInt128       := ⟨UInt128.mod⟩

instance : HMod UInt128 Nat UInt128 := ⟨UInt128.modn⟩

instance : Div UInt128       := ⟨UInt128.div⟩

instance : LT UInt128        := ⟨UInt128.lt⟩

instance : LE UInt128        := ⟨UInt128.le⟩

protected def UInt128.complement (a : UInt128) : UInt128 := ⟨~~~a.toBitVec⟩

protected def UInt128.neg (a : UInt128) : UInt128 := ⟨-a.toBitVec⟩

instance : Complement UInt128 := ⟨UInt128.complement⟩

instance : Neg UInt128 := ⟨UInt128.neg⟩

instance : AndOp UInt128     := ⟨UInt128.land⟩

instance : OrOp UInt128      := ⟨UInt128.lor⟩

instance : XorOp UInt128       := ⟨UInt128.xor⟩

instance : ShiftLeft UInt128  := ⟨UInt128.shiftLeft⟩

instance : ShiftRight UInt128 := ⟨UInt128.shiftRight⟩

def Bool.toUInt128 (b : Bool) : UInt128 := if b then 1 else 0

@[instance_reducible]
def UInt128.decLt (a b : UInt128) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))

@[instance_reducible]
def UInt128.decLe (a b : UInt128) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))

attribute [instance] UInt128.decLt UInt128.decLe

instance : Max UInt128 := maxOfLe

instance : Min UInt128 := minOfLe

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/SInt/Basic.lean
-- Target: Hax/MissingLean/Init/Data/SInt/Basic_Int128.lean
-- ──────────────────────────────────────────────────────────────────────

set_option autoImplicit true

structure Int128 where
  ofUInt128 ::
  /--
  Converts an 64-bit signed integer into the 64-bit unsigned integer that is its two's complement
  encoding.
  -/
  toUInt128 : UInt128

instance : Hashable Int8 where
  hash i := i.toUInt8.toUInt128

instance : Hashable Int16 where
  hash i := i.toUInt16.toUInt128

instance : Hashable Int32 where
  hash i := i.toUInt32.toUInt128

abbrev Int128.size : Nat := 340282366920938463463374607431768211456

@[inline] def Int128.toBitVec (x : Int128) : BitVec 128 := x.toUInt128.toBitVec

theorem Int128.toBitVec.inj : {x y : Int128} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

@[inline] def UInt128.toInt128 (i : UInt128) : Int128 := Int128.ofUInt128 i

def Int128.ofInt (i : @& Int) : Int128 := ⟨⟨BitVec.ofInt 128 i⟩⟩

def Int128.ofNat (n : @& Nat) : Int128 := ⟨⟨BitVec.ofNat 128 n⟩⟩

abbrev Int.toInt128 := Int128.ofInt

abbrev Nat.toInt128 := Int128.ofNat

def Int128.toInt (i : Int128) : Int := i.toBitVec.toInt

@[suggest_for Int128.toNat, inline] def Int128.toNatClampNeg (i : Int128) : Nat := i.toInt.toNat

@[inline] def Int128.ofBitVec (b : BitVec 128) : Int128 := ⟨⟨b⟩⟩

def Int128.toInt8 (a : Int128) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩

def Int128.toInt16 (a : Int128) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩

def Int128.toInt32 (a : Int128) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩

def Int8.toInt128 (a : Int8) : Int128 := ⟨⟨a.toBitVec.signExtend 128⟩⟩

def Int16.toInt128 (a : Int16) : Int128 := ⟨⟨a.toBitVec.signExtend 128⟩⟩

def Int32.toInt128 (a : Int32) : Int128 := ⟨⟨a.toBitVec.signExtend 128⟩⟩

def Int128.neg (i : Int128) : Int128 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString Int128 where
  toString i := toString i.toInt

instance : Repr Int128 where
  reprPrec i prec := reprPrec i.toInt prec

instance : ReprAtom Int128 := ⟨⟩

instance : Hashable Int128 where
  hash i := i.toUInt128

instance Int128.instOfNat : OfNat Int128 n := ⟨Int128.ofNat n⟩

instance Int128.instNeg : Neg Int128 where
  neg := Int128.neg

abbrev Int128.maxValue : Int128 := 9223372036854775807

abbrev Int128.minValue : Int128 := -9223372036854775808

@[inline]
def Int128.ofIntLE (i : Int) (_hl : Int128.minValue.toInt ≤ i) (_hr : i ≤ Int128.maxValue.toInt) : Int128 :=
  Int128.ofInt i

def Int128.ofIntTruncate (i : Int) : Int128 :=
  if hl : Int128.minValue.toInt ≤ i then
    if hr : i ≤ Int128.maxValue.toInt then
      Int128.ofIntLE i hl hr
    else
      Int128.minValue
  else
    Int128.minValue

protected def Int128.add (a b : Int128) : Int128 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩

protected def Int128.sub (a b : Int128) : Int128 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩

protected def Int128.mul (a b : Int128) : Int128 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩

protected def Int128.div (a b : Int128) : Int128 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩

protected def Int128.pow (x : Int128) (n : Nat) : Int128 :=
  match n with
  | 0 => 1
  | n + 1 => Int128.mul (Int128.pow x n) x

protected def Int128.mod (a b : Int128) : Int128 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩

protected def Int128.land (a b : Int128) : Int128 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩

protected def Int128.lor (a b : Int128) : Int128 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩

protected def Int128.xor (a b : Int128) : Int128 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩

protected def Int128.shiftLeft (a b : Int128) : Int128 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 128)⟩⟩

protected def Int128.shiftRight (a b : Int128) : Int128 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 128)⟩⟩

protected def Int128.complement (a : Int128) : Int128 := ⟨⟨~~~a.toBitVec⟩⟩

protected def Int128.abs (a : Int128) : Int128 := ⟨⟨a.toBitVec.abs⟩⟩

def Int128.decEq (a b : Int128) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => Int128.noConfusion h' (fun h' => absurd h' h))

protected def Int128.lt (a b : Int128) : Prop := a.toBitVec.slt b.toBitVec

protected def Int128.le (a b : Int128) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited Int128 where
  default := 0

instance : Add Int128         := ⟨Int128.add⟩

instance : Sub Int128         := ⟨Int128.sub⟩

instance : Mul Int128         := ⟨Int128.mul⟩

instance : Pow Int128 Nat     := ⟨Int128.pow⟩

instance : Mod Int128         := ⟨Int128.mod⟩

instance : Div Int128         := ⟨Int128.div⟩

instance : LT Int128          := ⟨Int128.lt⟩

instance : LE Int128          := ⟨Int128.le⟩

instance : Complement Int128  := ⟨Int128.complement⟩

instance : AndOp Int128       := ⟨Int128.land⟩

instance : OrOp Int128        := ⟨Int128.lor⟩

instance : XorOp Int128         := ⟨Int128.xor⟩

instance : ShiftLeft Int128   := ⟨Int128.shiftLeft⟩

instance : ShiftRight Int128  := ⟨Int128.shiftRight⟩

instance : DecidableEq Int128 := Int128.decEq

def Bool.toInt128 (b : Bool) : Int128 := if b then 1 else 0

@[instance_reducible]
def Int128.decLt (a b : Int128) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

@[instance_reducible]
def Int128.decLe (a b : Int128) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

attribute [instance] Int128.decLt Int128.decLe

instance : Max Int128 := maxOfLe

instance : Min Int128 := minOfLe

def ISize.toInt128 (a : ISize) : Int128 := ⟨⟨a.toBitVec.signExtend 128⟩⟩

def Int128.toISize (a : Int128) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩

instance : Hashable ISize where
  hash i := i.toUSize.toUInt128

-- ──────────────────────────────────────────────────────────────────────
-- Source: Lean/ToExpr.lean
-- Target: Hax/MissingLean/Lean/ToExpr.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean

instance : ToExpr UInt128 where
  toTypeExpr := mkConst ``UInt128
  toExpr a :=
    let r := mkRawNatLit a.toNat
    mkApp3 (.const ``OfNat.ofNat [0]) (mkConst ``UInt128) r
      (.app (.const ``UInt128.instOfNat []) r)

instance : ToExpr Int128 where
  toTypeExpr := mkConst ``Int128
  toExpr i := if 0 ≤ i then
    mkNat i.toNatClampNeg
  else
    mkApp3 (.const ``Neg.neg [0]) (.const ``Int128 []) (.const ``Int128.instNeg [])
      (mkNat (-(i.toInt)).toNat)
where
  mkNat (n : Nat) : Expr :=
    let r := mkRawNatLit n
    mkApp3 (.const ``OfNat.ofNat [0]) (.const ``Int128 []) r
        (.app (.const ``Int128.instOfNat []) r)

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

-- declare_uint_simprocs_ext UInt128 -- macro call replaced with direct inline (macros don't handle dsimproc correctly)
namespace UInt128

def fromExpr (e : Expr) : SimpM (Option UInt128) := do
  let some (n, _) ← getOfNatValue? e ``UInt128 | return none
  return ofNat n

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : UInt128 → UInt128 → UInt128) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : UInt128 → UInt128 → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : UInt128 → UInt128 → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

dsimproc [simp, seval] reduceAdd ((_ + _ : UInt128)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, seval] reduceMul ((_ * _ : UInt128)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, seval] reduceSub ((_ - _ : UInt128)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, seval] reduceDiv ((_ / _ : UInt128)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, seval] reduceMod ((_ % _ : UInt128)) := reduceBin ``HMod.hMod 6 (· % ·)

simproc [simp, seval] reduceLT  (( _ : UInt128) < _)  := reduceBinPred ``LT.lt 4 (. < .)
simproc [simp, seval] reduceLE  (( _ : UInt128) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] reduceGT  (( _ : UInt128) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] reduceGE  (( _ : UInt128) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
simproc [simp, seval] reduceEq  (( _ : UInt128) = _)  := reduceBinPred ``Eq 3 (. = .)
simproc [simp, seval] reduceNe  (( _ : UInt128) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
dsimproc [simp, seval] reduceBEq  (( _ : UInt128) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
dsimproc [simp, seval] reduceBNe  (( _ : UInt128) != _)  := reduceBoolPred ``bne 4 (. != .)

dsimproc [simp, seval] reduceOfNatLT (ofNatLT _ _) := fun e => do
  unless e.isAppOfArity ``UInt128.ofNatLT 2 do return .continue
  let some value ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let value := ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfNat (ofNat _) := fun e => do
  unless e.isAppOfArity ``UInt128.ofNat 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceToNat (toNat _) := fun e => do
  unless e.isAppOfArity ``UInt128.toNat 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := toNat v
  return .done <| toExpr n

/-- Return `.done` for UInt values. We don't want to unfold in the symbolic evaluator. -/
dsimproc [seval] isValue ((OfNat.ofNat _ : UInt128)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end UInt128

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

-- declare_sint_simprocs_ext Int128 -- macro call replaced with direct inline
namespace Int128

def fromExpr (e : Expr) : SimpM (Option Int128) := do
  if let some (n, _) ← getOfNatValue? e ``Int128 then
    return some (ofNat n)
  let_expr Neg.neg _ _ a ← e | return none
  let some (n, _) ← getOfNatValue? a ``Int128 | return none
  return some (ofInt (- n))

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : Int128 → Int128 → Int128) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Int128 → Int128 → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : Int128 → Int128 → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

dsimproc [simp, seval] reduceNeg ((- _ : Int128)) := fun e => do
  let_expr Neg.neg _ _ arg ← e | return .continue
  if arg.isAppOfArity ``OfNat.ofNat 3 then
    -- We return .done to ensure `Neg.neg` is not unfolded even when `ground := true`.
    return .done e
  else
    let some v ← (fromExpr arg) | return .continue
    return .done <| toExpr (- v)

dsimproc [simp, seval] reduceAdd ((_ + _ : Int128)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, seval] reduceMul ((_ * _ : Int128)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, seval] reduceSub ((_ - _ : Int128)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, seval] reduceDiv ((_ / _ : Int128)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, seval] reduceMod ((_ % _ : Int128)) := reduceBin ``HMod.hMod 6 (· % ·)

simproc [simp, seval] reduceLT  (( _ : Int128) < _)  := reduceBinPred ``LT.lt 4 (. < .)
simproc [simp, seval] reduceLE  (( _ : Int128) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] reduceGT  (( _ : Int128) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] reduceGE  (( _ : Int128) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
simproc [simp, seval] reduceEq  (( _ : Int128) = _)  := reduceBinPred ``Eq 3 (. = .)
simproc [simp, seval] reduceNe  (( _ : Int128) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
dsimproc [simp, seval] reduceBEq  (( _ : Int128) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
dsimproc [simp, seval] reduceBNe  (( _ : Int128) != _)  := reduceBoolPred ``bne 4 (. != .)

dsimproc [simp, seval] reduceOfIntLE (ofIntLE _ _ _) := fun e => do
  unless e.isAppOfArity ``Int128.ofIntLE 3 do return .continue
  let some value ← Int.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  let value := ofInt value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfNat (ofNat _) := fun e => do
  unless e.isAppOfArity ``Int128.ofNat 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfInt (ofInt _) := fun e => do
  unless e.isAppOfArity ``Int128.ofInt 1 do return .continue
  let some value ← Int.fromExpr? e.appArg! | return .continue
  let value := ofInt value
  return .done <| toExpr value

dsimproc [simp, seval] reduceToInt (toInt _) := fun e => do
  unless e.isAppOfArity ``Int128.toInt 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := toInt v
  return .done <| toExpr n

dsimproc [simp, seval] reduceToNatClampNeg (toNatClampNeg _) := fun e => do
  unless e.isAppOfArity ``Int128.toNatClampNeg 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := toNatClampNeg v
  return .done <| toExpr n

/-- Return `.done` for Int values. We don't want to unfold in the symbolic evaluator. -/
dsimproc [seval] isValue ((OfNat.ofNat _ : Int128)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end Int128

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/UInt/Lemmas.lean
-- Target: Hax/MissingLean/Init/Data/UInt/Lemmas_UInt128.lean
-- ──────────────────────────────────────────────────────────────────────

set_option autoImplicit true
open Std

declare_uint_theorems UInt128 128

@[simp] theorem USize.toNat_toUInt128 (x : USize) : x.toUInt128.toNat = x.toNat := (rfl)

theorem UInt128.ofNat_mod_size : ofNat (x % 2 ^ 128) = ofNat x := by
  simp [ofNat, BitVec.ofNat, Fin.ofNat]

theorem UInt128.ofNat_size : ofNat size = 0 := by decide

theorem UInt128.lt_ofNat_iff {n : UInt128} {m : Nat} (h : m < size) : n < ofNat m ↔ n.toNat < m := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]

theorem UInt128.ofNat_lt_iff {n : UInt128} {m : Nat} (h : m < size) : ofNat m < n ↔ m < n.toNat := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]

theorem UInt128.le_ofNat_iff {n : UInt128} {m : Nat} (h : m < size) : n ≤ ofNat m ↔ n.toNat ≤ m := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]

theorem UInt128.ofNat_le_iff {n : UInt128} {m : Nat} (h : m < size) : ofNat m ≤ n ↔ m ≤ n.toNat := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]

protected theorem UInt128.mod_eq_of_lt {a b : UInt128} (h : a < b) : a % b = a := UInt128.toNat_inj.1 (Nat.mod_eq_of_lt h)

@[simp] theorem UInt128.toNat_lt (n : UInt128) : n.toNat < 2 ^ 128 := n.toFin.isLt

theorem USize.size_le_uint128Size : USize.size ≤ UInt128.size := by
  cases USize.size_eq <;> simp_all +decide

theorem USize.size_dvd_uInt128Size : USize.size ∣ UInt128.size := by cases USize.size_eq <;> simp_all +decide

@[simp] theorem mod_uInt128Size_uSizeSize (n : Nat) : n % UInt128.size % USize.size = n % USize.size :=
  Nat.mod_mod_of_dvd _ USize.size_dvd_uInt128Size

@[simp] theorem UInt128.size_sub_one_mod_uSizeSize : 18446744073709551615 % USize.size = USize.size - 1 := by
  cases USize.size_eq <;> simp_all +decide

@[simp] theorem UInt8.toNat_mod_uInt128Size (n : UInt8) : n.toNat % UInt128.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))

@[simp] theorem UInt16.toNat_mod_uInt128Size (n : UInt16) : n.toNat % UInt128.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))

@[simp] theorem UInt32.toNat_mod_uInt128Size (n : UInt32) : n.toNat % UInt128.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))

@[simp] theorem UInt128.toNat_mod_size (n : UInt128) : n.toNat % UInt128.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt

@[simp] theorem USize.toNat_mod_uInt128Size (n : USize) : n.toNat % UInt128.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt

@[simp] theorem UInt8.toUInt128_mod_256 (n : UInt8) : n.toUInt128 % 256 = n.toUInt128 := UInt128.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt128_mod_65536 (n : UInt16) : n.toUInt128 % 65536 = n.toUInt128 := UInt128.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt128_mod_4294967296 (n : UInt32) : n.toUInt128 % 4294967296 = n.toUInt128 := UInt128.toNat.inj (by simp)

@[simp] theorem Fin.mk_uInt128ToNat (n : UInt128) : Fin.mk n.toNat (by exact n.toFin.isLt) = n.toFin := (rfl)

@[simp] theorem BitVec.ofNatLT_uInt128ToNat (n : UInt128) : BitVec.ofNatLT n.toNat (by exact n.toFin.isLt) = n.toBitVec := (rfl)

@[simp] theorem BitVec.ofFin_uInt128ToFin (n : UInt128) : BitVec.ofFin n.toFin = n.toBitVec := (rfl)

@[simp] theorem UInt8.toFin_toUInt128 (n : UInt8) : n.toUInt128.toFin = n.toFin.castLE (by decide) := (rfl)

@[simp] theorem UInt16.toFin_toUInt128 (n : UInt16) : n.toUInt128.toFin = n.toFin.castLE (by decide) := (rfl)

@[simp] theorem UInt32.toFin_toUInt128 (n : UInt32) : n.toUInt128.toFin = n.toFin.castLE (by decide) := (rfl)

@[simp] theorem USize.toFin_toUInt128 (n : USize) : n.toUInt128.toFin = n.toFin.castLE size_le_uint128Size := (rfl)

@[simp, int_toBitVec] theorem UInt128.toBitVec_toUInt8 (n : UInt128) : n.toUInt8.toBitVec = n.toBitVec.setWidth 8 := (rfl)

@[simp, int_toBitVec] theorem UInt128.toBitVec_toUInt16 (n : UInt128) : n.toUInt16.toBitVec = n.toBitVec.setWidth 16 := (rfl)

@[simp, int_toBitVec] theorem UInt128.toBitVec_toUInt32 (n : UInt128) : n.toUInt32.toBitVec = n.toBitVec.setWidth 32 := (rfl)

@[simp, int_toBitVec] theorem UInt8.toBitVec_toUInt128 (n : UInt8) : n.toUInt128.toBitVec = n.toBitVec.setWidth 64 := (rfl)

@[simp, int_toBitVec] theorem UInt16.toBitVec_toUInt128 (n : UInt16) : n.toUInt128.toBitVec = n.toBitVec.setWidth 64 := (rfl)

@[simp, int_toBitVec] theorem UInt32.toBitVec_toUInt128 (n : UInt32) : n.toUInt128.toBitVec = n.toBitVec.setWidth 64 := (rfl)

@[simp, int_toBitVec] theorem USize.toBitVec_toUInt128 (n : USize) : n.toUInt128.toBitVec = n.toBitVec.setWidth 64 :=
  BitVec.eq_of_toNat_eq (by simp)

@[simp, int_toBitVec] theorem UInt128.toBitVec_toUSize (n : UInt128) : n.toUSize.toBitVec = n.toBitVec.setWidth System.Platform.numBits :=
  BitVec.eq_of_toNat_eq (by simp)

@[simp] theorem UInt128.ofNatLT_uInt8ToNat (n : UInt8) : UInt128.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt128 := (rfl)

@[simp] theorem UInt128.ofNatLT_uInt16ToNat (n : UInt16) : UInt128.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt128 := (rfl)

@[simp] theorem UInt128.ofNatLT_uInt32ToNat (n : UInt32) : UInt128.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt128 := (rfl)

@[simp] theorem UInt128.ofNatLT_toNat (n : UInt128) : UInt128.ofNatLT n.toNat n.toNat_lt = n := (rfl)

@[simp] theorem UInt128.ofNatLT_uSizeToNat (n : USize) : UInt128.ofNatLT n.toNat n.toNat_lt = n.toUInt128 := (rfl)

theorem UInt8.ofNatLT_uInt128ToNat (n : UInt128) (h) : UInt8.ofNatLT n.toNat h = n.toUInt8 :=
  UInt8.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem UInt16.ofNatLT_uInt128ToNat (n : UInt128) (h) : UInt16.ofNatLT n.toNat h = n.toUInt16 :=
  UInt16.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem UInt32.ofNatLT_uInt128ToNat (n : UInt128) (h) : UInt32.ofNatLT n.toNat h = n.toUInt32 :=
  UInt32.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem USize.ofNatLT_uInt128ToNat (n : UInt128) (h) : USize.ofNatLT n.toNat h = n.toUSize :=
  USize.toNat.inj (by simp [Nat.mod_eq_of_lt h])

@[simp] theorem UInt128.ofFin_toFin (n : UInt128) : UInt128.ofFin n.toFin = n := (rfl)

@[simp] theorem UInt128.toFin_ofFin (n : Fin UInt128.size) : (UInt128.ofFin n).toFin = n := (rfl)

@[simp] theorem UInt128.ofFin_uint8ToFin (n : UInt8) : UInt128.ofFin (n.toFin.castLE (by decide)) = n.toUInt128 := (rfl)

@[simp] theorem UInt128.ofFin_uint16ToFin (n : UInt16) : UInt128.ofFin (n.toFin.castLE (by decide)) = n.toUInt128 := (rfl)

@[simp] theorem UInt128.ofFin_uint32ToFin (n : UInt32) : UInt128.ofFin (n.toFin.castLE (by decide)) = n.toUInt128 := (rfl)

@[simp] theorem Nat.toUInt128_eq {n : Nat} : n.toUInt128 = UInt128.ofNat n := (rfl)

@[simp] theorem UInt8.ofBitVec_uInt128ToBitVec (n : UInt128) :
    UInt8.ofBitVec (n.toBitVec.setWidth 8) = n.toUInt8 := (rfl)

@[simp] theorem UInt16.ofBitVec_uInt128ToBitVec (n : UInt128) :
    UInt16.ofBitVec (n.toBitVec.setWidth 16) = n.toUInt16 := (rfl)

@[simp] theorem UInt32.ofBitVec_uInt128ToBitVec (n : UInt128) :
    UInt32.ofBitVec (n.toBitVec.setWidth 32) = n.toUInt32 := (rfl)

@[simp] theorem UInt128.ofBitVec_uInt8ToBitVec (n : UInt8) :
    UInt128.ofBitVec (n.toBitVec.setWidth 64) = n.toUInt128 := (rfl)

@[simp] theorem UInt128.ofBitVec_uInt16ToBitVec (n : UInt16) :
    UInt128.ofBitVec (n.toBitVec.setWidth 64) = n.toUInt128 := (rfl)

@[simp] theorem UInt128.ofBitVec_uInt32ToBitVec (n : UInt32) :
    UInt128.ofBitVec (n.toBitVec.setWidth 64) = n.toUInt128 := (rfl)

@[simp] theorem UInt128.ofBitVec_uSizeToBitVec (n : USize) :
    UInt128.ofBitVec (n.toBitVec.setWidth 64) = n.toUInt128 :=
  UInt128.toNat.inj (by simp)

@[simp] theorem USize.ofBitVec_uInt128ToBitVec (n : UInt128) :
    USize.ofBitVec (n.toBitVec.setWidth System.Platform.numBits) = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt8.ofNat_uInt128ToNat (n : UInt128) : UInt8.ofNat n.toNat = n.toUInt8 := (rfl)

@[simp] theorem UInt16.ofNat_uInt128ToNat (n : UInt128) : UInt16.ofNat n.toNat = n.toUInt16 := (rfl)

@[simp] theorem UInt32.ofNat_uInt128ToNat (n : UInt128) : UInt32.ofNat n.toNat = n.toUInt32 := (rfl)

@[simp] theorem UInt128.ofNat_uInt8ToNat (n : UInt8) : UInt128.ofNat n.toNat = n.toUInt128 :=
  UInt128.toNat.inj (by simp)

@[simp] theorem UInt128.ofNat_uInt16ToNat (n : UInt16) : UInt128.ofNat n.toNat = n.toUInt128 :=
  UInt128.toNat.inj (by simp)

@[simp] theorem UInt128.ofNat_uInt32ToNat (n : UInt32) : UInt128.ofNat n.toNat = n.toUInt128 :=
  UInt128.toNat.inj (by simp)

@[simp] theorem UInt128.ofNat_uSizeToNat (n : USize) : UInt128.ofNat n.toNat = n.toUInt128 :=
  UInt128.toNat.inj (by simp)

@[simp] theorem USize.ofNat_uInt128ToNat (n : UInt128) : USize.ofNat n.toNat = n.toUSize :=
  USize.toNat.inj (by simp)

theorem UInt128.ofNatLT_eq_ofNat (n : Nat) {h} : UInt128.ofNatLT n h = UInt128.ofNat n :=
  UInt128.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem UInt128.ofNatTruncate_eq_ofNat (n : Nat) (hn : n < UInt128.size) :
    UInt128.ofNatTruncate n = UInt128.ofNat n := by
  simp [ofNatTruncate, hn, UInt128.ofNatLT_eq_ofNat]

@[simp] theorem UInt128.ofNatTruncate_uInt8ToNat (n : UInt8) : UInt128.ofNatTruncate n.toNat = n.toUInt128 := by
  rw [UInt128.ofNatTruncate_eq_ofNat, ofNat_uInt8ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)

@[simp] theorem UInt128.ofNatTruncate_uInt16ToNat (n : UInt16) : UInt128.ofNatTruncate n.toNat = n.toUInt128 := by
  rw [UInt128.ofNatTruncate_eq_ofNat, ofNat_uInt16ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)

@[simp] theorem UInt128.ofNatTruncate_uInt32ToNat (n : UInt32) : UInt128.ofNatTruncate n.toNat = n.toUInt128 := by
  rw [UInt128.ofNatTruncate_eq_ofNat, ofNat_uInt32ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)

@[simp] theorem UInt128.ofNatTruncate_toNat (n : UInt128) : UInt128.ofNatTruncate n.toNat = n := by
  rw [UInt128.ofNatTruncate_eq_ofNat] <;> simp [n.toNat_lt]

@[simp] theorem UInt128.ofNatTruncate_uSizeToNat (n : USize) : UInt128.ofNatTruncate n.toNat = n.toUInt128 := by
  rw [UInt128.ofNatTruncate_eq_ofNat, ofNat_uSizeToNat]
  exact n.toNat_lt

@[simp] theorem UInt8.toUInt8_toUInt128 (n : UInt8) : n.toUInt128.toUInt8 = n :=
  UInt8.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt16_toUInt128 (n : UInt8) : n.toUInt128.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt32_toUInt128 (n : UInt8) : n.toUInt128.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt128_toUInt16 (n : UInt8) : n.toUInt16.toUInt128 = n.toUInt128 := (rfl)

@[simp] theorem UInt8.toUInt128_toUInt32 (n : UInt8) : n.toUInt32.toUInt128 = n.toUInt128 := (rfl)

@[simp] theorem UInt8.toUInt128_toUSize (n : UInt8) : n.toUSize.toUInt128 = n.toUInt128 := (rfl)

@[simp] theorem UInt8.toUSize_toUInt128 (n : UInt8) : n.toUInt128.toUSize = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt8_toUInt128 (n : UInt16) : n.toUInt128.toUInt8 = n.toUInt8 := (rfl)

@[simp] theorem UInt16.toUInt16_toUInt128 (n : UInt16) : n.toUInt128.toUInt16 = n :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt32_toUInt128 (n : UInt16) : n.toUInt128.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt128_toUInt8 (n : UInt16) : n.toUInt8.toUInt128 = n.toUInt128 % 256 := (rfl)

@[simp] theorem UInt16.toUInt128_toUInt32 (n : UInt16) : n.toUInt32.toUInt128 = n.toUInt128 := (rfl)

@[simp] theorem UInt16.toUInt128_toUSize (n : UInt16) : n.toUSize.toUInt128 = n.toUInt128 := (rfl)

@[simp] theorem UInt16.toUSize_toUInt128 (n : UInt16) : n.toUInt128.toUSize = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt8_toUInt128 (n : UInt32) : n.toUInt128.toUInt8 = n.toUInt8 := (rfl)

@[simp] theorem UInt32.toUInt16_toUInt128 (n : UInt32) : n.toUInt128.toUInt16 = n.toUInt16 := (rfl)

@[simp] theorem UInt32.toUInt32_toUInt128 (n : UInt32) : n.toUInt128.toUInt32 = n :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt128_toUInt8 (n : UInt32) : n.toUInt8.toUInt128 = n.toUInt128 % 256 := (rfl)

@[simp] theorem UInt32.toUInt128_toUInt16 (n : UInt32) : n.toUInt16.toUInt128 = n.toUInt128 % 65536 := (rfl)

@[simp] theorem UInt32.toUInt128_toUSize (n : UInt32) : n.toUSize.toUInt128 = n.toUInt128 := (rfl)

@[simp] theorem UInt32.toUSize_toUInt128 (n : UInt32) : n.toUInt128.toUSize = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt8_toUInt16 (n : UInt128) : n.toUInt16.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt8_toUInt32 (n : UInt128) : n.toUInt32.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt8_toUSize (n : UInt128) : n.toUSize.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt16_toUInt8 (n : UInt128) : n.toUInt8.toUInt16 = n.toUInt16 % 256 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt16_toUInt32 (n : UInt128) : n.toUInt32.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt16_toUSize (n : UInt128) : n.toUSize.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt32_toUInt8 (n : UInt128) : n.toUInt8.toUInt32 = n.toUInt32 % 256 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt32_toUInt16 (n : UInt128) : n.toUInt16.toUInt32 = n.toUInt32 % 65536 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt32_toUSize (n : UInt128) : n.toUSize.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt128_toUInt8 (n : UInt128) : n.toUInt8.toUInt128 = n % 256 := (rfl)

@[simp] theorem UInt128.toUInt128_toUInt16 (n : UInt128) : n.toUInt16.toUInt128 = n % 65536 := (rfl)

@[simp] theorem UInt128.toUInt128_toUInt32 (n : UInt128) : n.toUInt32.toUInt128 = n % 4294967296 := (rfl)

@[simp] theorem UInt128.toUSize_toUInt8 (n : UInt128) : n.toUInt8.toUSize = n.toUSize % 256 :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt128.toUSize_toUInt16 (n : UInt128) : n.toUInt16.toUSize = n.toUSize % 65536 :=
  USize.toNat.inj (by simp)

@[simp] theorem USize.toUInt8_toUInt128 (n : USize) : n.toUInt128.toUInt8 = n.toUInt8 := (rfl)

@[simp] theorem USize.toUInt16_toUInt128 (n : USize) : n.toUInt128.toUInt16 = n.toUInt16 := (rfl)

@[simp] theorem USize.toUInt128_toUInt8 (n : USize) : n.toUInt8.toUInt128 = n.toUInt128 % 256 := (rfl)

@[simp] theorem USize.toUInt128_toUInt16 (n : USize) : n.toUInt16.toUInt128 = n.toUInt128 % 65536 := (rfl)

@[simp] theorem USize.toUInt32_toUInt128 (n : USize) : n.toUInt128.toUInt32 = n.toUInt32 :=
  UInt32.toNat.inj (by simp)

@[simp] theorem USize.toUSize_toUInt128 (n : USize) : n.toUInt128.toUSize = n :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt128.toNat_ofFin (x : Fin UInt128.size) : (UInt128.ofFin x).toNat = x.val := (rfl)

theorem UInt128.toNat_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
    (UInt128.ofNatTruncate n).toNat = n := by rw [UInt128.ofNatTruncate, dif_pos hn, toNat_ofNatLT]

theorem UInt128.toNat_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toNat = UInt128.size - 1 := by rw [ofNatTruncate, dif_neg (by omega), toNat_ofNatLT]

@[simp] theorem UInt128.toFin_ofNatLT {n : Nat} (hn) : (UInt128.ofNatLT n hn).toFin = ⟨n, hn⟩ := (rfl)

@[simp] theorem UInt128.toFin.ofNat {n : Nat} : (UInt128.ofNat n).toFin = Fin.ofNat _ n := (rfl)

@[simp] theorem UInt128.toFin_ofBitVec {b} : (UInt128.ofBitVec b).toFin = b.toFin := (rfl)

theorem UInt128.toFin_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
    (UInt128.ofNatTruncate n).toFin = ⟨n, hn⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt128.toFin_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toFin = ⟨UInt128.size - 1, by decide⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_le hn])

@[simp, int_toBitVec] theorem UInt128.toBitVec_ofNatLT {n : Nat} (hn : n < UInt128.size) :
    (UInt128.ofNatLT n hn).toBitVec = BitVec.ofNatLT n hn := (rfl)

@[simp, int_toBitVec] theorem UInt128.toBitVec_ofFin (n : Fin UInt128.size) : (UInt128.ofFin n).toBitVec = BitVec.ofFin n := (rfl)

@[simp, int_toBitVec] theorem UInt128.toBitVec_ofBitVec (n) : (UInt128.ofBitVec n).toBitVec = n := (rfl)

theorem UInt128.toBitVec_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
    (UInt128.ofNatTruncate n).toBitVec = BitVec.ofNatLT n hn :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt128.toBitVec_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toBitVec = BitVec.ofNatLT (UInt128.size - 1) (by decide) :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt128.toUInt8_ofNatLT {n : Nat} (hn) : (UInt128.ofNatLT n hn).toUInt8 = UInt8.ofNat n := (rfl)

@[simp] theorem UInt128.toUInt8_ofFin (n) : (UInt128.ofFin n).toUInt8 = UInt8.ofNat n.val := (rfl)

@[simp] theorem UInt128.toUInt8_ofBitVec (b) : (UInt128.ofBitVec b).toUInt8 = UInt8.ofBitVec (b.setWidth _) := (rfl)

@[simp] theorem UInt128.toUInt8_ofNat' (n : Nat) : (UInt128.ofNat n).toUInt8 = UInt8.ofNat n := UInt8.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt8_ofNat {n : Nat} : toUInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toUInt8_ofNat' _

theorem UInt128.toUInt8_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
    (UInt128.ofNatTruncate n).toUInt8 = UInt8.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt8_ofNatLT]

theorem UInt128.toUInt8_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toUInt8 = UInt8.ofNatLT (UInt8.size - 1) (by decide) :=
  UInt8.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt128.toUInt16_ofNatLT {n : Nat} (hn) : (UInt128.ofNatLT n hn).toUInt16 = UInt16.ofNat n := (rfl)

@[simp] theorem UInt128.toUInt16_ofFin (n) : (UInt128.ofFin n).toUInt16 = UInt16.ofNat n.val := (rfl)

@[simp] theorem UInt128.toUInt16_ofBitVec (b) : (UInt128.ofBitVec b).toUInt16 = UInt16.ofBitVec (b.setWidth _) := (rfl)

@[simp] theorem UInt128.toUInt16_ofNat' (n : Nat) : (UInt128.ofNat n).toUInt16 = UInt16.ofNat n := UInt16.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt16_ofNat {n : Nat} : toUInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := UInt128.toUInt16_ofNat' _

theorem UInt128.toUInt16_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
    (UInt128.ofNatTruncate n).toUInt16 = UInt16.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt16_ofNatLT]

theorem UInt128.toUInt16_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toUInt16 = UInt16.ofNatLT (UInt16.size - 1) (by decide) :=
  UInt16.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt128.toUInt32_ofNatLT {n : Nat} (hn) : (UInt128.ofNatLT n hn).toUInt32 = UInt32.ofNat n := (rfl)

@[simp] theorem UInt128.toUInt32_ofFin (n) : (UInt128.ofFin n).toUInt32 = UInt32.ofNat n.val := (rfl)

@[simp] theorem UInt128.toUInt32_ofBitVec (b) : (UInt128.ofBitVec b).toUInt32 = UInt32.ofBitVec (b.setWidth _) := (rfl)

@[simp] theorem UInt128.toUInt32_ofNat' (n : Nat) : (UInt128.ofNat n).toUInt32 = UInt32.ofNat n := UInt32.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt32_ofNat {n : Nat} : toUInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := UInt128.toUInt32_ofNat' _

theorem UInt128.toUInt32_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
    (UInt128.ofNatTruncate n).toUInt32 = UInt32.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt32_ofNatLT]

theorem UInt128.toUInt32_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toUInt32 = UInt32.ofNatLT (UInt32.size - 1) (by decide) :=
  UInt32.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt128.toUSize_ofNatLT {n : Nat} (hn) : (UInt128.ofNatLT n hn).toUSize = USize.ofNat n := (rfl)

@[simp] theorem UInt128.toUSize_ofFin (n) : (UInt128.ofFin n).toUSize = USize.ofNat n.val := (rfl)

@[simp] theorem UInt128.toUSize_ofBitVec (b) : (UInt128.ofBitVec b).toUSize = USize.ofBitVec (b.setWidth _) :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt128.toUSize_ofNat' (n : Nat) : (UInt128.ofNat n).toUSize = USize.ofNat n := USize.toNat.inj (by simp)

@[simp] theorem UInt128.toUSize_ofNat {n : Nat} : toUSize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := UInt128.toUSize_ofNat' _

theorem UInt128.toUSize_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt128.size) :
    (UInt128.ofNatTruncate n).toUSize = USize.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUSize_ofNatLT]

theorem UInt128.toUSize_ofNatTruncate_of_le {n : Nat} (hn : UInt128.size ≤ n) :
    (UInt128.ofNatTruncate n).toUSize = USize.ofNatLT (USize.size - 1) (by cases USize.size_eq <;> simp_all) :=
  USize.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt8.toUInt128_ofNatLT {n : Nat} (h) :
    (UInt8.ofNatLT n h).toUInt128 = UInt128.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := (rfl)

theorem UInt8.toUInt128_ofFin {n} :
  (UInt8.ofFin n).toUInt128 = UInt128.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := (rfl)

@[simp] theorem UInt8.toUInt128_ofBitVec {b} : (UInt8.ofBitVec b).toUInt128 = UInt128.ofBitVec (b.setWidth _) := (rfl)

theorem UInt8.toUInt128_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt8.size) :
    (UInt8.ofNatTruncate n).toUInt128 = UInt128.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  UInt128.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt8.toUInt128_ofNatTruncate_of_le {n : Nat} (hn : UInt8.size ≤ n) :
    (UInt8.ofNatTruncate n).toUInt128 = UInt128.ofNatLT (UInt8.size - 1) (by decide) :=
  UInt128.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt16.toUInt128_ofNatLT {n : Nat} (h) :
    (UInt16.ofNatLT n h).toUInt128 = UInt128.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := (rfl)

theorem UInt16.toUInt128_ofFin {n} :
  (UInt16.ofFin n).toUInt128 = UInt128.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := (rfl)

@[simp] theorem UInt16.toUInt128_ofBitVec {b} : (UInt16.ofBitVec b).toUInt128 = UInt128.ofBitVec (b.setWidth _) := (rfl)

theorem UInt16.toUInt128_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt16.size) :
    (UInt16.ofNatTruncate n).toUInt128 = UInt128.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  UInt128.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt16.toUInt128_ofNatTruncate_of_le {n : Nat} (hn : UInt16.size ≤ n) :
    (UInt16.ofNatTruncate n).toUInt128 = UInt128.ofNatLT (UInt16.size - 1) (by decide) :=
  UInt128.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt32.toUInt128_ofNatLT {n : Nat} (h) :
    (UInt32.ofNatLT n h).toUInt128 = UInt128.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := (rfl)

theorem UInt32.toUInt128_ofFin {n} :
  (UInt32.ofFin n).toUInt128 = UInt128.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := (rfl)

@[simp] theorem UInt32.toUInt128_ofBitVec {b} : (UInt32.ofBitVec b).toUInt128 = UInt128.ofBitVec (b.setWidth _) := (rfl)

theorem UInt32.toUInt128_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt32.size) :
    (UInt32.ofNatTruncate n).toUInt128 = UInt128.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  UInt128.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt32.toUInt128_ofNatTruncate_of_le {n : Nat} (hn : UInt32.size ≤ n) :
    (UInt32.ofNatTruncate n).toUInt128 = UInt128.ofNatLT (UInt32.size - 1) (by decide) :=
  UInt128.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem USize.toUInt128_ofNatLT {n : Nat} (h) :
    (USize.ofNatLT n h).toUInt128 = UInt128.ofNatLT n (Nat.lt_of_lt_of_le h size_le_uint128Size) := (rfl)

theorem USize.toUInt128_ofFin {n} :
  (USize.ofFin n).toUInt128 = UInt128.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt size_le_uint128Size) := (rfl)

@[simp] theorem USize.toUInt128_ofBitVec {b} : (USize.ofBitVec b).toUInt128 = UInt128.ofBitVec (b.setWidth _) :=
  UInt128.toBitVec_inj.1 (by simp)

theorem USize.toUInt128_ofNatTruncate_of_lt {n : Nat} (hn : n < USize.size) :
    (USize.ofNatTruncate n).toUInt128 = UInt128.ofNatLT n (Nat.lt_of_lt_of_le hn size_le_uint128Size) :=
  UInt128.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem USize.toUInt128_ofNatTruncate_of_le {n : Nat} (hn : USize.size ≤ n) :
    (USize.ofNatTruncate n).toUInt128 = UInt128.ofNatLT (USize.size - 1) (by cases USize.size_eq <;> simp_all +decide) :=
  UInt128.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt8.toUInt128_ofNat' {n : Nat} (hn : n < UInt8.size) : (UInt8.ofNat n).toUInt128 = UInt128.ofNat n := by
  rw [← UInt8.ofNatLT_eq_ofNat (h := hn), toUInt128_ofNatLT, UInt128.ofNatLT_eq_ofNat]

@[simp] theorem UInt16.toUInt128_ofNat' {n : Nat} (hn : n < UInt16.size) : (UInt16.ofNat n).toUInt128 = UInt128.ofNat n := by
  rw [← UInt16.ofNatLT_eq_ofNat (h := hn), toUInt128_ofNatLT, UInt128.ofNatLT_eq_ofNat]

@[simp] theorem UInt32.toUInt128_ofNat' {n : Nat} (hn : n < UInt32.size) : (UInt32.ofNat n).toUInt128 = UInt128.ofNat n := by
  rw [← UInt32.ofNatLT_eq_ofNat (h := hn), toUInt128_ofNatLT, UInt128.ofNatLT_eq_ofNat]

@[simp] theorem USize.toUInt128_ofNat' {n : Nat} (hn : n < USize.size) : (USize.ofNat n).toUInt128 = UInt128.ofNat n := by
  rw [← USize.ofNatLT_eq_ofNat (h := hn), toUInt128_ofNatLT, UInt128.ofNatLT_eq_ofNat]

@[simp] theorem UInt8.toUInt128_ofNat {n : Nat} (hn : n < 256) : toUInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt8.toUInt128_ofNat' hn

@[simp] theorem UInt16.toUInt128_ofNat {n : Nat} (hn : n < 65536) : toUInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt16.toUInt128_ofNat' hn

@[simp] theorem UInt32.toUInt128_ofNat {n : Nat} (hn : n < 4294967296) : toUInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt32.toUInt128_ofNat' hn

@[simp] theorem USize.toUInt128_ofNat {n : Nat} (hn : n < 4294967296) : toUInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  USize.toUInt128_ofNat' (Nat.lt_of_lt_of_le hn UInt32.size_le_usizeSize)

@[simp] theorem UInt128.ofNatLT_finVal (n : Fin UInt128.size) : UInt128.ofNatLT n.val n.isLt = UInt128.ofFin n := (rfl)

@[simp] theorem UInt128.ofNatLT_bitVecToNat (n : BitVec 128) : UInt128.ofNatLT n.toNat n.isLt = UInt128.ofBitVec n := (rfl)

@[simp] theorem UInt128.ofNat_finVal (n : Fin UInt128.size) : UInt128.ofNat n.val = UInt128.ofFin n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_finVal]

@[simp] theorem UInt128.ofNat_bitVecToNat (n : BitVec 128) : UInt128.ofNat n.toNat = UInt128.ofBitVec n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_bitVecToNat]

@[simp] theorem UInt128.ofNatTruncate_finVal (n : Fin UInt128.size) : UInt128.ofNatTruncate n.val = UInt128.ofFin n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, UInt128.ofNat_finVal]

@[simp] theorem UInt128.ofNatTruncate_bitVecToNat (n : BitVec 128) : UInt128.ofNatTruncate n.toNat = UInt128.ofBitVec n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, ofNat_bitVecToNat]

@[simp] theorem UInt128.ofFin_mk {n : Nat} (hn) : UInt128.ofFin (Fin.mk n hn) = UInt128.ofNatLT n hn := (rfl)

@[simp] theorem UInt128.ofFin_bitVecToFin (n : BitVec 128) : UInt128.ofFin n.toFin = UInt128.ofBitVec n := (rfl)

@[simp] theorem UInt128.ofBitVec_ofNatLT {n : Nat} (hn) : UInt128.ofBitVec (BitVec.ofNatLT n hn) = UInt128.ofNatLT n hn := (rfl)

@[simp] theorem UInt128.ofBitVec_ofFin (n) : UInt128.ofBitVec (BitVec.ofFin n) = UInt128.ofFin n := (rfl)

@[simp] theorem BitVec.ofNat_uInt128ToNat (n : UInt128) : BitVec.ofNat 128 n.toNat = n.toBitVec :=
  BitVec.eq_of_toNat_eq (by simp)

@[simp] protected theorem UInt128.toFin_div (a b : UInt128) : (a / b).toFin = a.toFin / b.toFin := (rfl)

@[simp] theorem UInt8.toUInt128_div (a b : UInt8) : (a / b).toUInt128 = a.toUInt128 / b.toUInt128 := (rfl)

@[simp] theorem UInt16.toUInt128_div (a b : UInt16) : (a / b).toUInt128 = a.toUInt128 / b.toUInt128 := (rfl)

@[simp] theorem UInt32.toUInt128_div (a b : UInt32) : (a / b).toUInt128 = a.toUInt128 / b.toUInt128 := (rfl)

@[simp] theorem USize.toUInt128_div (a b : USize) : (a / b).toUInt128 = a.toUInt128 / b.toUInt128 := (rfl)

theorem UInt128.toUInt8_div (a b : UInt128) (ha : a < 256) (hb : b < 256) : (a / b).toUInt8 = a.toUInt8 / b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem UInt128.toUInt16_div (a b : UInt128) (ha : a < 65536) (hb : b < 65536) : (a / b).toUInt16 = a.toUInt16 / b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem UInt128.toUInt32_div (a b : UInt128) (ha : a < 4294967296) (hb : b < 4294967296) : (a / b).toUInt32 = a.toUInt32 / b.toUInt32 :=
  UInt32.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem UInt128.toUSize_div (a b : UInt128) (ha : a < 4294967296) (hb : b < 4294967296) : (a / b).toUSize = a.toUSize / b.toUSize :=
  USize.toNat.inj (Nat.div_mod_eq_mod_div_mod (Nat.lt_of_lt_of_le ha UInt32.size_le_usizeSize) (Nat.lt_of_lt_of_le hb UInt32.size_le_usizeSize))

theorem UInt128.toUSize_div_of_toNat_lt (a b : UInt128) (ha : a.toNat < USize.size) (hb : b.toNat < USize.size) :
    (a / b).toUSize = a.toUSize / b.toUSize :=
  USize.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

@[simp] protected theorem UInt128.toFin_mod (a b : UInt128) : (a % b).toFin = a.toFin % b.toFin := (rfl)

@[simp] theorem UInt8.toUInt128_mod (a b : UInt8) : (a % b).toUInt128 = a.toUInt128 % b.toUInt128 := (rfl)

@[simp] theorem UInt16.toUInt128_mod (a b : UInt16) : (a % b).toUInt128 = a.toUInt128 % b.toUInt128 := (rfl)

@[simp] theorem UInt32.toUInt128_mod (a b : UInt32) : (a % b).toUInt128 = a.toUInt128 % b.toUInt128 := (rfl)

@[simp] theorem USize.toUInt128_mod (a b : USize) : (a % b).toUInt128 = a.toUInt128 % b.toUInt128 := (rfl)

theorem UInt128.toUInt8_mod (a b : UInt128) (ha : a < 256) (hb : b < 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem UInt128.toUInt16_mod (a b : UInt128) (ha : a < 65536) (hb : b < 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem UInt128.toUInt32_mod (a b : UInt128) (ha : a < 4294967296) (hb : b < 4294967296) : (a % b).toUInt32 = a.toUInt32 % b.toUInt32 :=
  UInt32.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem UInt128.toUSize_mod (a b : UInt128) (ha : a < 4294967296) (hb : b < 4294967296) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (Nat.mod_mod_eq_mod_mod_mod (Nat.lt_of_lt_of_le ha UInt32.size_le_usizeSize) (Nat.lt_of_lt_of_le hb UInt32.size_le_usizeSize))

theorem UInt128.toUSize_mod_of_toNat_lt (a b : UInt128) (ha : a.toNat < USize.size) (hb : b.toNat < USize.size) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem UInt128.toUInt8_mod_of_dvd (a b : UInt128) (hb : b.toNat ∣ 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem UInt128.toUInt16_mod_of_dvd (a b : UInt128)(hb : b.toNat ∣ 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem UInt128.toUInt32_mod_of_dvd (a b : UInt128) (hb : b.toNat ∣ 4294967296) : (a % b).toUInt32 = a.toUInt32 % b.toUInt32 :=
  UInt32.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem UInt128.toUSize_mod_of_dvd (a b : UInt128) (hb : b.toNat ∣ 4294967296) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (Nat.mod_mod_eq_mod_mod_mod_of_dvd (Nat.dvd_trans hb UInt32.size_dvd_usizeSize))

theorem UInt128.toUSize_mod_of_dvd_usizeSize (a b : UInt128) (hb : b.toNat ∣ USize.size) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

@[simp] protected theorem UInt128.toFin_add (a b : UInt128) : (a + b).toFin = a.toFin + b.toFin := (rfl)

@[simp] theorem UInt128.toUInt8_add (a b : UInt128) : (a + b).toUInt8 = a.toUInt8 + b.toUInt8 := UInt8.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt16_add (a b : UInt128) : (a + b).toUInt16 = a.toUInt16 + b.toUInt16 := UInt16.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt32_add (a b : UInt128) : (a + b).toUInt32 = a.toUInt32 + b.toUInt32 := UInt32.toNat.inj (by simp)

@[simp] theorem UInt128.toUSize_add (a b : UInt128) : (a + b).toUSize = a.toUSize + b.toUSize := USize.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt128_add (a b : UInt8) : (a + b).toUInt128 = (a.toUInt128 + b.toUInt128) % 256 := UInt128.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt128_add (a b : UInt16) : (a + b).toUInt128 = (a.toUInt128 + b.toUInt128) % 65536 := UInt128.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt128_add (a b : UInt32) : (a + b).toUInt128 = (a.toUInt128 + b.toUInt128) % 4294967296 := UInt128.toNat.inj (by simp)

@[simp] protected theorem UInt128.toFin_sub (a b : UInt128) : (a - b).toFin = a.toFin - b.toFin := (rfl)

@[simp] protected theorem UInt128.toFin_mul (a b : UInt128) : (a * b).toFin = a.toFin * b.toFin := (rfl)

@[simp] theorem UInt128.toUInt8_mul (a b : UInt128) : (a * b).toUInt8 = a.toUInt8 * b.toUInt8 := UInt8.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt16_mul (a b : UInt128) : (a * b).toUInt16 = a.toUInt16 * b.toUInt16 := UInt16.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt32_mul (a b : UInt128) : (a * b).toUInt32 = a.toUInt32 * b.toUInt32 := UInt32.toNat.inj (by simp)

@[simp] theorem UInt128.toUSize_mul (a b : UInt128) : (a * b).toUSize = a.toUSize * b.toUSize := USize.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt128_mul (a b : UInt8) : (a * b).toUInt128 = (a.toUInt128 * b.toUInt128) % 256 := UInt128.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt128_mul (a b : UInt16) : (a * b).toUInt128 = (a.toUInt128 * b.toUInt128) % 65536 := UInt128.toNat.inj (by simp)

@[simp] theorem UInt32.toUInt128_mul (a b : UInt32) : (a * b).toUInt128 = (a.toUInt128 * b.toUInt128) % 4294967296 := UInt128.toNat.inj (by simp)

theorem UInt128.toUInt8_eq (a b : UInt128) : a.toUInt8 = b.toUInt8 ↔ a % 256 = b % 256 := by
  simp [← UInt8.toNat_inj, ← UInt128.toNat_inj]

theorem UInt128.toUInt16_eq (a b : UInt128) : a.toUInt16 = b.toUInt16 ↔ a % 65536 = b % 65536 := by
  simp [← UInt16.toNat_inj, ← UInt128.toNat_inj]

theorem UInt128.toUInt32_eq (a b : UInt128) : a.toUInt32 = b.toUInt32 ↔ a % 4294967296 = b % 4294967296 := by
  simp [← UInt32.toNat_inj, ← UInt128.toNat_inj]

theorem UInt8.toUInt128_eq_mod_256_iff (a : UInt8) (b : UInt128) : a.toUInt128 = b % 256 ↔ a = b.toUInt8 := by
  simp [← UInt8.toNat_inj, ← UInt128.toNat_inj]

theorem UInt16.toUInt128_eq_mod_65536_iff (a : UInt16) (b : UInt128) : a.toUInt128 = b % 65536 ↔ a = b.toUInt16 := by
  simp [← UInt16.toNat_inj, ← UInt128.toNat_inj]

theorem UInt32.toUInt128_eq_mod_4294967296_iff (a : UInt32) (b : UInt128) : a.toUInt128 = b % 4294967296 ↔ a = b.toUInt32 := by
  simp [← UInt32.toNat_inj, ← UInt128.toNat_inj]

theorem USize.toUInt128_eq_mod_usizeSize_iff (a : USize) (b : UInt128) : a.toUInt128 = b % UInt128.ofNat USize.size ↔ a = b.toUSize := by
  simp [← USize.toNat_inj, ← UInt128.toNat_inj, USize.size_eq_two_pow]
  cases System.Platform.numBits_eq <;> simp_all

theorem UInt8.toUInt128_inj {a b : UInt8} : a.toUInt128 = b.toUInt128 ↔ a = b :=
  ⟨fun h => by rw [← toUInt8_toUInt128 a, h, toUInt8_toUInt128], by rintro rfl; rfl⟩

theorem UInt16.toUInt128_inj {a b : UInt16} : a.toUInt128 = b.toUInt128 ↔ a = b :=
  ⟨fun h => by rw [← toUInt16_toUInt128 a, h, toUInt16_toUInt128], by rintro rfl; rfl⟩

theorem UInt32.toUInt128_inj {a b : UInt32} : a.toUInt128 = b.toUInt128 ↔ a = b :=
  ⟨fun h => by rw [← toUInt32_toUInt128 a, h, toUInt32_toUInt128], by rintro rfl; rfl⟩

theorem USize.toUInt128_inj {a b : USize} : a.toUInt128 = b.toUInt128 ↔ a = b :=
  ⟨fun h => by rw [← toUSize_toUInt128 a, h, toUSize_toUInt128], by rintro rfl; rfl⟩

theorem UInt128.lt_iff_toFin_lt {a b : UInt128} : a < b ↔ a.toFin < b.toFin := Iff.rfl

theorem UInt128.le_iff_toFin_le {a b : UInt128} : a ≤ b ↔ a.toFin ≤ b.toFin := Iff.rfl

@[simp] theorem UInt8.toUInt128_lt {a b : UInt8} : a.toUInt128 < b.toUInt128 ↔ a < b := by
  simp [lt_iff_toNat_lt, UInt128.lt_iff_toNat_lt]

@[simp] theorem UInt16.toUInt128_lt {a b : UInt16} : a.toUInt128 < b.toUInt128 ↔ a < b := by
  simp [lt_iff_toNat_lt, UInt128.lt_iff_toNat_lt]

@[simp] theorem UInt32.toUInt128_lt {a b : UInt32} : a.toUInt128 < b.toUInt128 ↔ a < b := by
  simp [lt_iff_toNat_lt, UInt128.lt_iff_toNat_lt]

@[simp] theorem USize.toUInt128_lt {a b : USize} : a.toUInt128 < b.toUInt128 ↔ a < b := by
  simp [lt_iff_toNat_lt, UInt128.lt_iff_toNat_lt]

@[simp] theorem UInt128.toUInt8_lt {a b : UInt128} : a.toUInt8 < b.toUInt8 ↔ a % 256 < b % 256 := by
  simp [lt_iff_toNat_lt, UInt8.lt_iff_toNat_lt]

@[simp] theorem UInt128.toUInt16_lt {a b : UInt128} : a.toUInt16 < b.toUInt16 ↔ a % 65536 < b % 65536 := by
  simp [lt_iff_toNat_lt, UInt16.lt_iff_toNat_lt]

@[simp] theorem UInt128.toUInt32_lt {a b : UInt128} : a.toUInt32 < b.toUInt32 ↔ a % 4294967296 < b % 4294967296 := by
  simp [lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt]

@[simp] theorem UInt128.toUSize_lt {a b : UInt128} : a.toUSize < b.toUSize ↔ a % UInt128.ofNat USize.size < b % UInt128.ofNat USize.size := by
  simp only [USize.lt_iff_toNat_lt, toNat_toUSize, lt_iff_toNat_lt, UInt128.toNat_mod, toNat_ofNat', Nat.reducePow]
  cases System.Platform.numBits_eq <;> simp_all [USize.size]

@[simp] theorem UInt8.toUInt128_le {a b : UInt8} : a.toUInt128 ≤ b.toUInt128 ↔ a ≤ b := by
  simp [le_iff_toNat_le, UInt128.le_iff_toNat_le]

@[simp] theorem UInt16.toUInt128_le {a b : UInt16} : a.toUInt128 ≤ b.toUInt128 ↔ a ≤ b := by
  simp [le_iff_toNat_le, UInt128.le_iff_toNat_le]

@[simp] theorem UInt32.toUInt128_le {a b : UInt32} : a.toUInt128 ≤ b.toUInt128 ↔ a ≤ b := by
  simp [le_iff_toNat_le, UInt128.le_iff_toNat_le]

@[simp] theorem USize.toUInt128_le {a b : USize} : a.toUInt128 ≤ b.toUInt128 ↔ a ≤ b := by
  simp [le_iff_toNat_le, UInt128.le_iff_toNat_le]

@[simp] theorem UInt128.toUInt8_le {a b : UInt128} : a.toUInt8 ≤ b.toUInt8 ↔ a % 256 ≤ b % 256 := by
  simp [le_iff_toNat_le, UInt8.le_iff_toNat_le]

@[simp] theorem UInt128.toUInt16_le {a b : UInt128} : a.toUInt16 ≤ b.toUInt16 ↔ a % 65536 ≤ b % 65536 := by
  simp [le_iff_toNat_le, UInt16.le_iff_toNat_le]

@[simp] theorem UInt128.toUInt32_le {a b : UInt128} : a.toUInt32 ≤ b.toUInt32 ↔ a % 4294967296 ≤ b % 4294967296 := by
  simp [le_iff_toNat_le, UInt32.le_iff_toNat_le]

@[simp] theorem UInt128.toUSize_le {a b : UInt128} : a.toUSize ≤ b.toUSize ↔ a % UInt128.ofNat USize.size ≤ b % UInt128.ofNat USize.size := by
  simp only [USize.le_iff_toNat_le, toNat_toUSize, le_iff_toNat_le, UInt128.toNat_mod]
  cases System.Platform.numBits_eq <;> simp_all [USize.size]

@[simp] theorem UInt128.toUInt8_neg (a : UInt128) : (-a).toUInt8 = -a.toUInt8 := UInt8.toBitVec_inj.1 (by simp)

@[simp] theorem UInt128.toUInt16_neg (a : UInt128) : (-a).toUInt16 = -a.toUInt16 := UInt16.toBitVec_inj.1 (by simp)

@[simp] theorem UInt128.toUInt32_neg (a : UInt128) : (-a).toUInt32 = -a.toUInt32 := UInt32.toBitVec_inj.1 (by simp)

@[simp] theorem UInt128.toUSize_neg (a : UInt128) : (-a).toUSize = -a.toUSize := USize.toBitVec_inj.1 (by simp)

@[simp] theorem UInt8.toUInt128_neg (a : UInt8) : (-a).toUInt128 = -a.toUInt128 % 256 := by
  simp [UInt8.toUInt128_eq_mod_256_iff]

@[simp] theorem UInt16.toUInt128_neg (a : UInt16) : (-a).toUInt128 = -a.toUInt128 % 65536 := by
  simp [UInt16.toUInt128_eq_mod_65536_iff]

@[simp] theorem UInt32.toUInt128_neg (a : UInt32) : (-a).toUInt128 = -a.toUInt128 % 4294967296 := by
  simp [UInt32.toUInt128_eq_mod_4294967296_iff]

@[simp] theorem USize.toUInt128_neg (a : USize) : (-a).toUInt128 = -a.toUInt128 % UInt128.ofNat USize.size := by
  simp [USize.toUInt128_eq_mod_usizeSize_iff]

@[simp] theorem UInt128.toNat_neg (a : UInt128) : (-a).toNat = (UInt128.size - a.toNat) % UInt128.size := (rfl)

protected theorem UInt128.sub_eq_add_neg (a b : UInt128) : a - b = a + (-b) := UInt128.toBitVec_inj.1 (BitVec.sub_eq_add_neg _ _)

protected theorem UInt128.add_neg_eq_sub {a b : UInt128} : a + -b = a - b := UInt128.toBitVec_inj.1 BitVec.add_neg_eq_sub

theorem UInt128.neg_one_eq : (-1 : UInt128) = 18446744073709551615 := (rfl)

theorem UInt128.toBitVec_zero : toBitVec 0 = 0#128 := (rfl)

theorem UInt128.toBitVec_one : toBitVec 1 = 1#128 := (rfl)

theorem UInt128.neg_eq_neg_one_mul (a : UInt128) : -a = -1 * a := by
  apply UInt128.toBitVec_inj.1
  rw [UInt128.toBitVec_neg, UInt128.toBitVec_mul, UInt128.toBitVec_neg, UInt128.toBitVec_one, BitVec.neg_eq_neg_one_mul]

theorem UInt128.sub_eq_add_mul (a b : UInt128) : a - b = a + 18446744073709551615 * b := by
  rw [UInt128.sub_eq_add_neg, neg_eq_neg_one_mul, neg_one_eq]

@[simp] theorem USize.ofNat_uInt128Size_sub_one : USize.ofNat (UInt128.size - 1) = USize.ofNatLT (USize.size - 1) (Nat.sub_one_lt (Nat.pos_iff_ne_zero.1 size_pos)) :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt128.toUInt8_sub (a b : UInt128) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := by
  simp [UInt128.sub_eq_add_neg, UInt8.sub_eq_add_neg]

@[simp] theorem UInt128.toUInt16_sub (a b : UInt128) : (a - b).toUInt16 = a.toUInt16 - b.toUInt16 := by
  simp [UInt128.sub_eq_add_neg, UInt16.sub_eq_add_neg]

@[simp] theorem UInt128.toUInt32_sub (a b : UInt128) : (a - b).toUInt32 = a.toUInt32 - b.toUInt32 := by
  simp [UInt128.sub_eq_add_neg, UInt32.sub_eq_add_neg]

@[simp] theorem UInt128.toUSize_sub (a b : UInt128) : (a - b).toUSize = a.toUSize - b.toUSize := by
  simp [UInt128.sub_eq_add_neg, USize.sub_eq_add_neg]

@[simp] theorem UInt8.toUInt128_sub (a b : UInt8) : (a - b).toUInt128 = (a.toUInt128 - b.toUInt128) % 256 := by
  simp [UInt8.toUInt128_eq_mod_256_iff]

@[simp] theorem UInt16.toUInt128_sub (a b : UInt16) : (a - b).toUInt128 = (a.toUInt128 - b.toUInt128) % 65536 := by
  simp [UInt16.toUInt128_eq_mod_65536_iff]

@[simp] theorem UInt32.toUInt128_sub (a b : UInt32) : (a - b).toUInt128 = (a.toUInt128 - b.toUInt128) % 4294967296 := by
  simp [UInt32.toUInt128_eq_mod_4294967296_iff]

@[simp] theorem USize.toUInt128_sub (a b : USize) : (a - b).toUInt128 = (a.toUInt128 - b.toUInt128) % UInt128.ofNat USize.size := by
  simp [USize.toUInt128_eq_mod_usizeSize_iff]

@[simp] theorem UInt128.ofBitVec_neg (b : BitVec 128) : UInt128.ofBitVec (-b) = -UInt128.ofBitVec b := (rfl)

@[simp] theorem UInt128.ofFin_div (a b : Fin UInt128.size) : UInt128.ofFin (a / b) = UInt128.ofFin a / UInt128.ofFin b := (rfl)

@[simp] theorem UInt128.ofBitVec_div (a b : BitVec 128) : UInt128.ofBitVec (a / b) = UInt128.ofBitVec a / UInt128.ofBitVec b := (rfl)

@[simp] theorem UInt128.ofFin_mod (a b : Fin UInt128.size) : UInt128.ofFin (a % b) = UInt128.ofFin a % UInt128.ofFin b := (rfl)

@[simp] theorem UInt128.ofBitVec_mod (a b : BitVec 128) : UInt128.ofBitVec (a % b) = UInt128.ofBitVec a % UInt128.ofBitVec b := (rfl)

theorem UInt128.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : UInt128) : UInt128.ofNat a = b ↔ a % 2 ^ 128 = b.toNat := by
  simp [← UInt128.toNat_inj]

@[simp] theorem UInt128.ofNat_div {a b : Nat} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128) :
    UInt128.ofNat (a / b) = UInt128.ofNat a / UInt128.ofNat b := by
  simp [UInt128.ofNat_eq_iff_mod_eq_toNat, Nat.div_mod_eq_mod_div_mod ha hb]

@[simp] theorem UInt128.ofNatLT_div {a b : Nat} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128) :
    UInt128.ofNatLT (a / b) (Nat.div_lt_of_lt ha) = UInt128.ofNatLT a ha / UInt128.ofNatLT b hb := by
  simp [UInt128.ofNatLT_eq_ofNat, UInt128.ofNat_div ha hb]

@[simp] theorem UInt128.ofNat_mod {a b : Nat} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128) :
    UInt128.ofNat (a % b) = UInt128.ofNat a % UInt128.ofNat b := by
  simp [UInt128.ofNat_eq_iff_mod_eq_toNat, Nat.mod_mod_eq_mod_mod_mod ha hb]

@[simp] theorem UInt128.ofNatLT_mod {a b : Nat} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128) :
    UInt128.ofNatLT (a % b) (Nat.mod_lt_of_lt ha) = UInt128.ofNatLT a ha % UInt128.ofNatLT b hb := by
  simp [UInt128.ofNatLT_eq_ofNat, UInt128.ofNat_mod ha hb]

@[simp] theorem UInt128.ofInt_one : ofInt 1 = 1 := (rfl)

@[simp] theorem UInt128.ofInt_neg_one : ofInt (-1) = -1 := (rfl)

@[simp] theorem UInt128.ofNat_add (a b : Nat) : UInt128.ofNat (a + b) = UInt128.ofNat a + UInt128.ofNat b := by
  simp [UInt128.ofNat_eq_iff_mod_eq_toNat]

@[simp] theorem UInt128.ofInt_add (x y : Int) : UInt128.ofInt (x + y) = UInt128.ofInt x + UInt128.ofInt y := by
  dsimp only [UInt128.ofInt]
  rw [Int.add_emod]
  have h₁ : 0 ≤ x % 2 ^ 128 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 128 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ x % 2 ^ 128 + y % 2 ^ 128 := Int.add_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_add h₁ h₂]
  have : (2 ^ 128 : Int).toNat = 2 ^ 128 := (rfl)
  rw [this, UInt128.ofNat_mod_size, UInt128.ofNat_add]

@[simp] theorem UInt128.ofNatLT_add {a b : Nat} (hab : a + b < 2 ^ 128) :
    UInt128.ofNatLT (a + b) hab = UInt128.ofNatLT a (Nat.lt_of_add_right_lt hab) + UInt128.ofNatLT b (Nat.lt_of_add_left_lt hab) := by
  simp [UInt128.ofNatLT_eq_ofNat]

@[simp] theorem UInt128.ofFin_add (a b : Fin UInt128.size) : UInt128.ofFin (a + b) = UInt128.ofFin a + UInt128.ofFin b := (rfl)

@[simp] theorem UInt128.ofBitVec_add (a b : BitVec 128) : UInt128.ofBitVec (a + b) = UInt128.ofBitVec a + UInt128.ofBitVec b := (rfl)

@[simp] theorem UInt128.ofFin_sub (a b : Fin UInt128.size) : UInt128.ofFin (a - b) = UInt128.ofFin a - UInt128.ofFin b := (rfl)

@[simp] theorem UInt128.ofBitVec_sub (a b : BitVec 128) : UInt128.ofBitVec (a - b) = UInt128.ofBitVec a - UInt128.ofBitVec b := (rfl)

@[simp] protected theorem UInt128.add_sub_cancel (a b : UInt128) : a + b - b = a := UInt128.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)

theorem UInt128.ofNat_sub {a b : Nat} (hab : b ≤ a) : UInt128.ofNat (a - b) = UInt128.ofNat a - UInt128.ofNat b := by
  rw [(Nat.sub_add_cancel hab ▸ UInt128.ofNat_add (a - b) b :), UInt128.add_sub_cancel]

theorem UInt128.ofNatLT_sub {a b : Nat} (ha : a < 2 ^ 128) (hab : b ≤ a) :
    UInt128.ofNatLT (a - b) (Nat.sub_lt_of_lt ha) = UInt128.ofNatLT a ha - UInt128.ofNatLT b (Nat.lt_of_le_of_lt hab ha) := by
  simp [UInt128.ofNatLT_eq_ofNat, UInt128.ofNat_sub hab]

@[simp] theorem UInt128.ofNat_mul (a b : Nat) : UInt128.ofNat (a * b) = UInt128.ofNat a * UInt128.ofNat b := by
  simp [UInt128.ofNat_eq_iff_mod_eq_toNat]

@[simp] theorem UInt128.ofInt_mul (x y : Int) : ofInt (x * y) = ofInt x * ofInt y := by
  dsimp only [UInt128.ofInt]
  rw [Int.mul_emod]
  have h₁ : 0 ≤ x % 2 ^ 128 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 128 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ (x % 2 ^ 128) * (y % 2 ^ 128) := Int.mul_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_mul h₁ h₂]
  have : (2 ^ 128 : Int).toNat = 2 ^ 128 := (rfl)
  rw [this, UInt128.ofNat_mod_size, UInt128.ofNat_mul]

@[simp] theorem UInt128.ofNatLT_mul {a b : Nat} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128) (hab : a * b < 2 ^ 128) :
    UInt128.ofNatLT (a * b) hab = UInt128.ofNatLT a ha * UInt128.ofNatLT b hb := by
  simp [UInt128.ofNatLT_eq_ofNat]

@[simp] theorem UInt128.ofFin_mul (a b : Fin UInt128.size) : UInt128.ofFin (a * b) = UInt128.ofFin a * UInt128.ofFin b := (rfl)

@[simp] theorem UInt128.ofBitVec_mul (a b : BitVec 128) : UInt128.ofBitVec (a * b) = UInt128.ofBitVec a * UInt128.ofBitVec b := (rfl)

theorem UInt128.ofFin_lt_iff_lt {a b : Fin UInt128.size} : UInt128.ofFin a < UInt128.ofFin b ↔ a < b := Iff.rfl

theorem UInt128.ofFin_le_iff_le {a b : Fin UInt128.size} : UInt128.ofFin a ≤ UInt128.ofFin b ↔ a ≤ b := Iff.rfl

theorem UInt128.ofBitVec_lt_iff_lt {a b : BitVec 128} : UInt128.ofBitVec a < UInt128.ofBitVec b ↔ a < b := Iff.rfl

theorem UInt128.ofBitVec_le_iff_le {a b : BitVec 128} : UInt128.ofBitVec a ≤ UInt128.ofBitVec b ↔ a ≤ b := Iff.rfl

theorem UInt128.ofNatLT_lt_iff_lt {a b : Nat} (ha : a < UInt128.size) (hb : b < UInt128.size) :
    UInt128.ofNatLT a ha < UInt128.ofNatLT b hb ↔ a < b := Iff.rfl

theorem UInt128.ofNatLT_le_iff_le {a b : Nat} (ha : a < UInt128.size) (hb : b < UInt128.size) :
    UInt128.ofNatLT a ha ≤ UInt128.ofNatLT b hb ↔ a ≤ b := Iff.rfl

theorem UInt128.ofNat_lt_iff_lt {a b : Nat} (ha : a < UInt128.size) (hb : b < UInt128.size) :
    UInt128.ofNat a < UInt128.ofNat b ↔ a < b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_lt_iff_lt]

theorem UInt128.ofNat_le_iff_le {a b : Nat} (ha : a < UInt128.size) (hb : b < UInt128.size) :
    UInt128.ofNat a ≤ UInt128.ofNat b ↔ a ≤ b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_le_iff_le]

theorem UInt128.toNat_one : (1 : UInt128).toNat = 1 := (rfl)

theorem UInt128.zero_lt_one : (0 : UInt128) < 1 := by simp

theorem UInt128.zero_ne_one : (0 : UInt128) ≠ 1 := by simp

protected theorem UInt128.add_assoc (a b c : UInt128) : a + b + c = a + (b + c) :=
  UInt128.toBitVec_inj.1 (BitVec.add_assoc _ _ _)

instance : Std.Associative (α := UInt128) (· + ·) := ⟨UInt128.add_assoc⟩

protected theorem UInt128.add_comm (a b : UInt128) : a + b = b + a := UInt128.toBitVec_inj.1 (BitVec.add_comm _ _)

instance : Std.Commutative (α := UInt128) (· + ·) := ⟨UInt128.add_comm⟩

@[simp] protected theorem UInt128.add_zero (a : UInt128) : a + 0 = a := UInt128.toBitVec_inj.1 (BitVec.add_zero _)

@[simp] protected theorem UInt128.zero_add (a : UInt128) : 0 + a = a := UInt128.toBitVec_inj.1 (BitVec.zero_add _)

instance : Std.LawfulIdentity (α := UInt128) (· + ·) 0 where
  left_id := UInt128.zero_add
  right_id := UInt128.add_zero

@[simp] protected theorem UInt128.sub_zero (a : UInt128) : a - 0 = a := UInt128.toBitVec_inj.1 (BitVec.sub_zero _)

@[simp] protected theorem UInt128.zero_sub (a : UInt128) : 0 - a = -a := UInt128.toBitVec_inj.1 (BitVec.zero_sub _)

@[simp] protected theorem UInt128.sub_self (a : UInt128) : a - a = 0 := UInt128.toBitVec_inj.1 (BitVec.sub_self _)

protected theorem UInt128.add_left_neg (a : UInt128) : -a + a = 0 := UInt128.toBitVec_inj.1 (BitVec.add_left_neg _)

protected theorem UInt128.add_right_neg (a : UInt128) : a + -a = 0 := UInt128.toBitVec_inj.1 (BitVec.add_right_neg _)

@[simp] protected theorem UInt128.neg_zero : -(0 : UInt128) = 0 := (rfl)

@[simp] protected theorem UInt128.sub_add_cancel (a b : UInt128) : a - b + b = a :=
  UInt128.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)

protected theorem UInt128.eq_sub_iff_add_eq {a b c : UInt128} : a = c - b ↔ a + b = c := by
  simpa [← UInt128.toBitVec_inj] using BitVec.eq_sub_iff_add_eq

protected theorem UInt128.sub_eq_iff_eq_add {a b c : UInt128} : a - b = c ↔ a = c + b := by
  simpa [← UInt128.toBitVec_inj] using BitVec.sub_eq_iff_eq_add

@[simp] protected theorem UInt128.neg_neg {a : UInt128} : - -a = a := UInt128.toBitVec_inj.1 BitVec.neg_neg

@[simp] protected theorem UInt32.neg_inj {a b : UInt32} : -a = -b ↔ a = b := by simp [← UInt32.toBitVec_inj]
@[simp] protected theorem UInt128.neg_inj {a b : UInt128} : -a = -b ↔ a = b := by simp [← UInt128.toBitVec_inj]

@[simp] protected theorem UInt32.neg_ne_zero {a : UInt32} : -a ≠ 0 ↔ a ≠ 0 := by simp [← UInt32.toBitVec_inj]
@[simp] protected theorem UInt128.neg_ne_zero {a : UInt128} : -a ≠ 0 ↔ a ≠ 0 := by simp [← UInt128.toBitVec_inj]

protected theorem UInt128.neg_add {a b : UInt128} : - (a + b) = -a - b := UInt128.toBitVec_inj.1 BitVec.neg_add

@[simp] protected theorem UInt128.sub_neg {a b : UInt128} : a - -b = a + b := UInt128.toBitVec_inj.1 BitVec.sub_neg

@[simp] protected theorem UInt128.neg_sub {a b : UInt128} : -(a - b) = b - a := by
  rw [UInt128.sub_eq_add_neg, UInt128.neg_add, UInt128.sub_neg, UInt128.add_comm, ← UInt128.sub_eq_add_neg]

@[simp] protected theorem UInt128.ofInt_neg (x : Int) : ofInt (-x) = -ofInt x := by
  rw [Int.neg_eq_neg_one_mul, ofInt_mul, ofInt_neg_one, ← UInt128.neg_eq_neg_one_mul]

@[simp] protected theorem UInt128.add_left_inj {a b : UInt128} (c : UInt128) : (a + c = b + c) ↔ a = b := by
  simp [← UInt128.toBitVec_inj]

@[simp] protected theorem UInt128.add_right_inj {a b : UInt128} (c : UInt128) : (c + a = c + b) ↔ a = b := by
  simp [← UInt128.toBitVec_inj]

@[simp] protected theorem UInt128.sub_left_inj {a b : UInt128} (c : UInt128) : (a - c = b - c) ↔ a = b := by
  simp [← UInt128.toBitVec_inj]

@[simp] protected theorem UInt128.sub_right_inj {a b : UInt128} (c : UInt128) : (c - a = c - b) ↔ a = b := by
  simp [← UInt128.toBitVec_inj]

@[simp] theorem UInt128.add_eq_right {a b : UInt128} : a + b = b ↔ a = 0 := by
  simp [← UInt128.toBitVec_inj]

@[simp] theorem UInt128.add_eq_left {a b : UInt128} : a + b = a ↔ b = 0 := by
  simp [← UInt128.toBitVec_inj]

@[simp] theorem UInt128.right_eq_add {a b : UInt128} : b = a + b ↔ a = 0 := by
  simp [← UInt128.toBitVec_inj]

@[simp] theorem UInt128.left_eq_add {a b : UInt128} : a = a + b ↔ b = 0 := by
  simp [← UInt128.toBitVec_inj]

protected theorem UInt128.mul_comm (a b : UInt128) : a * b = b * a := UInt128.toBitVec_inj.1 (BitVec.mul_comm _ _)

instance : Std.Commutative (α := UInt128) (· * ·) := ⟨UInt128.mul_comm⟩

protected theorem UInt128.mul_assoc (a b c : UInt128) : a * b * c = a * (b * c) := UInt128.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)

instance : Std.Associative (α := UInt128) (· * ·) := ⟨UInt128.mul_assoc⟩

@[simp] theorem UInt128.mul_one (a : UInt128) : a * 1 = a := UInt128.toBitVec_inj.1 (BitVec.mul_one _)

@[simp] theorem UInt128.one_mul (a : UInt128) : 1 * a = a := UInt128.toBitVec_inj.1 (BitVec.one_mul _)

instance : Std.LawfulCommIdentity (α := UInt128) (· * ·) 1 where
  right_id := UInt128.mul_one

@[simp] theorem UInt128.mul_zero {a : UInt128} : a * 0 = 0 := UInt128.toBitVec_inj.1 BitVec.mul_zero

@[simp] theorem UInt128.zero_mul {a : UInt128} : 0 * a = 0 := UInt128.toBitVec_inj.1 BitVec.zero_mul

@[simp] protected theorem UInt128.pow_zero (x : UInt128) : x ^ 0 = 1 := (rfl)

protected theorem UInt128.pow_succ (x : UInt128) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)

@[simp, int_toBitVec] protected theorem UInt128.toBitVec_pow (a : UInt128) (n : Nat) : (a ^ n).toBitVec = a.toBitVec ^ n := by
  induction n <;> simp [*, UInt128.pow_succ, BitVec.pow_succ]

@[simp] protected theorem UInt128.ofBitVec_pow (a : BitVec 128) (n : Nat) : ofBitVec (a ^ n) = ofBitVec a ^ n := by
  induction n <;> simp [*, UInt128.pow_succ, BitVec.pow_succ]

protected theorem UInt128.mul_add {a b c : UInt128} : a * (b + c) = a * b + a * c :=
    UInt128.toBitVec_inj.1 BitVec.mul_add

protected theorem UInt128.add_mul {a b c : UInt128} : (a + b) * c = a * c + b * c := by
  rw [UInt128.mul_comm, UInt128.mul_add, UInt128.mul_comm a c, UInt128.mul_comm c b]

protected theorem UInt128.mul_succ {a b : UInt128} : a * (b + 1) = a * b + a := by simp [UInt128.mul_add]

protected theorem UInt128.succ_mul {a b : UInt128} : (a + 1) * b = a * b + b := by simp [UInt128.add_mul]

protected theorem UInt128.two_mul {a : UInt128} : 2 * a = a + a := UInt128.toBitVec_inj.1 BitVec.two_mul

protected theorem UInt128.mul_two {a : UInt128} : a * 2 = a + a := UInt128.toBitVec_inj.1 BitVec.mul_two

protected theorem UInt128.neg_mul (a b : UInt128) : -a * b = -(a * b) := UInt128.toBitVec_inj.1 (BitVec.neg_mul _ _)

protected theorem UInt128.mul_neg (a b : UInt128) : a * -b = -(a * b) := UInt128.toBitVec_inj.1 (BitVec.mul_neg _ _)

protected theorem UInt128.neg_mul_neg (a b : UInt128) : -a * -b = a * b := UInt128.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)

protected theorem UInt128.neg_mul_comm (a b : UInt128) : -a * b = a * -b := UInt128.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)

protected theorem UInt128.mul_sub {a b c : UInt128} : a * (b - c) = a * b - a * c := UInt128.toBitVec_inj.1 BitVec.mul_sub

protected theorem UInt128.sub_mul {a b c : UInt128} : (a - b) * c = a * c - b * c := by
  rw [UInt128.mul_comm, UInt128.mul_sub, UInt128.mul_comm, UInt128.mul_comm c]

theorem UInt128.neg_add_mul_eq_mul_not {a b : UInt128} : -(a + a * b) = a * ~~~b :=
  UInt128.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not

theorem UInt128.neg_mul_not_eq_add_mul {a b : UInt128} : -(a * ~~~b) = a + a * b :=
  UInt128.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul

protected theorem UInt128.le_of_lt {a b : UInt128} : a < b → a ≤ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le] using Nat.le_of_lt

protected theorem UInt128.lt_of_le_of_ne {a b : UInt128} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← UInt128.toNat_inj] using Nat.lt_of_le_of_ne

protected theorem UInt128.lt_iff_le_and_ne {a b : UInt128} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← UInt128.toNat_inj] using Nat.lt_iff_le_and_ne

@[simp] protected theorem UInt32.not_lt_zero {a : UInt32} : ¬a < 0 := by simp [UInt32.lt_iff_toBitVec_lt]
@[simp] protected theorem UInt128.not_lt_zero {a : UInt128} : ¬a < 0 := by simp [UInt128.lt_iff_toBitVec_lt]

@[simp] protected theorem UInt32.zero_le {a : UInt32} : 0 ≤ a := by simp [← UInt32.not_lt]
@[simp] protected theorem UInt128.zero_le {a : UInt128} : 0 ≤ a := by simp [← UInt128.not_lt]

@[simp] protected theorem UInt128.le_zero_iff {a : UInt128} : a ≤ 0 ↔ a = 0 := by
  simp [UInt128.le_iff_toBitVec_le, ← UInt128.toBitVec_inj]

@[simp] protected theorem UInt128.lt_one_iff {a : UInt128} : a < 1 ↔ a = 0 := by
  simp [UInt128.lt_iff_toBitVec_lt, ← UInt128.toBitVec_inj]

@[simp] protected theorem UInt128.zero_div {a : UInt128} : 0 / a = 0 := UInt128.toBitVec_inj.1 BitVec.zero_udiv

@[simp] protected theorem UInt128.div_zero {a : UInt128} : a / 0 = 0 := UInt128.toBitVec_inj.1 BitVec.udiv_zero

@[simp] protected theorem UInt128.div_one {a : UInt128} : a / 1 = a := UInt128.toBitVec_inj.1 BitVec.udiv_one

protected theorem UInt128.div_self {a : UInt128} : a / a = if a = 0 then 0 else 1 := by
  simp [← UInt128.toBitVec_inj, apply_ite]

@[simp] protected theorem UInt128.mod_zero {a : UInt128} : a % 0 = a := UInt128.toBitVec_inj.1 BitVec.umod_zero

@[simp] protected theorem UInt128.zero_mod {a : UInt128} : 0 % a = 0 := UInt128.toBitVec_inj.1 BitVec.zero_umod

@[simp] protected theorem UInt128.mod_one {a : UInt128} : a % 1 = 0 := UInt128.toBitVec_inj.1 BitVec.umod_one

@[simp] protected theorem UInt128.mod_self {a : UInt128} : a % a = 0 := UInt128.toBitVec_inj.1 BitVec.umod_self

protected theorem UInt128.pos_iff_ne_zero {a : UInt128} : 0 < a ↔ a ≠ 0 := by simp [UInt128.lt_iff_le_and_ne, Eq.comm]

protected theorem UInt128.lt_of_le_of_lt {a b c : UInt128} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_le_of_lt

protected theorem UInt128.lt_of_lt_of_le {a b c : UInt128} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_lt_of_le

protected theorem UInt128.lt_or_lt_of_ne {a b : UInt128} : a ≠ b → a < b ∨ b < a := by
  simpa [lt_iff_toNat_lt, ← UInt128.toNat_inj] using Nat.lt_or_lt_of_ne

protected theorem UInt128.lt_or_le (a b : UInt128) : a < b ∨ b ≤ a := by
  simp [lt_iff_toNat_lt, le_iff_toNat_le]; omega

protected theorem UInt128.le_or_lt (a b : UInt128) : a ≤ b ∨ b < a := (b.lt_or_le a).symm

protected theorem UInt128.le_of_eq {a b : UInt128} : a = b → a ≤ b := (· ▸ UInt128.le_rfl)

protected theorem UInt128.le_iff_lt_or_eq {a b : UInt128} : a ≤ b ↔ a < b ∨ a = b := by
  simpa [← UInt128.toNat_inj, le_iff_toNat_le, lt_iff_toNat_lt] using Nat.le_iff_lt_or_eq

protected theorem UInt128.lt_or_eq_of_le {a b : UInt128} : a ≤ b → a < b ∨ a = b := UInt128.le_iff_lt_or_eq.mp

protected theorem UInt128.sub_le {a b : UInt128} (hab : b ≤ a) : a - b ≤ a := by
  simp [le_iff_toNat_le, UInt128.toNat_sub_of_le _ _ hab]

protected theorem UInt128.sub_lt {a b : UInt128} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  rw [lt_iff_toNat_lt, UInt128.toNat_sub_of_le _ _ hab]
  refine Nat.sub_lt ?_ (UInt128.lt_iff_toNat_lt.1 hb)
  exact UInt128.lt_iff_toNat_lt.1 (UInt128.lt_of_lt_of_le hb hab)

theorem UInt128.lt_add_one {c : UInt128} (h : c ≠ -1) : c < c + 1 :=
  UInt128.lt_iff_toBitVec_lt.2 (BitVec.lt_add_one (by simpa [← UInt128.toBitVec_inj] using h))

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/SInt/Lemmas.lean
-- Target: Hax/MissingLean/Init/Data/SInt/Lemmas_Int128.lean
-- ──────────────────────────────────────────────────────────────────────

set_option maxRecDepth 4000

declare_int_theorems Int128 128

theorem Int128.toInt.inj {x y : Int128} (h : x.toInt = y.toInt) : x = y := Int128.toBitVec.inj (BitVec.eq_of_toInt_eq h)

theorem Int128.toInt_inj {x y : Int128} : x.toInt = y.toInt ↔ x = y := ⟨Int128.toInt.inj, fun h => h ▸ rfl⟩

@[simp, int_toBitVec] theorem Int128.toBitVec_neg (x : Int128) : (-x).toBitVec = -x.toBitVec := (rfl)

@[simp] theorem Int128.toBitVec_zero : toBitVec 0 = 0#128 := (rfl)

theorem Int128.toBitVec_one : (1 : Int128).toBitVec = 1#128 := (rfl)

@[simp, int_toBitVec] theorem Int128.toBitVec_ofInt (i : Int) : (ofInt i).toBitVec = BitVec.ofInt _ i := (rfl)

@[simp] protected theorem Int128.neg_zero : -(0 : Int128) = 0 := (rfl)

@[simp] theorem Int128.toInt_ofInt {n : Int} : toInt (ofInt n) = n.bmod Int128.size := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt]

@[simp] theorem Int128.toInt_ofNat' {n : Nat} : toInt (ofNat n) = (n : Int).bmod Int128.size := by
  rw [toInt, toBitVec_ofNat', BitVec.toInt_ofNat']

theorem Int128.toInt_ofNat {n : Nat} : toInt (no_index (OfNat.ofNat n)) = (n : Int).bmod Int128.size := by
  rw [toInt, toBitVec_ofNat, BitVec.toInt_ofNat]

theorem Int128.toInt_ofInt_of_le {n : Int} (hn : -2^127 ≤ n) (hn' : n < 2^127) : toInt (ofInt n) = n := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt_eq_self (by decide) hn hn']

theorem Int128.neg_ofInt {n : Int} : -ofInt n = ofInt (-n) :=
  toBitVec.inj (by simp [BitVec.ofInt_neg])

theorem Int128.ofInt_eq_ofNat {n : Nat} : ofInt n = ofNat n := toBitVec.inj (by simp)

theorem Int128.neg_ofNat {n : Nat} : -ofNat n = ofInt (-n) := by
  rw [← neg_ofInt, ofInt_eq_ofNat]

theorem Int128.toNatClampNeg_ofNat_of_lt {n : Nat} (h : n < 2 ^ 127) : toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, ← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega), Int.toNat_natCast]

theorem Int128.toInt_ofNat_of_lt {n : Nat} (h : n < 2 ^ 127) : toInt (ofNat n) = n := by
  rw [← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega)]

theorem Int128.toInt_neg_ofNat_of_le {n : Nat} (h : n ≤ 2^127) : toInt (-ofNat n) = -n := by
  rw [← ofInt_eq_ofNat, neg_ofInt, toInt_ofInt_of_le (by omega) (by omega)]

theorem Int128.toInt_zero : toInt 0 = 0 := by simp

theorem Int128.toInt_minValue : Int128.minValue.toInt = -2^127 := (rfl)

theorem Int128.toInt_maxValue : Int128.maxValue.toInt = 2 ^ 127 - 1 := (rfl)

@[simp] theorem Int128.toNatClampNeg_minValue : Int128.minValue.toNatClampNeg = 0 := (rfl)

@[simp, int_toBitVec] theorem UInt128.toBitVec_toInt128 (x : UInt128) : x.toInt128.toBitVec = x.toBitVec := (rfl)

@[simp] theorem Int128.ofBitVec_uInt128ToBitVec (x : UInt128) : Int128.ofBitVec x.toBitVec = x.toInt128 := (rfl)

@[simp] theorem UInt128.toUInt128_toInt128 (x : UInt128) : x.toInt128.toUInt128 = x := (rfl)

@[simp] theorem Int128.toNat_toInt (x : Int128) : x.toInt.toNat = x.toNatClampNeg := (rfl)

@[simp] theorem Int128.toInt_toBitVec (x : Int128) : x.toBitVec.toInt = x.toInt := (rfl)

@[simp, int_toBitVec] theorem Int8.toBitVec_toInt128 (x : Int8) : x.toInt128.toBitVec = x.toBitVec.signExtend 128 := (rfl)

@[simp, int_toBitVec] theorem Int16.toBitVec_toInt128 (x : Int16) : x.toInt128.toBitVec = x.toBitVec.signExtend 128 := (rfl)

@[simp, int_toBitVec] theorem Int32.toBitVec_toInt128 (x : Int32) : x.toInt128.toBitVec = x.toBitVec.signExtend 128 := (rfl)

@[simp, int_toBitVec] theorem Int128.toBitVec_toInt8 (x : Int128) : x.toInt8.toBitVec = x.toBitVec.signExtend 8 := (rfl)

@[simp, int_toBitVec] theorem Int128.toBitVec_toInt16 (x : Int128) : x.toInt16.toBitVec = x.toBitVec.signExtend 16 := (rfl)

@[simp, int_toBitVec] theorem Int128.toBitVec_toInt32 (x : Int128) : x.toInt32.toBitVec = x.toBitVec.signExtend 32 := (rfl)

@[simp, int_toBitVec] theorem Int128.toBitVec_toISize (x : Int128) : x.toISize.toBitVec = x.toBitVec.signExtend System.Platform.numBits := (rfl)

@[simp, int_toBitVec] theorem ISize.toBitVec_toInt128 (x : ISize) : x.toInt128.toBitVec = x.toBitVec.signExtend 128 := (rfl)

theorem Int128.toInt_lt (x : Int128) : x.toInt < 2 ^ 127 := Int.lt_of_mul_lt_mul_left BitVec.two_mul_toInt_lt (by decide)

theorem Int128.le_toInt (x : Int128) : -2 ^ 127 ≤ x.toInt := Int.le_of_mul_le_mul_left BitVec.le_two_mul_toInt (by decide)

theorem Int128.toInt_le (x : Int128) : x.toInt ≤ Int128.maxValue.toInt := Int.le_of_lt_add_one x.toInt_lt

theorem Int128.minValue_le_toInt (x : Int128) : Int128.minValue.toInt ≤ x.toInt := x.le_toInt

theorem ISize.int128MinValue_le_toInt (x : ISize) : Int128.minValue.toInt ≤ x.toInt :=
  Int.le_trans (by decide) x.le_toInt

theorem ISize.toInt_le_int128MaxValue (x : ISize) : x.toInt ≤ Int128.maxValue.toInt :=
  Int.le_of_lt_add_one x.toInt_lt

theorem Int128.toNatClampNeg_lt (x : Int128) : x.toNatClampNeg < 2 ^ 127 := (Int.toNat_lt' (by decide)).2 x.toInt_lt

@[simp] theorem Int8.toInt_toInt128 (x : Int8) : x.toInt128.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)

@[simp] theorem Int16.toInt_toInt128 (x : Int16) : x.toInt128.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)

@[simp] theorem Int32.toInt_toInt128 (x : Int32) : x.toInt128.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)

@[simp] theorem Int128.toInt_toInt8 (x : Int128) : x.toInt8.toInt = x.toInt.bmod (2 ^ 8) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)

@[simp] theorem Int128.toInt_toInt16 (x : Int128) : x.toInt16.toInt = x.toInt.bmod (2 ^ 16) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)

@[simp] theorem Int128.toInt_toInt32 (x : Int128) : x.toInt32.toInt = x.toInt.bmod (2 ^ 32) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)

@[simp] theorem Int128.toInt_toISize (x : Int128) : x.toISize.toInt = x.toInt.bmod (2 ^ System.Platform.numBits) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem ISize.toInt_toInt128 (x : ISize) : x.toInt128.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem Int8.toNatClampNeg_toInt128 (x : Int8) : x.toInt128.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt128

@[simp] theorem Int16.toNatClampNeg_toInt128 (x : Int16) : x.toInt128.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt128

@[simp] theorem Int32.toNatClampNeg_toInt128 (x : Int32) : x.toInt128.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt128

@[simp] theorem ISize.toNatClampNeg_toInt128 (x : ISize) : x.toInt128.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt128

@[simp] theorem Int128.toInt128_toUInt128 (x : Int128) : x.toUInt128.toInt128 = x := (rfl)

theorem Int128.toNat_toBitVec (x : Int128) : x.toBitVec.toNat = x.toUInt128.toNat := (rfl)

theorem Int128.toNat_toBitVec_of_le {x : Int128} (hx : 0 ≤ x) : x.toBitVec.toNat = x.toNatClampNeg :=
  (x.toBitVec.toNat_toInt_of_sle hx).symm

theorem Int128.toNat_toUInt128_of_le {x : Int128} (hx : 0 ≤ x) : x.toUInt128.toNat = x.toNatClampNeg := by
  rw [← toNat_toBitVec, toNat_toBitVec_of_le hx]

theorem Int128.toFin_toBitVec (x : Int128) : x.toBitVec.toFin = x.toUInt128.toFin := (rfl)

@[simp, int_toBitVec] theorem Int128.toBitVec_toUInt128 (x : Int128) : x.toUInt128.toBitVec = x.toBitVec := (rfl)

@[simp] theorem UInt128.ofBitVec_int128ToBitVec (x : Int128) : UInt128.ofBitVec x.toBitVec = x.toUInt128 := (rfl)

@[simp] theorem Int128.ofBitVec_toBitVec (x : Int128) : Int128.ofBitVec x.toBitVec = x := (rfl)

@[simp] theorem Int8.ofBitVec_int128ToBitVec (x : Int128) : Int8.ofBitVec (x.toBitVec.signExtend 8) = x.toInt8 := (rfl)

@[simp] theorem Int16.ofBitVec_int128ToBitVec (x : Int128) : Int16.ofBitVec (x.toBitVec.signExtend 16) = x.toInt16 := (rfl)

@[simp] theorem Int32.ofBitVec_int128ToBitVec (x : Int128) : Int32.ofBitVec (x.toBitVec.signExtend 32) = x.toInt32 := (rfl)

@[simp] theorem Int128.ofBitVec_int8ToBitVec (x : Int8) : Int128.ofBitVec (x.toBitVec.signExtend 128) = x.toInt128 := (rfl)

@[simp] theorem Int128.ofBitVec_int16ToBitVec (x : Int16) : Int128.ofBitVec (x.toBitVec.signExtend 128) = x.toInt128 := (rfl)

@[simp] theorem Int128.ofBitVec_int32ToBitVec (x : Int32) : Int128.ofBitVec (x.toBitVec.signExtend 128) = x.toInt128 := (rfl)

@[simp] theorem Int128.ofBitVec_iSizeToBitVec (x : ISize) : Int128.ofBitVec (x.toBitVec.signExtend 128) = x.toInt128 := (rfl)

@[simp] theorem ISize.ofBitVec_int128ToBitVec (x : Int128) : ISize.ofBitVec (x.toBitVec.signExtend System.Platform.numBits) = x.toISize := (rfl)

@[simp] theorem Int128.toBitVec_ofIntLE (x : Int) (h₁ h₂) : (Int128.ofIntLE x h₁ h₂).toBitVec = BitVec.ofInt 128 x := (rfl)

@[simp] theorem Int128.toInt_bmod (x : Int128) : x.toInt.bmod 340282366920938463463374607431768211456 = x.toInt := Int.bmod_eq_of_le x.le_toInt x.toInt_lt

@[simp] theorem BitVec.ofInt_int128ToInt (x : Int128) : BitVec.ofInt 128 x.toInt = x.toBitVec := BitVec.eq_of_toInt_eq (by simp)

@[simp] theorem Int128.ofIntLE_toInt (x : Int128) : Int128.ofIntLE x.toInt x.minValue_le_toInt x.toInt_le = x := Int128.toBitVec.inj (by simp)

theorem Int8.ofIntLE_int128ToInt (x : Int128) {h₁ h₂} : Int8.ofIntLE x.toInt h₁ h₂ = x.toInt8 := (rfl)

theorem Int16.ofIntLE_int128ToInt (x : Int128) {h₁ h₂} : Int16.ofIntLE x.toInt h₁ h₂ = x.toInt16 := (rfl)

theorem Int32.ofIntLE_int128ToInt (x : Int128) {h₁ h₂} : Int32.ofIntLE x.toInt h₁ h₂ = x.toInt32 := (rfl)

@[simp] theorem Int128.ofIntLE_int8ToInt (x : Int8) :
    Int128.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt128 := (rfl)

@[simp] theorem Int128.ofIntLE_int16ToInt (x : Int16) :
    Int128.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt128 := (rfl)

@[simp] theorem Int128.ofIntLE_int32ToInt (x : Int32) :
    Int128.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt128 := (rfl)

@[simp] theorem Int128.ofIntLE_iSizeToInt (x : ISize) :
    Int128.ofIntLE x.toInt x.int128MinValue_le_toInt x.toInt_le_int128MaxValue = x.toInt128 := (rfl)

theorem ISize.ofIntLE_int128ToInt (x : Int128) {h₁ h₂} : ISize.ofIntLE x.toInt h₁ h₂ = x.toISize := (rfl)

@[simp] theorem Int128.ofInt_toInt (x : Int128) : Int128.ofInt x.toInt = x := Int128.toBitVec.inj (by simp)

@[simp] theorem Int8.ofInt_int128ToInt (x : Int128) : Int8.ofInt x.toInt = x.toInt8 := (rfl)

@[simp] theorem Int16.ofInt_int128ToInt (x : Int128) : Int16.ofInt x.toInt = x.toInt16 := (rfl)

@[simp] theorem Int32.ofInt_int128ToInt (x : Int128) : Int32.ofInt x.toInt = x.toInt32 := (rfl)

@[simp] theorem Int128.ofInt_int8ToInt (x : Int8) : Int128.ofInt x.toInt = x.toInt128 := (rfl)

@[simp] theorem Int128.ofInt_int16ToInt (x : Int16) : Int128.ofInt x.toInt = x.toInt128 := (rfl)

@[simp] theorem Int128.ofInt_int32ToInt (x : Int32) : Int128.ofInt x.toInt = x.toInt128 := (rfl)

@[simp] theorem Int128.ofInt_iSizeToInt (x : ISize) : Int128.ofInt x.toInt = x.toInt128 := (rfl)

@[simp] theorem ISize.ofInt_int128ToInt (x : Int128) : ISize.ofInt x.toInt = x.toISize := (rfl)

@[simp] theorem Int128.toInt_ofIntLE {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂).toInt = x := by
  rw [ofIntLE, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]

theorem Int128.ofIntLE_eq_ofIntTruncate {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂) = ofIntTruncate x := by
  rw [ofIntTruncate, dif_pos h₁, dif_pos h₂]

theorem Int128.ofIntLE_eq_ofInt {n : Int} (h₁ h₂) : Int128.ofIntLE n h₁ h₂ = Int128.ofInt n := (rfl)

theorem Int128.toInt_ofIntTruncate {x : Int} (h₁ : Int128.minValue.toInt ≤ x)
    (h₂ : x ≤ Int128.maxValue.toInt) : (Int128.ofIntTruncate x).toInt = x := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toInt_ofIntLE]

@[simp] theorem Int128.ofIntTruncate_toInt (x : Int128) : Int128.ofIntTruncate x.toInt = x :=
  Int128.toInt.inj (toInt_ofIntTruncate x.minValue_le_toInt x.toInt_le)

@[simp] theorem Int128.ofIntTruncate_int8ToInt (x : Int8) : Int128.ofIntTruncate x.toInt = x.toInt128 :=
  Int128.toInt.inj (by
    rw [toInt_ofIntTruncate, Int8.toInt_toInt128]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))

@[simp] theorem Int128.ofIntTruncate_int16ToInt (x : Int16) : Int128.ofIntTruncate x.toInt = x.toInt128 :=
  Int128.toInt.inj (by
    rw [toInt_ofIntTruncate, Int16.toInt_toInt128]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))

@[simp] theorem Int128.ofIntTruncate_int32ToInt (x : Int32) : Int128.ofIntTruncate x.toInt = x.toInt128 :=
  Int128.toInt.inj (by
    rw [toInt_ofIntTruncate, Int32.toInt_toInt128]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))

@[simp] theorem Int128.ofIntTruncate_iSizeToInt (x : ISize) : Int128.ofIntTruncate x.toInt = x.toInt128 :=
  Int128.toInt.inj (by
    rw [toInt_ofIntTruncate, ISize.toInt_toInt128]
    · exact x.int128MinValue_le_toInt
    · exact x.toInt_le_int128MaxValue)

theorem Int128.le_iff_toInt_le {x y : Int128} : x ≤ y ↔ x.toInt ≤ y.toInt := BitVec.sle_iff_toInt_le

theorem Int128.lt_iff_toInt_lt {x y : Int128} : x < y ↔ x.toInt < y.toInt := BitVec.slt_iff_toInt_lt

theorem Int128.cast_toNatClampNeg (x : Int128) (hx : 0 ≤ x) : x.toNatClampNeg = x.toInt := by
  rw [toNatClampNeg, toInt, Int.toNat_of_nonneg (by simpa using le_iff_toInt_le.1 hx)]

theorem Int128.ofNat_toNatClampNeg (x : Int128) (hx : 0 ≤ x) : Int128.ofNat x.toNatClampNeg = x :=
  Int128.toInt.inj (by rw [Int128.toInt_ofNat_of_lt x.toNatClampNeg_lt, cast_toNatClampNeg _ hx])

theorem Int128.ofNat_int8ToNatClampNeg (x : Int8) (hx : 0 ≤ x) : Int128.ofNat x.toNatClampNeg = x.toInt128 :=
  Int128.toInt.inj (by rw [Int128.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int8.cast_toNatClampNeg _ hx, Int8.toInt_toInt128])

theorem Int128.ofNat_int16ToNatClampNeg (x : Int16) (hx : 0 ≤ x) : Int128.ofNat x.toNatClampNeg = x.toInt128 :=
  Int128.toInt.inj (by rw [Int128.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int16.cast_toNatClampNeg _ hx, Int16.toInt_toInt128])

theorem Int128.ofNat_int32ToNatClampNeg (x : Int32) (hx : 0 ≤ x) : Int128.ofNat x.toNatClampNeg = x.toInt128 :=
  Int128.toInt.inj (by rw [Int128.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int32.cast_toNatClampNeg _ hx, Int32.toInt_toInt128])

@[simp] theorem Int8.toInt8_toInt128 (n : Int8) : n.toInt128.toInt8 = n :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int8.toInt16_toInt128 (n : Int8) : n.toInt128.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int8.toInt32_toInt128 (n : Int8) : n.toInt128.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)

@[simp] theorem Int8.toInt128_toInt16 (n : Int8) : n.toInt16.toInt128 = n.toInt128 :=
  Int128.toInt.inj (by simp)

@[simp] theorem Int8.toInt128_toInt32 (n : Int8) : n.toInt32.toInt128 = n.toInt128 :=
  Int128.toInt.inj (by simp)

@[simp] theorem Int8.toInt128_toISize (n : Int8) : n.toISize.toInt128 = n.toInt128 :=
  Int128.toInt.inj (by simp)

@[simp] theorem Int8.toISize_toInt128 (n : Int8) : n.toInt128.toISize = n.toISize :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int16.toInt8_toInt128 (n : Int16) : n.toInt128.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int16.toInt16_toInt128 (n : Int16) : n.toInt128.toInt16 = n :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int16.toInt32_toInt128 (n : Int16) : n.toInt128.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)

@[simp] theorem Int16.toInt128_toInt32 (n : Int16) : n.toInt32.toInt128 = n.toInt128 :=
  Int128.toInt.inj (by simp)

@[simp] theorem Int16.toInt128_toISize (n : Int16) : n.toISize.toInt128 = n.toInt128 :=
  Int128.toInt.inj (by simp)

@[simp] theorem Int16.toISize_toInt128 (n : Int16) : n.toInt128.toISize = n.toISize :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int32.toInt8_toInt128 (n : Int32) : n.toInt128.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int32.toInt16_toInt128 (n : Int32) : n.toInt128.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int32.toInt32_toInt128 (n : Int32) : n.toInt128.toInt32 = n :=
  Int32.toInt.inj (by simp)

@[simp] theorem Int32.toInt128_toISize (n : Int32) : n.toISize.toInt128 = n.toInt128 :=
  Int128.toInt.inj (by simp)

@[simp] theorem Int32.toISize_toInt128 (n : Int32) : n.toInt128.toISize = n.toISize :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int128.toInt8_toInt16 (n : Int128) : n.toInt16.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem Int128.toInt8_toInt32 (n : Int128) : n.toInt32.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem Int128.toInt8_toISize (n : Int128) : n.toISize.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem Int128.toInt16_toInt32 (n : Int128) : n.toInt32.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem Int128.toInt16_toISize (n : Int128) : n.toISize.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem Int128.toInt32_toISize (n : Int128) : n.toISize.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem ISize.toInt8_toInt128 (n : ISize) : n.toInt128.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem ISize.toInt16_toInt128 (n : ISize) : n.toInt128.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem ISize.toInt32_toInt128 (n : ISize) : n.toInt128.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)

@[simp] theorem ISize.toISize_toInt128 (n : ISize) : n.toInt128.toISize = n :=
  ISize.toInt.inj (by simp)

theorem UInt128.toInt128_ofNatLT {n : Nat} (hn) : (UInt128.ofNatLT n hn).toInt128 = Int128.ofNat n :=
  Int128.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat])

@[simp] theorem UInt128.toInt128_ofNat' {n : Nat} : (UInt128.ofNat n).toInt128 = Int128.ofNat n := (rfl)

@[simp] theorem UInt128.toInt128_ofNat {n : Nat} : toInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := (rfl)

@[simp] theorem UInt128.toInt128_ofBitVec (b) : (UInt128.ofBitVec b).toInt128 = Int128.ofBitVec b := (rfl)

@[simp, int_toBitVec] theorem Int128.toBitVec_ofBitVec (b) : (Int128.ofBitVec b).toBitVec = b := (rfl)

theorem Int128.toBitVec_ofIntTruncate {n : Int} (h₁ : Int128.minValue.toInt ≤ n) (h₂ : n ≤ Int128.maxValue.toInt) :
    (Int128.ofIntTruncate n).toBitVec = BitVec.ofInt _ n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toBitVec_ofIntLE]

@[simp] theorem Int128.toInt_ofBitVec (b) : (Int128.ofBitVec b).toInt = b.toInt := (rfl)

@[simp] theorem Int128.toNatClampNeg_ofIntLE {n : Int} (h₁ h₂) : (Int128.ofIntLE n h₁ h₂).toNatClampNeg = n.toNat := by
  rw [ofIntLE, toNatClampNeg, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]

@[simp] theorem Int128.toNatClampNeg_ofBitVec (b) : (Int128.ofBitVec b).toNatClampNeg = b.toInt.toNat := (rfl)

theorem Int128.toNatClampNeg_ofInt_of_le {n : Int} (h₁ : -2 ^ 127 ≤ n) (h₂ : n < 2 ^ 127) :
    (Int128.ofInt n).toNatClampNeg = n.toNat := by rw [toNatClampNeg, toInt_ofInt_of_le h₁ h₂]

theorem Int128.toNatClampNeg_ofIntTruncate_of_lt {n : Int} (h₁ : n < 2 ^ 127) :
    (Int128.ofIntTruncate n).toNatClampNeg = n.toNat := by
  rw [ofIntTruncate]
  split
  · rw [dif_pos (by rw [toInt_maxValue]; omega), toNatClampNeg_ofIntLE]
  next h =>
    rw [toNatClampNeg_minValue, eq_comm, Int.toNat_eq_zero]
    rw [toInt_minValue] at h
    omega

@[simp] theorem Int128.toUInt128_ofBitVec (b) : (Int128.ofBitVec b).toUInt128 = UInt128.ofBitVec b := (rfl)

@[simp] theorem Int128.toUInt128_ofNat' {n} : (Int128.ofNat n).toUInt128 = UInt128.ofNat n := (rfl)

@[simp] theorem Int128.toUInt128_ofNat {n} : toUInt128 (OfNat.ofNat n) = OfNat.ofNat n := (rfl)

theorem Int128.toInt8_ofIntLE {n} (h₁ h₂) : (Int128.ofIntLE n h₁ h₂).toInt8 = Int8.ofInt n := Int8.toInt.inj (by simp)

@[simp] theorem Int128.toInt8_ofBitVec (b) : (Int128.ofBitVec b).toInt8 = Int8.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int128.toInt8_ofNat' {n} : (Int128.ofNat n).toInt8 = Int8.ofNat n :=
  Int8.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem Int128.toInt8_ofInt {n} : (Int128.ofInt n).toInt8 = Int8.ofInt n :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem Int128.toInt8_ofNat {n} : toInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt8_ofNat'

theorem Int128.toInt8_ofIntTruncate {n : Int} (h₁ : -2 ^ 127 ≤ n) (h₂ : n < 2 ^ 127) :
    (Int128.ofIntTruncate n).toInt8 = Int8.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt8_ofIntLE]

theorem Int128.toInt16_ofIntLE {n} (h₁ h₂) : (Int128.ofIntLE n h₁ h₂).toInt16 = Int16.ofInt n := Int16.toInt.inj (by simp)

@[simp] theorem Int128.toInt16_ofBitVec (b) : (Int128.ofBitVec b).toInt16 = Int16.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int128.toInt16_ofNat' {n} : (Int128.ofNat n).toInt16 = Int16.ofNat n :=
  Int16.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem Int128.toInt16_ofInt {n} : (Int128.ofInt n).toInt16 = Int16.ofInt n :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem Int128.toInt16_ofNat {n} : toInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt16_ofNat'

theorem Int128.toInt16_ofIntTruncate {n : Int} (h₁ : -2 ^ 127 ≤ n) (h₂ : n < 2 ^ 127) :
    (Int128.ofIntTruncate n).toInt16 = Int16.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt16_ofIntLE]

theorem Int128.toInt32_ofIntLE {n} (h₁ h₂) : (Int128.ofIntLE n h₁ h₂).toInt32 = Int32.ofInt n := Int32.toInt.inj (by simp)

@[simp] theorem Int128.toInt32_ofBitVec (b) : (Int128.ofBitVec b).toInt32 = Int32.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int128.toInt32_ofNat' {n} : (Int128.ofNat n).toInt32 = Int32.ofNat n :=
  Int32.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem Int128.toInt32_ofInt {n} : (Int128.ofInt n).toInt32 = Int32.ofInt n :=
  Int32.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem Int128.toInt32_ofNat {n} : toInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt32_ofNat'

theorem Int128.toInt32_ofIntTruncate {n : Int} (h₁ : -2 ^ 127 ≤ n) (h₂ : n < 2 ^ 127) :
    (Int128.ofIntTruncate n).toInt32 = Int32.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt32_ofIntLE]

theorem Int128.toISize_ofIntLE {n} (h₁ h₂) : (Int128.ofIntLE n h₁ h₂).toISize = ISize.ofInt n :=
  ISize.toInt.inj (by simp [ISize.toInt_ofInt])

@[simp] theorem Int128.toISize_ofBitVec (b) : (Int128.ofBitVec b).toISize = ISize.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int128.toISize_ofNat' {n} : (Int128.ofNat n).toISize = ISize.ofNat n :=
  ISize.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem Int128.toISize_ofInt {n} : (Int128.ofInt n).toISize = ISize.ofInt n :=
 ISize.toInt.inj (by simpa [ISize.toInt_ofInt] using Int.bmod_bmod_of_dvd USize.size_dvd_uInt128Size)

@[simp] theorem Int128.toISize_ofNat {n} : toISize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toISize_ofNat'

theorem Int128.toISize_ofIntTruncate {n : Int} (h₁ : -2 ^ 127 ≤ n) (h₂ : n < 2 ^ 127) :
    (Int128.ofIntTruncate n).toISize = ISize.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toISize_ofIntLE]

@[simp, int_toBitVec] theorem Int128.toBitVec_minValue : minValue.toBitVec = BitVec.intMin _ := (rfl)

@[simp, int_toBitVec] theorem Int128.toBitVec_maxValue : maxValue.toBitVec = BitVec.intMax _ := (rfl)

@[simp] theorem Int128.toInt8_neg (x : Int128) : (-x).toInt8 = -x.toInt8 := Int8.toBitVec.inj (by simp)

@[simp] theorem Int128.toInt16_neg (x : Int128) : (-x).toInt16 = -x.toInt16 := Int16.toBitVec.inj (by simp)

@[simp] theorem Int128.toInt32_neg (x : Int128) : (-x).toInt32 = -x.toInt32 := Int32.toBitVec.inj (by simp)

@[simp] theorem Int128.toISize_neg (x : Int128) : (-x).toISize = -x.toISize := ISize.toBitVec.inj (by simp)

@[simp] theorem Int8.toInt128_neg_of_ne {x : Int8} (hx : x ≠ -128) : (-x).toInt128 = -x.toInt128 :=
  Int128.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int8.toBitVec.inj h)))

@[simp] theorem Int16.toInt128_neg_of_ne {x : Int16} (hx : x ≠ -32768) : (-x).toInt128 = -x.toInt128 :=
  Int128.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int16.toBitVec.inj h)))

@[simp] theorem Int32.toInt128_neg_of_ne {x : Int32} (hx : x ≠ -2147483648) : (-x).toInt128 = -x.toInt128 :=
  Int128.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _  (fun h => hx (Int32.toBitVec.inj h)))

@[simp] theorem ISize.toInt128_neg_of_ne {x : ISize} (hx : x ≠ minValue) : (-x).toInt128 = -x.toInt128 :=
  Int128.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _
    (fun h => hx (ISize.toBitVec.inj (h.trans toBitVec_minValue.symm))))

theorem Int8.toInt128_ofIntLE {n : Int} (h₁ h₂) :
    (Int8.ofIntLE n h₁ h₂).toInt128 = Int128.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int128.toInt.inj (by simp)

@[simp] theorem Int8.toInt128_ofBitVec (b) : (Int8.ofBitVec b).toInt128 = Int128.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int8.toInt128_ofInt {n : Int} (h₁ : Int8.minValue.toInt ≤ n) (h₂ : n ≤ Int8.maxValue.toInt) :
    (Int8.ofInt n).toInt128 = Int128.ofInt n := by rw [← Int8.ofIntLE_eq_ofInt h₁ h₂, toInt128_ofIntLE, Int128.ofIntLE_eq_ofInt]

@[simp] theorem Int8.toInt128_ofNat' {n : Nat} (h : n ≤ Int8.maxValue.toInt) :
    (Int8.ofNat n).toInt128 = Int128.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt128_ofInt (by simp [toInt_minValue]) h, Int128.ofInt_eq_ofNat]

@[simp] theorem Int8.toInt128_ofNat {n : Nat} (h : n ≤ 127) :
    toInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int8.toInt128_ofNat' (by rw [toInt_maxValue]; omega)

theorem Int16.toInt128_ofIntLE {n : Int} (h₁ h₂) :
    (Int16.ofIntLE n h₁ h₂).toInt128 = Int128.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int128.toInt.inj (by simp)

@[simp] theorem Int16.toInt128_ofBitVec (b) : (Int16.ofBitVec b).toInt128 = Int128.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int16.toInt128_ofInt {n : Int} (h₁ : Int16.minValue.toInt ≤ n) (h₂ : n ≤ Int16.maxValue.toInt) :
    (Int16.ofInt n).toInt128 = Int128.ofInt n := by rw [← Int16.ofIntLE_eq_ofInt h₁ h₂, toInt128_ofIntLE, Int128.ofIntLE_eq_ofInt]

@[simp] theorem Int16.toInt128_ofNat' {n : Nat} (h : n ≤ Int16.maxValue.toInt) :
    (Int16.ofNat n).toInt128 = Int128.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt128_ofInt (by simp [toInt_minValue]) h, Int128.ofInt_eq_ofNat]

@[simp] theorem Int16.toInt128_ofNat {n : Nat} (h : n ≤ 32767) :
    toInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int16.toInt128_ofNat' (by rw [toInt_maxValue]; omega)

theorem Int32.toInt128_ofIntLE {n : Int} (h₁ h₂) :
    (Int32.ofIntLE n h₁ h₂).toInt128 = Int128.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int128.toInt.inj (by simp)

@[simp] theorem Int32.toInt128_ofBitVec (b) : (Int32.ofBitVec b).toInt128 = Int128.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int32.toInt128_ofInt {n : Int} (h₁ : Int32.minValue.toInt ≤ n) (h₂ : n ≤ Int32.maxValue.toInt) :
    (Int32.ofInt n).toInt128 = Int128.ofInt n := by rw [← Int32.ofIntLE_eq_ofInt h₁ h₂, toInt128_ofIntLE, Int128.ofIntLE_eq_ofInt]

@[simp] theorem Int32.toInt128_ofNat' {n : Nat} (h : n ≤ Int32.maxValue.toInt) :
    (Int32.ofNat n).toInt128 = Int128.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt128_ofInt (by simp [toInt_minValue]) h, Int128.ofInt_eq_ofNat]

@[simp] theorem Int32.toInt128_ofNat {n : Nat} (h : n ≤ 2147483647) :
    toInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int32.toInt128_ofNat' (by rw [toInt_maxValue]; omega)

theorem ISize.toInt128_ofIntLE {n : Int} (h₁ h₂) :
    (ISize.ofIntLE n h₁ h₂).toInt128 = Int128.ofIntLE n (Int.le_trans minValue.int128MinValue_le_toInt h₁)
      (Int.le_trans h₂ maxValue.toInt_le_int128MaxValue) :=
  Int128.toInt.inj (by simp)

@[simp] theorem ISize.toInt128_ofBitVec (b) : (ISize.ofBitVec b).toInt128 = Int128.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem ISize.toInt128_ofInt {n : Int} (h₁ : ISize.minValue.toInt ≤ n) (h₂ : n ≤ ISize.maxValue.toInt) :
    (ISize.ofInt n).toInt128 = Int128.ofInt n := by rw [← ISize.ofIntLE_eq_ofInt h₁ h₂, toInt128_ofIntLE, Int128.ofIntLE_eq_ofInt]

@[simp] theorem ISize.toInt128_ofNat' {n : Nat} (h : n ≤ ISize.maxValue.toInt) :
    (ISize.ofNat n).toInt128 = Int128.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt128_ofInt _ h, Int128.ofInt_eq_ofNat]
  refine Int.le_trans ?_ (Int.zero_le_ofNat _)
  cases System.Platform.numBits_eq <;> simp_all [ISize.toInt_minValue]

@[simp] theorem ISize.toInt128_ofNat {n : Nat} (h : n ≤ 2147483647) :
    toInt128 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  ISize.toInt128_ofNat' (by rw [toInt_maxValue]; cases System.Platform.numBits_eq <;> simp_all <;> omega)

@[simp] theorem Int128.ofIntLE_bitVecToInt (n : BitVec 128) :
    Int128.ofIntLE n.toInt (by exact n.le_toInt) (by exact n.toInt_le) = Int128.ofBitVec n :=
  Int128.toBitVec.inj (by simp)

theorem Int128.ofBitVec_ofNatLT (n : Nat) (hn) : Int128.ofBitVec (BitVec.ofNatLT n hn) = Int128.ofNat n :=
  Int128.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat hn])

@[simp] theorem Int128.ofBitVec_ofNat (n : Nat) : Int128.ofBitVec (BitVec.ofNat 128 n) = Int128.ofNat n := (rfl)

@[simp] theorem Int128.ofBitVec_ofInt (n : Int) : Int128.ofBitVec (BitVec.ofInt 128 n) = Int128.ofInt n := (rfl)

@[simp] theorem Int128.ofNat_bitVecToNat (n : BitVec 128) : Int128.ofNat n.toNat = Int128.ofBitVec n :=
  Int128.toBitVec.inj (by simp)

@[simp] theorem Int128.ofInt_bitVecToInt (n : BitVec 128) : Int128.ofInt n.toInt = Int128.ofBitVec n :=
  Int128.toBitVec.inj (by simp)

@[simp] theorem Int128.ofIntTruncate_bitVecToInt (n : BitVec 128) : Int128.ofIntTruncate n.toInt = Int128.ofBitVec n :=
  Int128.toBitVec.inj (by simp [toBitVec_ofIntTruncate (n.le_toInt) (n.toInt_le)])

@[simp] theorem Int128.toInt_neg (n : Int128) : (-n).toInt = (-n.toInt).bmod (2 ^ 128) := BitVec.toInt_neg

@[simp] theorem Int128.toNatClampNeg_eq_zero_iff {n : Int128} : n.toNatClampNeg = 0 ↔ n ≤ 0 := by
  rw [toNatClampNeg, Int.toNat_eq_zero, le_iff_toInt_le, toInt_zero]

@[simp] protected theorem Int32.not_le {n m : Int32} : ¬n ≤ m ↔ m < n := by simp [le_iff_toInt_le, lt_iff_toInt_lt]
@[simp] protected theorem Int128.not_le {n m : Int128} : ¬n ≤ m ↔ m < n := by simp [le_iff_toInt_le, lt_iff_toInt_lt]

@[simp] theorem Int128.neg_nonpos_iff (n : Int128) : -n ≤ 0 ↔ n = minValue ∨ 0 ≤ n := by
  rw [le_iff_toBitVec_sle, toBitVec_zero, toBitVec_neg, BitVec.neg_sle_zero (by decide)]
  simp [← toBitVec_inj, le_iff_toBitVec_sle, BitVec.intMin_eq_neg_two_pow]

@[simp] theorem Int32.toNatClampNeg_pos_iff (n : Int32) : 0 < n.toNatClampNeg ↔ 0 < n := by simp [Nat.pos_iff_ne_zero]
@[simp] theorem Int128.toNatClampNeg_pos_iff (n : Int128) : 0 < n.toNatClampNeg ↔ 0 < n := by simp [Nat.pos_iff_ne_zero]

@[simp] theorem Int128.toInt_div (a b : Int128) : (a / b).toInt = (a.toInt.tdiv b.toInt).bmod (2 ^ 128) := by
  rw [← toInt_toBitVec, Int128.toBitVec_div, BitVec.toInt_sdiv, toInt_toBitVec, toInt_toBitVec]

theorem Int128.toInt_div_of_ne_left (a b : Int128) (h : a ≠ minValue) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, Int128.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inl (by simpa [← toBitVec_inj] using h)

theorem Int128.toInt_div_of_ne_right (a b : Int128) (h : b ≠ -1) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, Int128.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inr (by simpa [← toBitVec_inj] using h)

theorem Int8.toInt128_ne_minValue (a : Int8) : a.toInt128 ≠ Int128.minValue :=
  have := a.le_toInt; by simp [← Int128.toInt_inj]; omega

theorem Int16.toInt128_ne_minValue (a : Int16) : a.toInt128 ≠ Int128.minValue :=
  have := a.le_toInt; by simp [← Int128.toInt_inj]; omega

theorem Int32.toInt128_ne_minValue (a : Int32) : a.toInt128 ≠ Int128.minValue :=
  have := a.le_toInt; by simp [← Int128.toInt_inj]; omega

theorem ISize.toInt128_ne_minValue (a : ISize) (ha : a ≠ minValue) : a.toInt128 ≠ Int128.minValue := by
  have := a.minValue_le_toInt
  have : -2 ^ 127 ≤ minValue.toInt := minValue.le_toInt
  simp [← Int128.toInt_inj, ← ISize.toInt_inj] at *; omega

theorem Int8.toInt128_ne_neg_one (a : Int8) (ha : a ≠ -1) : a.toInt128 ≠ -1 :=
  ne_of_apply_ne Int128.toInt8 (by simpa using ha)

theorem Int16.toInt128_ne_neg_one (a : Int16) (ha : a ≠ -1) : a.toInt128 ≠ -1 :=
  ne_of_apply_ne Int128.toInt16 (by simpa using ha)

theorem Int32.toInt128_ne_neg_one (a : Int32) (ha : a ≠ -1) : a.toInt128 ≠ -1 :=
  ne_of_apply_ne Int128.toInt32 (by simpa using ha)

theorem ISize.toInt128_ne_neg_one (a : ISize) (ha : a ≠ -1) : a.toInt128 ≠ -1 :=
  ne_of_apply_ne Int128.toISize (by simpa using ha)

theorem Int8.toInt128_div_of_ne_left (a b : Int8) (ha : a ≠ minValue) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_left _ _ ha,
    Int128.toInt_div_of_ne_left _ _ a.toInt128_ne_minValue, toInt_toInt128, toInt_toInt128])

theorem Int16.toInt128_div_of_ne_left (a b : Int16) (ha : a ≠ minValue) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_left _ _ ha,
    Int128.toInt_div_of_ne_left _ _ a.toInt128_ne_minValue, toInt_toInt128, toInt_toInt128])

theorem Int32.toInt128_div_of_ne_left (a b : Int32) (ha : a ≠ minValue) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_left _ _ ha,
    Int128.toInt_div_of_ne_left _ _ a.toInt128_ne_minValue, toInt_toInt128, toInt_toInt128])

theorem ISize.toInt128_div_of_ne_left (a b : ISize) (ha : a ≠ minValue) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_left _ _ ha,
    Int128.toInt_div_of_ne_left _ _ (a.toInt128_ne_minValue ha), toInt_toInt128, toInt_toInt128])

theorem Int8.toInt128_div_of_ne_right (a b : Int8) (hb : b ≠ -1) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_right _ _ hb,
    Int128.toInt_div_of_ne_right _ _ (b.toInt128_ne_neg_one hb), toInt_toInt128, toInt_toInt128])

theorem Int16.toInt128_div_of_ne_right (a b : Int16) (hb : b ≠ -1) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_right _ _ hb,
    Int128.toInt_div_of_ne_right _ _ (b.toInt128_ne_neg_one hb), toInt_toInt128, toInt_toInt128])

theorem Int32.toInt128_div_of_ne_right (a b : Int32) (hb : b ≠ -1) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_right _ _ hb,
    Int128.toInt_div_of_ne_right _ _ (b.toInt128_ne_neg_one hb), toInt_toInt128, toInt_toInt128])

theorem ISize.toInt128_div_of_ne_right (a b : ISize) (hb : b ≠ -1) : (a / b).toInt128 = a.toInt128 / b.toInt128 :=
  Int128.toInt_inj.1 (by rw [toInt_toInt128, toInt_div_of_ne_right _ _ hb,
    Int128.toInt_div_of_ne_right _ _ (b.toInt128_ne_neg_one hb), toInt_toInt128, toInt_toInt128])

@[simp] theorem Int128.minValue_div_neg_one : minValue / -1 = minValue := (rfl)

@[simp] theorem Int128.toInt_add (a b : Int128) : (a + b).toInt = (a.toInt + b.toInt).bmod (2 ^ 128) := by
  rw [← toInt_toBitVec, Int128.toBitVec_add, BitVec.toInt_add, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem Int128.toInt8_add (a b : Int128) : (a + b).toInt8 = a.toInt8 + b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem Int128.toInt16_add (a b : Int128) : (a + b).toInt16 = a.toInt16 + b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem Int128.toInt32_add (a b : Int128) : (a + b).toInt32 = a.toInt32 + b.toInt32 :=
  Int32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem Int128.toISize_add (a b : Int128) : (a + b).toISize = a.toISize + b.toISize :=
  ISize.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem Int128.toInt_mul (a b : Int128) : (a * b).toInt = (a.toInt * b.toInt).bmod (2 ^ 128) := by
  rw [← toInt_toBitVec, Int128.toBitVec_mul, BitVec.toInt_mul, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem Int128.toInt8_mul (a b : Int128) : (a * b).toInt8 = a.toInt8 * b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

@[simp] theorem Int128.toInt16_mul (a b : Int128) : (a * b).toInt16 = a.toInt16 * b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

@[simp] theorem Int128.toInt32_mul (a b : Int128) : (a * b).toInt32 = a.toInt32 * b.toInt32 :=
  Int32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

@[simp] theorem Int128.toISize_mul (a b : Int128) : (a * b).toISize = a.toISize * b.toISize :=
  ISize.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

protected theorem Int128.sub_eq_add_neg (a b : Int128) : a - b = a + -b := Int128.toBitVec.inj (by simp [BitVec.sub_eq_add_neg])

@[simp] theorem Int128.toInt_sub (a b : Int128) : (a - b).toInt = (a.toInt - b.toInt).bmod (2 ^ 128) := by
  simp [Int128.sub_eq_add_neg, Int.sub_eq_add_neg]

@[simp] theorem Int128.toInt8_sub (a b : Int128) : (a - b).toInt8 = a.toInt8 - b.toInt8 := by
  simp [Int128.sub_eq_add_neg, Int8.sub_eq_add_neg]

@[simp] theorem Int128.toInt16_sub (a b : Int128) : (a - b).toInt16 = a.toInt16 - b.toInt16 := by
  simp [Int128.sub_eq_add_neg, Int16.sub_eq_add_neg]

@[simp] theorem Int128.toInt32_sub (a b : Int128) : (a - b).toInt32 = a.toInt32 - b.toInt32 := by
  simp [Int128.sub_eq_add_neg, Int32.sub_eq_add_neg]

@[simp] theorem Int128.toISize_sub (a b : Int128) : (a - b).toISize = a.toISize - b.toISize := by
  simp [Int128.sub_eq_add_neg, ISize.sub_eq_add_neg]

@[simp] theorem Int8.toInt128_lt {a b : Int8} : a.toInt128 < b.toInt128 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int128.lt_iff_toInt_lt]

@[simp] theorem Int16.toInt128_lt {a b : Int16} : a.toInt128 < b.toInt128 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int128.lt_iff_toInt_lt]

@[simp] theorem Int32.toInt128_lt {a b : Int32} : a.toInt128 < b.toInt128 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int128.lt_iff_toInt_lt]

@[simp] theorem ISize.toInt128_lt {a b : ISize} : a.toInt128 < b.toInt128 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int128.lt_iff_toInt_lt]

@[simp] theorem Int8.toInt128_le {a b : Int8} : a.toInt128 ≤ b.toInt128 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int128.le_iff_toInt_le]

@[simp] theorem Int16.toInt128_le {a b : Int16} : a.toInt128 ≤ b.toInt128 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int128.le_iff_toInt_le]

@[simp] theorem Int32.toInt128_le {a b : Int32} : a.toInt128 ≤ b.toInt128 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int128.le_iff_toInt_le]

@[simp] theorem ISize.toInt128_le {a b : ISize} : a.toInt128 ≤ b.toInt128 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int128.le_iff_toInt_le]

@[simp] theorem Int128.ofBitVec_neg (a : BitVec 128) : Int128.ofBitVec (-a) = -Int128.ofBitVec a := (rfl)

@[simp] theorem Int128.ofInt_neg (a : Int) : Int128.ofInt (-a) = -Int128.ofInt a := Int128.toInt_inj.1 (by simp)

theorem Int128.ofInt_eq_iff_bmod_eq_toInt (a : Int) (b : Int128) : Int128.ofInt a = b ↔ a.bmod (2 ^ 128) = b.toInt := by
  simp [← Int128.toInt_inj]

@[simp] theorem Int128.ofBitVec_add (a b : BitVec 128) : Int128.ofBitVec (a + b) = Int128.ofBitVec a + Int128.ofBitVec b := (rfl)

@[simp] theorem Int128.ofInt_add (a b : Int) : Int128.ofInt (a + b) = Int128.ofInt a + Int128.ofInt b := by
  simp [Int128.ofInt_eq_iff_bmod_eq_toInt]

@[simp] theorem Int128.ofNat_add (a b : Nat) : Int128.ofNat (a + b) = Int128.ofNat a + Int128.ofNat b := by
  simp [← Int128.ofInt_eq_ofNat]

theorem Int128.ofIntLE_add {a b : Int} {hab₁ hab₂} : Int128.ofIntLE (a + b) hab₁ hab₂ = Int128.ofInt a + Int128.ofInt b := by
  simp [Int128.ofIntLE_eq_ofInt]

@[simp] theorem Int128.ofBitVec_sub (a b : BitVec 128) : Int128.ofBitVec (a - b) = Int128.ofBitVec a - Int128.ofBitVec b := (rfl)

@[simp] theorem Int128.ofInt_sub (a b : Int) : Int128.ofInt (a - b) = Int128.ofInt a - Int128.ofInt b := by
  simp [Int128.ofInt_eq_iff_bmod_eq_toInt]

@[simp] theorem Int128.ofNat_sub (a b : Nat) (hab : b ≤ a) : Int128.ofNat (a - b) = Int128.ofNat a - Int128.ofNat b := by
  simp [← Int128.ofInt_eq_ofNat, Int.ofNat_sub hab]

theorem Int128.ofIntLE_sub {a b : Int} {hab₁ hab₂} : Int128.ofIntLE (a - b) hab₁ hab₂ = Int128.ofInt a - Int128.ofInt b := by
  simp [Int128.ofIntLE_eq_ofInt]

@[simp] theorem Int128.ofBitVec_mul (a b : BitVec 128) : Int128.ofBitVec (a * b) = Int128.ofBitVec a * Int128.ofBitVec b := (rfl)

@[simp] theorem Int128.ofInt_mul (a b : Int) : Int128.ofInt (a * b) = Int128.ofInt a * Int128.ofInt b := by
  simp [Int128.ofInt_eq_iff_bmod_eq_toInt]

@[simp] theorem Int128.ofNat_mul (a b : Nat) : Int128.ofNat (a * b) = Int128.ofNat a * Int128.ofNat b := by
  simp [← Int128.ofInt_eq_ofNat]

theorem Int128.ofIntLE_mul {a b : Int} {hab₁ hab₂} : Int128.ofIntLE (a * b) hab₁ hab₂ = Int128.ofInt a * Int128.ofInt b := by
  simp [Int128.ofIntLE_eq_ofInt]

theorem Int128.toInt_minValue_lt_zero : minValue.toInt < 0 := by decide

theorem Int128.toInt_maxValue_add_one : maxValue.toInt + 1 = 2 ^ 127 := (rfl)

@[simp] theorem Int128.ofBitVec_sdiv (a b : BitVec 128) : Int128.ofBitVec (a.sdiv b) = Int128.ofBitVec a / Int128.ofBitVec b := (rfl)

theorem Int128.ofInt_tdiv {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int128.ofInt (a.tdiv b) = Int128.ofInt a / Int128.ofInt b := by
  rw [Int128.ofInt_eq_iff_bmod_eq_toInt, toInt_div, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂

theorem Int128.ofInt_eq_ofIntLE_div {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int128.ofInt (a.tdiv b) = Int128.ofIntLE a ha₁ ha₂ / Int128.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tdiv ha₁ ha₂ hb₁ hb₂]

theorem Int128.ofNat_div {a b : Nat} (ha : a < 2 ^ 127) (hb : b < 2 ^ 127) :
    Int128.ofNat (a / b) = Int128.ofNat a / Int128.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tdiv,
    ofInt_tdiv (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)

@[simp] theorem Int128.ofBitVec_srem (a b : BitVec 128) : Int128.ofBitVec (a.srem b) = Int128.ofBitVec a % Int128.ofBitVec b := (rfl)

@[simp] theorem Int128.toInt_bmod_size (a : Int128) : a.toInt.bmod size = a.toInt := BitVec.toInt_bmod_cancel _

theorem Int128.ofIntLE_le_iff_le {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int128.ofIntLE a ha₁ ha₂ ≤ Int128.ofIntLE b hb₁ hb₂ ↔ a ≤ b := by simp [le_iff_toInt_le]

theorem Int128.ofInt_le_iff_le {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int128.ofInt a ≤ Int128.ofInt b ↔ a ≤ b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_le_iff_le]

theorem Int128.ofNat_le_iff_le {a b : Nat} (ha : a < 2 ^ 127) (hb : b < 2 ^ 127) :
    Int128.ofNat a ≤ Int128.ofNat b ↔ a ≤ b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_le_iff_le (by simp) _ (by simp), Int.ofNat_le]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)

theorem Int128.ofBitVec_le_iff_sle (a b : BitVec 128) : Int128.ofBitVec a ≤ Int128.ofBitVec b ↔ a.sle b := Iff.rfl

theorem Int128.ofIntLE_lt_iff_lt {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int128.ofIntLE a ha₁ ha₂ < Int128.ofIntLE b hb₁ hb₂ ↔ a < b := by simp [lt_iff_toInt_lt]

theorem Int128.ofInt_lt_iff_lt {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int128.ofInt a < Int128.ofInt b ↔ a < b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_lt_iff_lt]

theorem Int128.ofNat_lt_iff_lt {a b : Nat} (ha : a < 2 ^ 127) (hb : b < 2 ^ 127) :
    Int128.ofNat a < Int128.ofNat b ↔ a < b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_lt_iff_lt (by simp) _ (by simp), Int.ofNat_lt]
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 ha)

theorem Int128.ofBitVec_lt_iff_slt (a b : BitVec 128) : Int128.ofBitVec a < Int128.ofBitVec b ↔ a.slt b := Iff.rfl

theorem Int128.toNatClampNeg_one : (1 : Int128).toNatClampNeg = 1 := (rfl)

theorem Int128.toInt_one : (1 : Int128).toInt = 1 := (rfl)

theorem Int128.zero_lt_one : (0 : Int128) < 1 := by simp

theorem Int128.zero_ne_one : (0 : Int128) ≠ 1 := by simp

protected theorem Int128.add_assoc (a b c : Int128) : a + b + c = a + (b + c) :=
  Int128.toBitVec_inj.1 (BitVec.add_assoc _ _ _)

instance : Std.Associative (α := Int128) (· + ·) := ⟨Int128.add_assoc⟩

protected theorem Int128.add_comm (a b : Int128) : a + b = b + a := Int128.toBitVec_inj.1 (BitVec.add_comm _ _)

instance : Std.Commutative (α := Int128) (· + ·) := ⟨Int128.add_comm⟩

@[simp] protected theorem Int128.add_zero (a : Int128) : a + 0 = a := Int128.toBitVec_inj.1 (BitVec.add_zero _)

@[simp] protected theorem Int128.zero_add (a : Int128) : 0 + a = a := Int128.toBitVec_inj.1 (BitVec.zero_add _)

instance : Std.LawfulIdentity (α := Int128) (· + ·) 0 where
  left_id := Int128.zero_add
  right_id := Int128.add_zero

@[simp] protected theorem Int128.sub_zero (a : Int128) : a - 0 = a := Int128.toBitVec_inj.1 (BitVec.sub_zero _)

@[simp] protected theorem Int128.zero_sub (a : Int128) : 0 - a = -a := Int128.toBitVec_inj.1 (BitVec.zero_sub _)

@[simp] protected theorem Int128.sub_self (a : Int128) : a - a = 0 := Int128.toBitVec_inj.1 (BitVec.sub_self _)

protected theorem Int128.add_left_neg (a : Int128) : -a + a = 0 := Int128.toBitVec_inj.1 (BitVec.add_left_neg _)

protected theorem Int128.add_right_neg (a : Int128) : a + -a = 0 := Int128.toBitVec_inj.1 (BitVec.add_right_neg _)

@[simp] protected theorem Int128.sub_add_cancel (a b : Int128) : a - b + b = a :=
  Int128.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)

protected theorem Int128.eq_sub_iff_add_eq {a b c : Int128} : a = c - b ↔ a + b = c := by
  simpa [← Int128.toBitVec_inj] using BitVec.eq_sub_iff_add_eq

protected theorem Int128.sub_eq_iff_eq_add {a b c : Int128} : a - b = c ↔ a = c + b := by
  simpa [← Int128.toBitVec_inj] using BitVec.sub_eq_iff_eq_add

@[simp] protected theorem Int128.neg_neg {a : Int128} : - -a = a := Int128.toBitVec_inj.1 BitVec.neg_neg

@[simp] protected theorem Int32.neg_inj {a b : Int32} : -a = -b ↔ a = b := by simp [← Int32.toBitVec_inj]
@[simp] protected theorem Int128.neg_inj {a b : Int128} : -a = -b ↔ a = b := by simp [← Int128.toBitVec_inj]

@[simp] protected theorem Int32.neg_ne_zero {a : Int32} : -a ≠ 0 ↔ a ≠ 0 := by simp [← Int32.toBitVec_inj]
@[simp] protected theorem Int128.neg_ne_zero {a : Int128} : -a ≠ 0 ↔ a ≠ 0 := by simp [← Int128.toBitVec_inj]

protected theorem Int128.neg_add {a b : Int128} : - (a + b) = -a - b := Int128.toBitVec_inj.1 BitVec.neg_add

@[simp] protected theorem Int128.sub_neg {a b : Int128} : a - -b = a + b := Int128.toBitVec_inj.1 BitVec.sub_neg

@[simp] protected theorem Int128.neg_sub {a b : Int128} : -(a - b) = b - a := by
  rw [Int128.sub_eq_add_neg, Int128.neg_add, Int128.sub_neg, Int128.add_comm, ← Int128.sub_eq_add_neg]

protected theorem Int128.sub_sub (a b c : Int128) : a - b - c = a - (b + c) := by
  simp [Int128.sub_eq_add_neg, Int128.add_assoc, Int128.neg_add]

@[simp] protected theorem Int128.add_left_inj {a b : Int128} (c : Int128) : (a + c = b + c) ↔ a = b := by
  simp [← Int128.toBitVec_inj]

@[simp] protected theorem Int128.add_right_inj {a b : Int128} (c : Int128) : (c + a = c + b) ↔ a = b := by
  simp [← Int128.toBitVec_inj]

@[simp] protected theorem Int128.sub_left_inj {a b : Int128} (c : Int128) : (a - c = b - c) ↔ a = b := by
  simp [← Int128.toBitVec_inj]

@[simp] protected theorem Int128.sub_right_inj {a b : Int128} (c : Int128) : (c - a = c - b) ↔ a = b := by
  simp [← Int128.toBitVec_inj]

@[simp] theorem Int128.add_eq_right {a b : Int128} : a + b = b ↔ a = 0 := by
  simp [← Int128.toBitVec_inj]

@[simp] theorem Int128.add_eq_left {a b : Int128} : a + b = a ↔ b = 0 := by
  simp [← Int128.toBitVec_inj]

@[simp] theorem Int128.right_eq_add {a b : Int128} : b = a + b ↔ a = 0 := by
  simp [← Int128.toBitVec_inj]

@[simp] theorem Int128.left_eq_add {a b : Int128} : a = a + b ↔ b = 0 := by
  simp [← Int128.toBitVec_inj]

protected theorem Int128.mul_comm (a b : Int128) : a * b = b * a := Int128.toBitVec_inj.1 (BitVec.mul_comm _ _)

instance : Std.Commutative (α := Int128) (· * ·) := ⟨Int128.mul_comm⟩

protected theorem Int128.mul_assoc (a b c : Int128) : a * b * c = a * (b * c) := Int128.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)

instance : Std.Associative (α := Int128) (· * ·) := ⟨Int128.mul_assoc⟩

@[simp] theorem Int128.mul_one (a : Int128) : a * 1 = a := Int128.toBitVec_inj.1 (BitVec.mul_one _)

@[simp] theorem Int128.one_mul (a : Int128) : 1 * a = a := Int128.toBitVec_inj.1 (BitVec.one_mul _)

instance : Std.LawfulCommIdentity (α := Int128) (· * ·) 1 where
  right_id := Int128.mul_one

@[simp] theorem Int128.mul_zero {a : Int128} : a * 0 = 0 := Int128.toBitVec_inj.1 BitVec.mul_zero

@[simp] theorem Int128.zero_mul {a : Int128} : 0 * a = 0 := Int128.toBitVec_inj.1 BitVec.zero_mul

@[simp] protected theorem Int128.pow_zero (x : Int128) : x ^ 0 = 1 := (rfl)

protected theorem Int128.pow_succ (x : Int128) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)

protected theorem Int128.mul_add {a b c : Int128} : a * (b + c) = a * b + a * c :=
    Int128.toBitVec_inj.1 BitVec.mul_add

protected theorem Int128.add_mul {a b c : Int128} : (a + b) * c = a * c + b * c := by
  rw [Int128.mul_comm, Int128.mul_add, Int128.mul_comm a c, Int128.mul_comm c b]

protected theorem Int128.mul_succ {a b : Int128} : a * (b + 1) = a * b + a := by simp [Int128.mul_add]

protected theorem Int128.succ_mul {a b : Int128} : (a + 1) * b = a * b + b := by simp [Int128.add_mul]

protected theorem Int128.two_mul {a : Int128} : 2 * a = a + a := Int128.toBitVec_inj.1 BitVec.two_mul

protected theorem Int128.mul_two {a : Int128} : a * 2 = a + a := Int128.toBitVec_inj.1 BitVec.mul_two

protected theorem Int128.neg_mul (a b : Int128) : -a * b = -(a * b) := Int128.toBitVec_inj.1 (BitVec.neg_mul _ _)

protected theorem Int128.mul_neg (a b : Int128) : a * -b = -(a * b) := Int128.toBitVec_inj.1 (BitVec.mul_neg _ _)

protected theorem Int128.neg_mul_neg (a b : Int128) : -a * -b = a * b := Int128.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)

protected theorem Int128.neg_mul_comm (a b : Int128) : -a * b = a * -b := Int128.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)

protected theorem Int128.mul_sub {a b c : Int128} : a * (b - c) = a * b - a * c := Int128.toBitVec_inj.1 BitVec.mul_sub

protected theorem Int128.sub_mul {a b c : Int128} : (a - b) * c = a * c - b * c := by
  rw [Int128.mul_comm, Int128.mul_sub, Int128.mul_comm, Int128.mul_comm c]

theorem Int128.neg_add_mul_eq_mul_not {a b : Int128} : -(a + a * b) = a * ~~~b :=
  Int128.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not

theorem Int128.neg_mul_not_eq_add_mul {a b : Int128} : -(a * ~~~b) = a + a * b :=
  Int128.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul

protected theorem Int128.le_of_lt {a b : Int128} : a < b → a ≤ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le] using Int.le_of_lt

protected theorem Int128.lt_of_le_of_ne {a b : Int128} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← Int128.toInt_inj] using (Int.lt_iff_le_and_ne.2 ⟨·, ·⟩)

protected theorem Int128.lt_iff_le_and_ne {a b : Int128} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← Int128.toInt_inj] using Int.lt_iff_le_and_ne

@[simp] protected theorem Int32.lt_irrefl {a : Int32} : ¬a < a := by simp [lt_iff_toInt_lt]
@[simp] protected theorem Int128.lt_irrefl {a : Int128} : ¬a < a := by simp [lt_iff_toInt_lt]

protected theorem Int128.lt_of_le_of_lt {a b c : Int128} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_le_of_lt

protected theorem Int128.lt_of_lt_of_le {a b c : Int128} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_lt_of_le

@[simp] theorem Int128.minValue_le (a : Int128) : minValue ≤ a := by simpa [le_iff_toInt_le] using a.minValue_le_toInt

@[simp] theorem Int128.le_maxValue (a : Int128) : a ≤ maxValue := by simpa [le_iff_toInt_le] using a.toInt_le

@[simp] theorem Int128.not_lt_minValue {a : Int128} : ¬a < minValue :=
  fun h => Int128.lt_irrefl (Int128.lt_of_le_of_lt a.minValue_le h)

@[simp] theorem Int128.not_maxValue_lt {a : Int128} : ¬maxValue < a :=
  fun h => Int128.lt_irrefl (Int128.lt_of_lt_of_le h a.le_maxValue)

@[simp] protected theorem Int32.le_refl (a : Int32) : a ≤ a := by simp [Int32.le_iff_toInt_le]
@[simp] protected theorem Int128.le_refl (a : Int128) : a ≤ a := by simp [Int128.le_iff_toInt_le]

protected theorem Int128.le_rfl {a : Int128} : a ≤ a := Int128.le_refl _

protected theorem Int128.le_antisymm_iff {a b : Int128} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨by rintro rfl; simp, by simpa [← Int128.toInt_inj, le_iff_toInt_le] using Int.le_antisymm⟩

protected theorem Int128.le_antisymm {a b : Int128} : a ≤ b → b ≤ a → a = b := by simpa using Int128.le_antisymm_iff.2

@[simp] theorem Int128.le_minValue_iff {a : Int128} : a ≤ minValue ↔ a = minValue :=
  ⟨fun h => Int128.le_antisymm h a.minValue_le, by rintro rfl; simp⟩

@[simp] theorem Int128.maxValue_le_iff {a : Int128} : maxValue ≤ a ↔ a = maxValue :=
  ⟨fun h => Int128.le_antisymm a.le_maxValue h, by rintro rfl; simp⟩

@[simp] protected theorem Int128.zero_div {a : Int128} : 0 / a = 0 := Int128.toBitVec_inj.1 BitVec.zero_sdiv

@[simp] protected theorem Int128.div_zero {a : Int128} : a / 0 = 0 := Int128.toBitVec_inj.1 BitVec.sdiv_zero

@[simp] protected theorem Int128.div_one {a : Int128} : a / 1 = a := Int128.toBitVec_inj.1 BitVec.sdiv_one

protected theorem Int128.div_self {a : Int128} : a / a = if a = 0 then 0 else 1 := by
  simp [← Int128.toBitVec_inj, apply_ite]

@[simp] protected theorem Int128.mod_zero {a : Int128} : a % 0 = a := Int128.toBitVec_inj.1 BitVec.srem_zero

@[simp] protected theorem Int128.zero_mod {a : Int128} : 0 % a = 0 := Int128.toBitVec_inj.1 BitVec.zero_srem

@[simp] protected theorem Int128.mod_one {a : Int128} : a % 1 = 0 := Int128.toBitVec_inj.1 BitVec.srem_one

@[simp] protected theorem Int128.mod_self {a : Int128} : a % a = 0 := Int128.toBitVec_inj.1 BitVec.srem_self

@[simp] protected theorem Int128.not_lt {a b : Int128} : ¬ a < b ↔ b ≤ a := by
  simp [lt_iff_toBitVec_slt, le_iff_toBitVec_sle, BitVec.sle_eq_not_slt]

protected theorem Int128.le_trans {a b c : Int128} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [le_iff_toInt_le] using Int.le_trans

protected theorem Int128.lt_trans {a b c : Int128} : a < b → b < c → a < c := by
  simpa [lt_iff_toInt_lt] using Int.lt_trans

protected theorem Int128.le_total (a b : Int128) : a ≤ b ∨ b ≤ a := by
  simpa [le_iff_toInt_le] using Int.le_total _ _

protected theorem Int128.lt_asymm {a b : Int128} : a < b → ¬b < a :=
  fun hab hba => Int128.lt_irrefl (Int128.lt_trans hab hba)

instance Int128.instIsLinearOrder : IsLinearOrder Int128 := by
  apply IsLinearOrder.of_le
  case le_antisymm => constructor; apply Int128.le_antisymm
  case le_total => constructor; apply Int128.le_total
  case le_trans => constructor; apply Int128.le_trans

instance : LawfulOrderLT Int128 where
  lt_iff := by
    simp [← Int128.not_le, Decidable.imp_iff_not_or, Std.Total.total]

protected theorem Int128.add_neg_eq_sub {a b : Int128} : a + -b = a - b := Int128.toBitVec_inj.1 BitVec.add_neg_eq_sub

theorem Int128.neg_eq_neg_one_mul (a : Int128) : -a = -1 * a := Int128.toInt_inj.1 (by simp)

@[simp] protected theorem Int128.add_sub_cancel (a b : Int128) : a + b - b = a := Int128.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)

protected theorem Int128.lt_or_lt_of_ne {a b : Int128} : a ≠ b → a < b ∨ b < a := by
  simp [lt_iff_toInt_lt, ← Int128.toInt_inj]; omega

protected theorem Int128.lt_or_le (a b : Int128) : a < b ∨ b ≤ a := by
  simp [lt_iff_toInt_lt, le_iff_toInt_le]; omega

protected theorem Int128.le_or_lt (a b : Int128) : a ≤ b ∨ b < a := (b.lt_or_le a).symm

protected theorem Int128.le_of_eq {a b : Int128} : a = b → a ≤ b := (· ▸ Int128.le_rfl)

protected theorem Int128.le_iff_lt_or_eq {a b : Int128} : a ≤ b ↔ a < b ∨ a = b := by
  simp [← Int128.toInt_inj, le_iff_toInt_le, lt_iff_toInt_lt]; omega

protected theorem Int128.lt_or_eq_of_le {a b : Int128} : a ≤ b → a < b ∨ a = b := Int128.le_iff_lt_or_eq.mp

theorem Int128.toInt_eq_toNatClampNeg {a : Int128} (ha : 0 ≤ a) : a.toInt = a.toNatClampNeg := by
  simpa only [← toNat_toInt, Int.eq_natCast_toNat, le_iff_toInt_le] using ha

@[simp] theorem UInt128.toInt128_add (a b : UInt128) : (a + b).toInt128 = a.toInt128 + b.toInt128 := (rfl)

@[simp] theorem UInt128.toInt128_neg (a : UInt128) : (-a).toInt128 = -a.toInt128 := (rfl)

@[simp] theorem UInt128.toInt128_sub (a b : UInt128) : (a - b).toInt128 = a.toInt128 - b.toInt128 := (rfl)

@[simp] theorem UInt128.toInt128_mul (a b : UInt128) : (a * b).toInt128 = a.toInt128 * b.toInt128 := (rfl)

@[simp] theorem Int128.toUInt128_add (a b : Int128) : (a + b).toUInt128 = a.toUInt128 + b.toUInt128 := (rfl)

@[simp] theorem Int128.toUInt128_neg (a : Int128) : (-a).toUInt128 = -a.toUInt128 := (rfl)

@[simp] theorem Int128.toUInt128_sub (a b : Int128) : (a - b).toUInt128 = a.toUInt128 - b.toUInt128 := (rfl)

@[simp] theorem Int128.toUInt128_mul (a b : Int128) : (a * b).toUInt128 = a.toUInt128 * b.toUInt128 := (rfl)

theorem Int128.toNatClampNeg_le {a b : Int128} (hab : a ≤ b) : a.toNatClampNeg ≤ b.toNatClampNeg := by
  rw [← Int128.toNat_toInt, ← Int128.toNat_toInt]
  exact Int.toNat_le_toNat (Int128.le_iff_toInt_le.1 hab)

theorem Int128.toUInt128_le {a b : Int128} (ha : 0 ≤ a) (hab : a ≤ b) : a.toUInt128 ≤ b.toUInt128 := by
  rw [UInt128.le_iff_toNat_le, toNat_toUInt128_of_le ha, toNat_toUInt128_of_le (Int128.le_trans ha hab)]
  exact Int128.toNatClampNeg_le hab

theorem Int128.zero_le_ofNat_of_lt {a : Nat} (ha : a < 2 ^ 127) : 0 ≤ Int128.ofNat a := by
  rw [le_iff_toInt_le, toInt_ofNat_of_lt ha, Int128.toInt_zero]
  exact Int.natCast_nonneg _

protected theorem Int128.sub_nonneg_of_le {a b : Int128} (hb : 0 ≤ b) (hab : b ≤ a) : 0 ≤ a - b := by
  rw [← ofNat_toNatClampNeg _ hb, ← ofNat_toNatClampNeg _ (Int128.le_trans hb hab),
    ← ofNat_sub _ _ (Int128.toNatClampNeg_le hab)]
  exact Int128.zero_le_ofNat_of_lt (Nat.sub_lt_of_lt a.toNatClampNeg_lt)

theorem Int128.toNatClampNeg_sub_of_le {a b : Int128} (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b).toNatClampNeg = a.toNatClampNeg - b.toNatClampNeg := by
  rw [← toNat_toUInt128_of_le (Int128.sub_nonneg_of_le hb hab), toUInt128_sub,
    UInt128.toNat_sub_of_le _ _ (Int128.toUInt128_le hb hab),
    ← toNat_toUInt128_of_le (Int128.le_trans hb hab), ← toNat_toUInt128_of_le hb]

theorem Int128.toInt_sub_of_le (a b : Int128) (hb : 0 ≤ b) (h : b ≤ a) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int128.toInt_eq_toNatClampNeg (Int128.sub_nonneg_of_le hb h),
    Int128.toInt_eq_toNatClampNeg (Int128.le_trans hb h), Int128.toInt_eq_toNatClampNeg hb,
    Int128.toNatClampNeg_sub_of_le hb h, Int.ofNat_sub]
  exact Int128.toNatClampNeg_le h

protected theorem Int128.sub_le {a b : Int128} (hb : 0 ≤ b) (hab : b ≤ a) : a - b ≤ a := by
  simp_all [le_iff_toInt_le, Int128.toInt_sub_of_le _ _ hb hab]; omega

protected theorem Int128.sub_lt {a b : Int128} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  simp_all [lt_iff_toInt_lt, Int128.toInt_sub_of_le _ _ (Int128.le_of_lt hb) hab]; omega

protected theorem Int128.ne_of_lt {a b : Int128} : a < b → a ≠ b := by
  simpa [Int128.lt_iff_toInt_lt, ← Int128.toInt_inj] using Int.ne_of_lt

@[simp] theorem Int128.toInt_mod (a b : Int128) : (a % b).toInt = a.toInt.tmod b.toInt := by
  rw [← toInt_toBitVec, Int128.toBitVec_mod, BitVec.toInt_srem, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem Int8.toInt128_mod (a b : Int8) : (a % b).toInt128 = a.toInt128 % b.toInt128 := Int128.toInt.inj (by simp)

@[simp] theorem Int16.toInt128_mod (a b : Int16) : (a % b).toInt128 = a.toInt128 % b.toInt128 := Int128.toInt.inj (by simp)

@[simp] theorem Int32.toInt128_mod (a b : Int32) : (a % b).toInt128 = a.toInt128 % b.toInt128 := Int128.toInt.inj (by simp)

@[simp] theorem ISize.toInt128_mod (a b : ISize) : (a % b).toInt128 = a.toInt128 % b.toInt128 := Int128.toInt.inj (by simp)

theorem Int128.ofInt_tmod {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int128.ofInt (a.tmod b) = Int128.ofInt a % Int128.ofInt b := by
  rw [Int128.ofInt_eq_iff_bmod_eq_toInt, ← toInt_bmod_size, toInt_mod, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂

theorem Int128.ofInt_eq_ofIntLE_mod {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int128.ofInt (a.tmod b) = Int128.ofIntLE a ha₁ ha₂ % Int128.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tmod ha₁ ha₂ hb₁ hb₂]

theorem Int128.ofNat_mod {a b : Nat} (ha : a < 2 ^ 127) (hb : b < 2 ^ 127) :
    Int128.ofNat (a % b) = Int128.ofNat a % Int128.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tmod,
    ofInt_tmod (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/GrindInstances/ToInt.lean
-- Target: Hax/MissingLean/Init/GrindInstances/ToInt.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean.Grind

instance : ToInt UInt128 (.uint 128) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := private UInt128.toNat_inj.mp (Int.ofNat_inj.mp w)
  toInt_mem x := by simpa using Int.lt_toNat.mp (UInt128.toNat_lt x)

@[simp] theorem toInt_uint128 (x : UInt128) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Zero UInt128 (.uint 128) where
  toInt_zero := by simp

instance : ToInt.OfNat UInt128 (.uint 128) where
  toInt_ofNat x := by simp; rfl

instance : ToInt.Add UInt128 (.uint 128) where
  toInt_add x y := by simp

instance : ToInt.Mul UInt128 (.uint 128) where
  toInt_mul x y := by simp

instance : ToInt.Mod UInt128 (.uint 128) where
  toInt_mod x y := by simp

instance : ToInt.Div UInt128 (.uint 128) where
  toInt_div x y := by simp

instance : ToInt.LE UInt128 (.uint 128) where
  le_iff x y := by simpa using UInt128.le_iff_toBitVec_le

instance : ToInt.LT UInt128 (.uint 128) where
  lt_iff x y := by simpa using UInt128.lt_iff_toBitVec_lt

instance : ToInt Int128 (.sint 128) where
  toInt x := x.toInt
  toInt_inj x y w := private Int128.toInt_inj.mp w
  toInt_mem x := by simp; exact ⟨Int128.le_toInt x, Int128.toInt_lt x⟩

@[simp] theorem toInt_int128 (x : Int128) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Zero Int128 (.sint 128) where
  toInt_zero := by
    -- simp -- FIXME: succeeds, but generates a `(kernel) application type mismatch` error!
    change (0 : Int128).toInt = _
    rw [Int128.toInt_zero]

instance : ToInt.OfNat Int128 (.sint 128) where
  toInt_ofNat x := by
    rw [toInt_int128, Int128.toInt_ofNat, Int128.size, Int.bmod_eq_emod, IntInterval.wrap]
    simp
    split <;> omega

instance : ToInt.Add Int128 (.sint 128) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.Mul Int128 (.sint 128) where
  toInt_mul x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.LE Int128 (.sint 128) where
  le_iff x y := by simpa using Int128.le_iff_toInt_le

instance : ToInt.LT Int128 (.sint 128) where
  lt_iff x y := by simpa using Int128.lt_iff_toInt_lt

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/GrindInstances/Ring/SInt.lean
-- Target: Hax/MissingLean/Init/GrindInstances/Ring/SInt.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean Grind

@[expose, instance_reducible]
def Int128.natCast : NatCast Int128 where
  natCast x := Int128.ofNat x

@[expose, instance_reducible]
def Int128.intCast : IntCast Int128 where
  intCast x := Int128.ofInt x

attribute [local instance] Int128.intCast in
theorem Int128.intCast_neg (i : Int) : ((-i : Int) : Int128) = -(i : Int128) :=
  Int128.ofInt_neg _

attribute [local instance] Int128.intCast in
theorem Int128.intCast_ofNat (x : Nat) : (OfNat.ofNat (α := Int) x : Int128) = OfNat.ofNat x := Int128.ofInt_eq_ofNat

attribute [local instance] Int128.natCast Int128.intCast in
instance : CommRing Int128 where
  nsmul := ⟨(· * ·)⟩
  zsmul := ⟨(· * ·)⟩
  add_assoc := Int128.add_assoc
  add_comm := Int128.add_comm
  add_zero := Int128.add_zero
  neg_add_cancel := Int128.add_left_neg
  mul_assoc := Int128.mul_assoc
  mul_comm := Int128.mul_comm
  mul_one := Int128.mul_one
  one_mul := Int128.one_mul
  left_distrib _ _ _ := Int128.mul_add
  right_distrib _ _ _ := Int128.add_mul
  zero_mul _ := Int128.zero_mul
  mul_zero _ := Int128.mul_zero
  sub_eq_add_neg := Int128.sub_eq_add_neg
  pow_zero := Int128.pow_zero
  pow_succ := Int128.pow_succ
  ofNat_succ x := Int128.ofNat_add x 1
  intCast_neg := Int128.ofInt_neg
  neg_zsmul i x := by
    change (-i : Int) * x = - (i * x)
    simp [Int128.intCast_neg, Int128.neg_mul]
  zsmul_natCast_eq_nsmul n a := congrArg (· * a) (Int128.intCast_ofNat _)

instance : IsCharP Int128 (2 ^ 128) := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = Int128.ofInt x := rfl
    rw [this]
    simp [Int128.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_bmod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, Int.ofNat_dvd_right])

example : ToInt.Add Int128 (.sint 128) := inferInstance

example : ToInt.Neg Int128 (.sint 128) := inferInstance

example : ToInt.Sub Int128 (.sint 128) := inferInstance

instance : ToInt.Pow Int128 (.sint 128) := ToInt.pow_of_semiring (by simp)

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/GrindInstances/Ring/UInt.lean
-- Target: Hax/MissingLean/Init/GrindInstances/Ring/UInt.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean Grind

set_option autoImplicit true

namespace UInt128

/-- Variant of `UInt128.ofNat_mod_size` replacing `2 ^ 128` with `340282366920938463463374607431768211456`.-/
theorem ofNat_mod_size' : ofNat (x % 340282366920938463463374607431768211456) = ofNat x := ofNat_mod_size

@[expose, instance_reducible]
def natCast : NatCast UInt128 where
  natCast x := UInt128.ofNat x

@[expose, instance_reducible]
def intCast : IntCast UInt128 where
  intCast x := UInt128.ofInt x

attribute [local instance] natCast intCast

theorem intCast_neg (x : Int) : ((-x : Int) : UInt128) = - (x : UInt128) := by
  simp only [Int.cast, IntCast.intCast, UInt128.ofInt_neg]

theorem intCast_ofNat (x : Nat) : (OfNat.ofNat (α := Int) x : UInt128) = OfNat.ofNat x := by
    -- A better proof would be welcome!
    simp only [Int.cast, IntCast.intCast]
    rw [UInt128.ofInt]
    rw [Int.toNat_emod (Int.zero_le_ofNat x) (by decide)]
    erw [Int.toNat_natCast]
    rw [Int.toNat_pow_of_nonneg (by decide)]
    simp +instances only [ofNat, BitVec.ofNat, Fin.Internal.ofNat_eq_ofNat, Fin.ofNat, Int.reduceToNat, Nat.dvd_refl,
      Nat.mod_mod_of_dvd, instOfNat]
    try rfl

end UInt128

attribute [local instance] UInt128.natCast UInt128.intCast in
instance : CommRing UInt128 where
  nsmul := ⟨(· * ·)⟩
  zsmul := ⟨(· * ·)⟩
  add_assoc := UInt128.add_assoc
  add_comm := UInt128.add_comm
  add_zero := UInt128.add_zero
  neg_add_cancel := UInt128.add_left_neg
  mul_assoc := UInt128.mul_assoc
  mul_comm := UInt128.mul_comm
  mul_one := UInt128.mul_one
  one_mul := UInt128.one_mul
  left_distrib _ _ _ := UInt128.mul_add
  right_distrib _ _ _ := UInt128.add_mul
  zero_mul _ := UInt128.zero_mul
  mul_zero _ := UInt128.mul_zero
  sub_eq_add_neg := UInt128.sub_eq_add_neg
  pow_zero := UInt128.pow_zero
  pow_succ := UInt128.pow_succ
  ofNat_succ x := UInt128.ofNat_add x 1
  intCast_neg := UInt128.ofInt_neg
  intCast_ofNat := UInt128.intCast_ofNat
  neg_zsmul i a := by
    change (-i : Int) * a = - (i * a)
    simp [UInt128.intCast_neg, UInt128.neg_mul]
  zsmul_natCast_eq_nsmul n a := congrArg (· * a) (UInt128.intCast_ofNat _)

instance : IsCharP UInt128 340282366920938463463374607431768211456 := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = UInt128.ofNat x := rfl
    simp [this, UInt128.ofNat_eq_iff_mod_eq_toNat])

-- Verify we can derive the instances showing how `toInt` interacts with operations:
example : ToInt.Add UInt128 (.uint 128) := inferInstance
example : ToInt.Neg UInt128 (.uint 128) := inferInstance
example : ToInt.Sub UInt128 (.uint 128) := inferInstance

instance : ToInt.Pow UInt128 (.uint 128) := ToInt.pow_of_semiring (by simp)
