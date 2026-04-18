-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Prelude.lean
-- Target: Hax/MissingLean/Init/Prelude.lean
-- ──────────────────────────────────────────────────────────────────────

abbrev USize32.size : Nat := 4294967296

structure USize32 where
  /--
  Creates a `USize32` from a `BitVec 32`. This function is overridden with a native implementation.
  -/
  ofBitVec ::
  /--
  Unpacks a `USize32` into a `BitVec 32`. This function is overridden with a native implementation.
  -/
  toBitVec : BitVec 32

def USize32.ofNatLT (n : @& Nat) (h : LT.lt n USize32.size) : USize32 where
  toBitVec := BitVec.ofNatLT n h

def USize32.toNat (n : USize32) : Nat := n.toBitVec.toNat

def USize32.decEq (a b : USize32) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h => isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => USize32.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq USize32 := USize32.decEq

instance : Inhabited USize32 where
  default := USize32.ofNatLT 0 (of_decide_eq_true rfl)

instance : LT USize32 where
  lt a b := LT.lt a.toBitVec b.toBitVec

instance : LE USize32 where
  le a b := LE.le a.toBitVec b.toBitVec

def USize32.decLt (a b : USize32) : Decidable (LT.lt a b) :=
  inferInstanceAs (Decidable (LT.lt a.toBitVec b.toBitVec))

def USize32.decLe (a b : USize32) : Decidable (LE.le a b) :=
  inferInstanceAs (Decidable (LE.le a.toBitVec b.toBitVec))

instance : Max USize32 := maxOfLe

instance : Min USize32 := minOfLe

abbrev USize32.isValidChar (n : USize32) : Prop :=
  n.toNat.isValidChar

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/UInt/BasicAux.lean
-- Target: Hax/MissingLean/Init/Data/UInt/BasicAux.lean
-- ──────────────────────────────────────────────────────────────────────

def USize32.toFin (x : USize32) : Fin USize32.size := x.toBitVec.toFin

def USize32.ofNat (n : @& Nat) : USize32 := ⟨BitVec.ofNat 32 n⟩

def USize32.ofNatTruncate (n : Nat) : USize32 :=
  if h : n < USize32.size then
    USize32.ofNatLT n h
  else
    USize32.ofNatLT (USize32.size - 1) (by decide)

abbrev Nat.toUSize32 := USize32.ofNat

def USize32.toUInt8 (a : USize32) : UInt8 := a.toNat.toUInt8

def USize32.toUInt16 (a : USize32) : UInt16 := a.toNat.toUInt16

def UInt8.toUSize32 (a : UInt8) : USize32 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

def UInt16.toUSize32 (a : UInt16) : USize32 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

instance USize32.instOfNat : OfNat USize32 n := ⟨USize32.ofNat n⟩

theorem USize32.ofNatLT_lt_of_lt {n m : Nat} (h1 : n < USize32.size) (h2 : m < USize32.size) :
     n < m → USize32.ofNatLT n h1 < USize32.ofNat m := by
  simp only [(· < ·), BitVec.toNat, ofNatLT, BitVec.ofNatLT, ofNat, BitVec.ofNat,
    Fin.Internal.ofNat_eq_ofNat, Fin.ofNat, Nat.mod_eq_of_lt h2, imp_self]

theorem USize32.lt_ofNatLT_of_lt {n m : Nat} (h1 : n < USize32.size) (h2 : m < USize32.size) :
     m < n → USize32.ofNat m < USize32.ofNatLT n h1 := by
  simp only [(· < ·), BitVec.toNat, ofNatLT, BitVec.ofNatLT, ofNat, BitVec.ofNat, Fin.Internal.ofNat_eq_ofNat,
    Fin.ofNat, Nat.mod_eq_of_lt h2, imp_self]

protected def USize32.add (a b : USize32) : USize32 := ⟨a.toBitVec + b.toBitVec⟩

protected def USize32.sub (a b : USize32) : USize32 := ⟨a.toBitVec - b.toBitVec⟩

instance : Add USize32       := ⟨USize32.add⟩

instance : Sub USize32       := ⟨USize32.sub⟩

def UInt64.toUSize32 (a : UInt64) : USize32 := a.toNat.toUSize32

def USize32.toUInt64 (a : USize32) : UInt64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/UInt/Basic.lean
-- Target: Hax/MissingLean/Init/Data/UInt/Basic.lean
-- ──────────────────────────────────────────────────────────────────────

@[inline] def USize32.ofFin (a : Fin USize32.size) : USize32 := ⟨⟨a⟩⟩

def USize32.ofInt (x : Int) : USize32 := ofNat (x % 2 ^ 32).toNat

protected def USize32.mul (a b : USize32) : USize32 := ⟨a.toBitVec * b.toBitVec⟩

protected def USize32.div (a b : USize32) : USize32 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩

protected def USize32.pow (x : USize32) (n : Nat) : USize32 :=
  match n with
  | 0 => 1
  | n + 1 => USize32.mul (USize32.pow x n) x

protected def USize32.mod (a b : USize32) : USize32 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩

@[deprecated USize32.mod (since := "2024-09-23")]
protected def USize32.modn (a : USize32) (n : Nat) : USize32 := ⟨Fin.modn a.toFin n⟩

protected def USize32.land (a b : USize32) : USize32 := ⟨a.toBitVec &&& b.toBitVec⟩

protected def USize32.lor (a b : USize32) : USize32 := ⟨a.toBitVec ||| b.toBitVec⟩

protected def USize32.xor (a b : USize32) : USize32 := ⟨a.toBitVec ^^^ b.toBitVec⟩

protected def USize32.shiftLeft (a b : USize32) : USize32 := ⟨a.toBitVec <<< (USize32.mod b 32).toBitVec⟩

protected def USize32.shiftRight (a b : USize32) : USize32 := ⟨a.toBitVec >>> (USize32.mod b 32).toBitVec⟩

@[expose] protected def USize32.lt (a b : USize32) : Prop := a.toBitVec < b.toBitVec

@[expose] protected def USize32.le (a b : USize32) : Prop := a.toBitVec ≤ b.toBitVec

instance : Mul USize32       := ⟨USize32.mul⟩

instance : Pow USize32 Nat   := ⟨USize32.pow⟩

instance : Mod USize32       := ⟨USize32.mod⟩

instance : HMod USize32 Nat USize32 := ⟨USize32.modn⟩

instance : Div USize32       := ⟨USize32.div⟩

protected def USize32.complement (a : USize32) : USize32 := ⟨~~~a.toBitVec⟩

protected def USize32.neg (a : USize32) : USize32 := ⟨-a.toBitVec⟩

instance : Complement USize32 := ⟨USize32.complement⟩

instance : Neg USize32 := ⟨USize32.neg⟩

instance : AndOp USize32     := ⟨USize32.land⟩

instance : OrOp USize32      := ⟨USize32.lor⟩

instance : XorOp USize32       := ⟨USize32.xor⟩

instance : ShiftLeft USize32  := ⟨USize32.shiftLeft⟩

instance : ShiftRight USize32 := ⟨USize32.shiftRight⟩

def Bool.toUSize32 (b : Bool) : USize32 := if b then 1 else 0

def USize32.toUSize (a : USize32) : USize := USize.ofNat32 a.toBitVec.toNat a.toBitVec.isLt

def USize.toUSize32 (a : USize) : USize32 := a.toNat.toUSize32

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/SInt/Basic.lean
-- Target: Hax/MissingLean/Init/Data/SInt/Basic_Int128.lean
-- ──────────────────────────────────────────────────────────────────────

set_option autoImplicit true

structure ISize32 where
  ofUSize32 ::
  /--
  Converts an 32-bit signed integer into the 32-bit unsigned integer that is its two's complement
  encoding.
  -/
  toUSize32 : USize32

abbrev ISize32.size : Nat := 4294967296

@[inline] def ISize32.toBitVec (x : ISize32) : BitVec 32 := x.toUSize32.toBitVec

theorem ISize32.toBitVec.inj : {x y : ISize32} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

@[inline] def USize32.toISize32 (i : USize32) : ISize32 := ISize32.ofUSize32 i

def ISize32.ofInt (i : @& Int) : ISize32 := ⟨⟨BitVec.ofInt 32 i⟩⟩

def ISize32.ofNat (n : @& Nat) : ISize32 := ⟨⟨BitVec.ofNat 32 n⟩⟩

abbrev Int.toISize32 := ISize32.ofInt

abbrev Nat.toISize32 := ISize32.ofNat

def ISize32.toInt (i : ISize32) : Int := i.toBitVec.toInt

@[suggest_for ISize32.toNat, inline] def ISize32.toNatClampNeg (i : ISize32) : Nat := i.toInt.toNat

@[inline] def ISize32.ofBitVec (b : BitVec 32) : ISize32 := ⟨⟨b⟩⟩

def ISize32.toInt8 (a : ISize32) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩

def ISize32.toInt16 (a : ISize32) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩

def Int8.toISize32 (a : Int8) : ISize32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩

def Int16.toISize32 (a : Int16) : ISize32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩

def ISize32.neg (i : ISize32) : ISize32 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString ISize32 where
  toString i := toString i.toInt

instance : Repr ISize32 where
  reprPrec i prec := reprPrec i.toInt prec

instance : ReprAtom ISize32 := ⟨⟩

instance : Hashable ISize32 where
  hash i := i.toUSize32.toUInt64

instance ISize32.instOfNat : OfNat ISize32 n := ⟨ISize32.ofNat n⟩

instance ISize32.instNeg : Neg ISize32 where
  neg := ISize32.neg

abbrev ISize32.maxValue : ISize32 := 2147483647

abbrev ISize32.minValue : ISize32 := -2147483648

@[inline]
def ISize32.ofIntLE (i : Int) (_hl : ISize32.minValue.toInt ≤ i) (_hr : i ≤ ISize32.maxValue.toInt) : ISize32 :=
  ISize32.ofInt i

def ISize32.ofIntTruncate (i : Int) : ISize32 :=
  if hl : ISize32.minValue.toInt ≤ i then
    if hr : i ≤ ISize32.maxValue.toInt then
      ISize32.ofIntLE i hl hr
    else
      ISize32.minValue
  else
    ISize32.minValue

protected def ISize32.add (a b : ISize32) : ISize32 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩

protected def ISize32.sub (a b : ISize32) : ISize32 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩

protected def ISize32.mul (a b : ISize32) : ISize32 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩

protected def ISize32.div (a b : ISize32) : ISize32 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩

protected def ISize32.pow (x : ISize32) (n : Nat) : ISize32 :=
  match n with
  | 0 => 1
  | n + 1 => ISize32.mul (ISize32.pow x n) x

protected def ISize32.mod (a b : ISize32) : ISize32 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩

protected def ISize32.land (a b : ISize32) : ISize32 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩

protected def ISize32.lor (a b : ISize32) : ISize32 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩

protected def ISize32.xor (a b : ISize32) : ISize32 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩

protected def ISize32.shiftLeft (a b : ISize32) : ISize32 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 32)⟩⟩

protected def ISize32.shiftRight (a b : ISize32) : ISize32 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 32)⟩⟩

protected def ISize32.complement (a : ISize32) : ISize32 := ⟨⟨~~~a.toBitVec⟩⟩

protected def ISize32.abs (a : ISize32) : ISize32 := ⟨⟨a.toBitVec.abs⟩⟩

def ISize32.decEq (a b : ISize32) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => ISize32.noConfusion h' (fun h' => absurd h' h))

protected def ISize32.lt (a b : ISize32) : Prop := a.toBitVec.slt b.toBitVec

protected def ISize32.le (a b : ISize32) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited ISize32 where
  default := 0

instance : Add ISize32         := ⟨ISize32.add⟩

instance : Sub ISize32         := ⟨ISize32.sub⟩

instance : Mul ISize32         := ⟨ISize32.mul⟩

instance : Pow ISize32 Nat     := ⟨ISize32.pow⟩

instance : Mod ISize32         := ⟨ISize32.mod⟩

instance : Div ISize32         := ⟨ISize32.div⟩

instance : LT ISize32          := ⟨ISize32.lt⟩

instance : LE ISize32          := ⟨ISize32.le⟩

instance : Complement ISize32  := ⟨ISize32.complement⟩

instance : AndOp ISize32       := ⟨ISize32.land⟩

instance : OrOp ISize32        := ⟨ISize32.lor⟩

instance : XorOp ISize32         := ⟨ISize32.xor⟩

instance : ShiftLeft ISize32   := ⟨ISize32.shiftLeft⟩

instance : ShiftRight ISize32  := ⟨ISize32.shiftRight⟩

instance : DecidableEq ISize32 := ISize32.decEq

def Bool.toISize32 (b : Bool) : ISize32 := if b then 1 else 0

def ISize32.decLt (a b : ISize32) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

def ISize32.decLe (a b : ISize32) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

attribute [instance] ISize32.decLt ISize32.decLe

instance : Max ISize32 := maxOfLe

instance : Min ISize32 := minOfLe

def Int64.toISize32 (a : Int64) : ISize32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩

def ISize32.toInt64 (a : ISize32) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩

def ISize.toISize32 (a : ISize) : ISize32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩

def ISize32.toISize (a : ISize32) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩

-- ──────────────────────────────────────────────────────────────────────
-- Source: Lean/ToExpr.lean
-- Target: Hax/MissingLean/Lean/ToExpr.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean

instance : ToExpr USize32 where
  toTypeExpr := mkConst ``USize32
  toExpr a :=
    let r := mkRawNatLit a.toNat
    mkApp3 (.const ``OfNat.ofNat [0]) (mkConst ``USize32) r
      (.app (.const ``USize32.instOfNat []) r)

instance : ToExpr ISize32 where
  toTypeExpr := mkConst ``ISize32
  toExpr i := if 0 ≤ i then
    mkNat i.toNatClampNeg
  else
    mkApp3 (.const ``Neg.neg [0]) (.const ``ISize32 []) (.const ``ISize32.instNeg [])
      (mkNat (-(i.toInt)).toNat)
where
  mkNat (n : Nat) : Expr :=
    let r := mkRawNatLit n
    mkApp3 (.const ``OfNat.ofNat [0]) (.const ``ISize32 []) r
        (.app (.const ``ISize32.instOfNat []) r)

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

-- declare_uint_simprocs_ext USize32 -- macro call replaced with direct inline (macros don't handle dsimproc correctly)
namespace USize32

def fromExpr (e : Expr) : SimpM (Option USize32) := do
  let some (n, _) ← getOfNatValue? e ``USize32 | return none
  return ofNat n

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : USize32 → USize32 → USize32) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : USize32 → USize32 → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : USize32 → USize32 → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

dsimproc [simp, seval] reduceAdd ((_ + _ : USize32)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, seval] reduceMul ((_ * _ : USize32)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, seval] reduceSub ((_ - _ : USize32)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, seval] reduceDiv ((_ / _ : USize32)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, seval] reduceMod ((_ % _ : USize32)) := reduceBin ``HMod.hMod 6 (· % ·)

simproc [simp, seval] reduceLT  (( _ : USize32) < _)  := reduceBinPred ``LT.lt 4 (. < .)
simproc [simp, seval] reduceLE  (( _ : USize32) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] reduceGT  (( _ : USize32) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] reduceGE  (( _ : USize32) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
simproc [simp, seval] reduceEq  (( _ : USize32) = _)  := reduceBinPred ``Eq 3 (. = .)
simproc [simp, seval] reduceNe  (( _ : USize32) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
dsimproc [simp, seval] reduceBEq  (( _ : USize32) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
dsimproc [simp, seval] reduceBNe  (( _ : USize32) != _)  := reduceBoolPred ``bne 4 (. != .)

dsimproc [simp, seval] reduceOfNatLT (ofNatLT _ _) := fun e => do
  unless e.isAppOfArity ``USize32.ofNatLT 2 do return .continue
  let some value ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let value := ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfNat (ofNat _) := fun e => do
  unless e.isAppOfArity ``USize32.ofNat 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceToNat (toNat _) := fun e => do
  unless e.isAppOfArity ``USize32.toNat 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := toNat v
  return .done <| toExpr n

/-- Return `.done` for UInt values. We don't want to unfold in the symbolic evaluator. -/
dsimproc [seval] isValue ((OfNat.ofNat _ : USize32)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end USize32

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

-- declare_sint_simprocs_ext ISize32 -- macro call replaced with direct inline
namespace ISize32

def fromExpr (e : Expr) : SimpM (Option ISize32) := do
  if let some (n, _) ← getOfNatValue? e ``ISize32 then
    return some (ofNat n)
  let_expr Neg.neg _ _ a ← e | return none
  let some (n, _) ← getOfNatValue? a ``ISize32 | return none
  return some (ofInt (- n))

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : ISize32 → ISize32 → ISize32) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : ISize32 → ISize32 → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : ISize32 → ISize32 → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

dsimproc [simp, seval] reduceNeg ((- _ : ISize32)) := fun e => do
  let_expr Neg.neg _ _ arg ← e | return .continue
  if arg.isAppOfArity ``OfNat.ofNat 3 then
    -- We return .done to ensure `Neg.neg` is not unfolded even when `ground := true`.
    return .done e
  else
    let some v ← (fromExpr arg) | return .continue
    return .done <| toExpr (- v)

dsimproc [simp, seval] reduceAdd ((_ + _ : ISize32)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, seval] reduceMul ((_ * _ : ISize32)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, seval] reduceSub ((_ - _ : ISize32)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, seval] reduceDiv ((_ / _ : ISize32)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, seval] reduceMod ((_ % _ : ISize32)) := reduceBin ``HMod.hMod 6 (· % ·)

simproc [simp, seval] reduceLT  (( _ : ISize32) < _)  := reduceBinPred ``LT.lt 4 (. < .)
simproc [simp, seval] reduceLE  (( _ : ISize32) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] reduceGT  (( _ : ISize32) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] reduceGE  (( _ : ISize32) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
simproc [simp, seval] reduceEq  (( _ : ISize32) = _)  := reduceBinPred ``Eq 3 (. = .)
simproc [simp, seval] reduceNe  (( _ : ISize32) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
dsimproc [simp, seval] reduceBEq  (( _ : ISize32) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
dsimproc [simp, seval] reduceBNe  (( _ : ISize32) != _)  := reduceBoolPred ``bne 4 (. != .)

dsimproc [simp, seval] reduceOfIntLE (ofIntLE _ _ _) := fun e => do
  unless e.isAppOfArity ``ISize32.ofIntLE 3 do return .continue
  let some value ← Int.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  let value := ofInt value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfNat (ofNat _) := fun e => do
  unless e.isAppOfArity ``ISize32.ofNat 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfInt (ofInt _) := fun e => do
  unless e.isAppOfArity ``ISize32.ofInt 1 do return .continue
  let some value ← Int.fromExpr? e.appArg! | return .continue
  let value := ofInt value
  return .done <| toExpr value

dsimproc [simp, seval] reduceToInt (toInt _) := fun e => do
  unless e.isAppOfArity ``ISize32.toInt 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := toInt v
  return .done <| toExpr n

dsimproc [simp, seval] reduceToNatClampNeg (toNatClampNeg _) := fun e => do
  unless e.isAppOfArity ``ISize32.toNatClampNeg 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := toNatClampNeg v
  return .done <| toExpr n

/-- Return `.done` for Int values. We don't want to unfold in the symbolic evaluator. -/
dsimproc [seval] isValue ((OfNat.ofNat _ : ISize32)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end ISize32

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/UInt/Lemmas.lean
-- Target: Hax/MissingLean/Init/Data/UInt/Lemmas_UInt128.lean
-- ──────────────────────────────────────────────────────────────────────

set_option autoImplicit true
open Std

declare_uint_theorems USize32 32

@[simp] theorem USize.toNat_toUSize32 (x : USize) : x.toUSize32.toNat = x.toNat % 2 ^ 32 := (rfl)

theorem USize32.ofNat_mod_size : ofNat (x % 2 ^ 32) = ofNat x := by
  simp [ofNat, BitVec.ofNat, Fin.ofNat]

theorem USize32.ofNat_size : ofNat size = 0 := by decide

theorem USize32.lt_ofNat_iff {n : USize32} {m : Nat} (h : m < size) : n < ofNat m ↔ n.toNat < m := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]

theorem USize32.ofNat_lt_iff {n : USize32} {m : Nat} (h : m < size) : ofNat m < n ↔ m < n.toNat := by
  rw [lt_iff_toNat_lt, toNat_ofNat_of_lt' h]

theorem USize32.le_ofNat_iff {n : USize32} {m : Nat} (h : m < size) : n ≤ ofNat m ↔ n.toNat ≤ m := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]

theorem USize32.ofNat_le_iff {n : USize32} {m : Nat} (h : m < size) : ofNat m ≤ n ↔ m ≤ n.toNat := by
  rw [le_iff_toNat_le, toNat_ofNat_of_lt' h]

protected theorem USize32.mod_eq_of_lt {a b : USize32} (h : a < b) : a % b = a := USize32.toNat_inj.1 (Nat.mod_eq_of_lt h)

@[simp] theorem USize32.toNat_lt (n : USize32) : n.toNat < 2 ^ 32 := n.toFin.isLt

theorem USize32.size_le_usizeSize : USize32.size ≤ USize.size := by
  cases USize.size_eq <;> simp_all +decide

theorem USize32.toNat_lt_usizeSize (n : USize32) : n.toNat < USize.size :=
  Nat.lt_of_lt_of_le n.toNat_lt (by cases USize.size_eq <;> simp_all)

theorem USize32.size_dvd_usizeSize : USize32.size ∣ USize.size := by cases USize.size_eq <;> simp_all +decide

@[simp] theorem mod_usizeSize_uISize32Size (n : Nat) : n % USize.size % USize32.size = n % USize32.size :=
  Nat.mod_mod_of_dvd _ USize32.size_dvd_usizeSize

@[simp] theorem USize.size_sub_one_mod_uisize32Size : (USize.size - 1) % USize32.size = USize32.size - 1 := by
  cases USize.size_eq <;> simp_all +decide

@[simp] theorem UInt8.toNat_mod_uISize32Size (n : UInt8) : n.toNat % USize32.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))

@[simp] theorem UInt16.toNat_mod_uISize32Size (n : UInt16) : n.toNat % USize32.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))

@[simp] theorem USize32.toNat_mod_size (n : USize32) : n.toNat % USize32.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt

@[simp] theorem USize32.toNat_mod_uInt64Size (n : USize32) : n.toNat % UInt64.size = n.toNat := Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))

@[simp] theorem USize32.toNat_mod_uSizeSize (n : USize32) : n.toNat % USize.size = n.toNat := Nat.mod_eq_of_lt n.toNat_lt_usizeSize

@[simp] theorem UInt8.toUSize32_mod_256 (n : UInt8) : n.toUSize32 % 256 = n.toUSize32 := USize32.toNat.inj (by simp)

@[simp] theorem UInt16.toUSize32_mod_65536 (n : UInt16) : n.toUSize32 % 65536 = n.toUSize32 := USize32.toNat.inj (by simp)

@[simp] theorem USize32.toUInt64_mod_4294967296 (n : USize32) : n.toUInt64 % 4294967296 = n.toUInt64 := UInt64.toNat.inj (by simp)

@[simp] theorem Fin.mk_uISize32ToNat (n : USize32) : Fin.mk n.toNat (by exact n.toFin.isLt) = n.toFin := (rfl)

@[simp] theorem BitVec.ofNatLT_uISize32ToNat (n : USize32) : BitVec.ofNatLT n.toNat (by exact n.toFin.isLt) = n.toBitVec := (rfl)

@[simp] theorem BitVec.ofFin_uISize32ToFin (n : USize32) : BitVec.ofFin n.toFin = n.toBitVec := (rfl)

@[simp] theorem UInt8.toFin_toUSize32 (n : UInt8) : n.toUSize32.toFin = n.toFin.castLE (by decide) := (rfl)

@[simp] theorem UInt16.toFin_toUSize32 (n : UInt16) : n.toUSize32.toFin = n.toFin.castLE (by decide) := (rfl)

@[simp] theorem USize32.toFin_toUInt64 (n : USize32) : n.toUInt64.toFin = n.toFin.castLE (by decide) := (rfl)

@[simp] theorem USize32.toFin_toUSize (n : USize32) :
  n.toUSize.toFin = n.toFin.castLE size_le_usizeSize := (rfl)

@[simp, int_toBitVec] theorem USize32.toBitVec_toUInt8 (n : USize32) : n.toUInt8.toBitVec = n.toBitVec.setWidth 8 := (rfl)

@[simp, int_toBitVec] theorem USize32.toBitVec_toUInt16 (n : USize32) : n.toUInt16.toBitVec = n.toBitVec.setWidth 16 := (rfl)

@[simp, int_toBitVec] theorem UInt8.toBitVec_toUSize32 (n : UInt8) : n.toUSize32.toBitVec = n.toBitVec.setWidth 32 := (rfl)

@[simp, int_toBitVec] theorem UInt16.toBitVec_toUSize32 (n : UInt16) : n.toUSize32.toBitVec = n.toBitVec.setWidth 32 := (rfl)

@[simp, int_toBitVec] theorem UInt64.toBitVec_toUSize32 (n : UInt64) : n.toUSize32.toBitVec = n.toBitVec.setWidth 32 := (rfl)

@[simp, int_toBitVec] theorem USize.toBitVec_toUSize32 (n : USize) : n.toUSize32.toBitVec = n.toBitVec.setWidth 32 := BitVec.eq_of_toNat_eq (by simp)

@[simp, int_toBitVec] theorem USize32.toBitVec_toUInt64 (n : USize32) : n.toUInt64.toBitVec = n.toBitVec.setWidth 64 := (rfl)

@[simp, int_toBitVec] theorem USize32.toBitVec_toUSize (n : USize32) : n.toUSize.toBitVec = n.toBitVec.setWidth System.Platform.numBits :=
  BitVec.eq_of_toNat_eq (by simp)

@[simp] theorem USize32.ofNatLT_uInt8ToNat (n : UInt8) : USize32.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUSize32 := (rfl)

@[simp] theorem USize32.ofNatLT_uInt16ToNat (n : UInt16) : USize32.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUSize32 := (rfl)

@[simp] theorem USize32.ofNatLT_toNat (n : USize32) : USize32.ofNatLT n.toNat n.toNat_lt = n := (rfl)

@[simp] theorem UInt64.ofNatLT_uISize32ToNat (n : USize32) : UInt64.ofNatLT n.toNat (Nat.lt_trans n.toNat_lt (by decide)) = n.toUInt64 := (rfl)

@[simp] theorem USize.ofNatLT_uISize32ToNat (n : USize32) : USize.ofNatLT n.toNat n.toNat_lt_usizeSize = n.toUSize := (rfl)

theorem UInt8.ofNatLT_uISize32ToNat (n : USize32) (h) : UInt8.ofNatLT n.toNat h = n.toUInt8 :=
  UInt8.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem UInt16.ofNatLT_uISize32ToNat (n : USize32) (h) : UInt16.ofNatLT n.toNat h = n.toUInt16 :=
  UInt16.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem USize32.ofNatLT_uInt64ToNat (n : UInt64) (h) : USize32.ofNatLT n.toNat h = n.toUSize32 :=
  USize32.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem USize32.ofNatLT_uSizeToNat (n : USize) (h) : USize32.ofNatLT n.toNat h = n.toUSize32 :=
  USize32.toNat.inj (by simp [Nat.mod_eq_of_lt h])

@[simp] theorem USize32.ofFin_toFin (n : USize32) : USize32.ofFin n.toFin = n := (rfl)

@[simp] theorem USize32.toFin_ofFin (n : Fin USize32.size) : (USize32.ofFin n).toFin = n := (rfl)

@[simp] theorem USize32.ofFin_uint8ToFin (n : UInt8) : USize32.ofFin (n.toFin.castLE (by decide)) = n.toUSize32 := (rfl)

@[simp] theorem USize32.ofFin_uint16ToFin (n : UInt16) : USize32.ofFin (n.toFin.castLE (by decide)) = n.toUSize32 := (rfl)

@[simp] theorem UInt64.ofFin_uisize32ToFin (n : USize32) : UInt64.ofFin (n.toFin.castLE (by decide)) = n.toUInt64 := (rfl)

@[simp] theorem USize.ofFin_uisize32ToFin (n : USize32) : USize.ofFin (n.toFin.castLE USize32.size_le_usizeSize) = n.toUSize := (rfl)

@[simp] theorem Nat.toUSize32_eq {n : Nat} : n.toUSize32 = USize32.ofNat n := (rfl)

@[simp] theorem UInt8.ofBitVec_uISize32ToBitVec (n : USize32) :
    UInt8.ofBitVec (n.toBitVec.setWidth 8) = n.toUInt8 := (rfl)

@[simp] theorem UInt16.ofBitVec_uISize32ToBitVec (n : USize32) :
    UInt16.ofBitVec (n.toBitVec.setWidth 16) = n.toUInt16 := (rfl)

@[simp] theorem USize32.ofBitVec_uInt8ToBitVec (n : UInt8) :
    USize32.ofBitVec (n.toBitVec.setWidth 32) = n.toUSize32 := (rfl)

@[simp] theorem USize32.ofBitVec_uInt16ToBitVec (n : UInt16) :
    USize32.ofBitVec (n.toBitVec.setWidth 32) = n.toUSize32 := (rfl)

@[simp] theorem USize32.ofBitVec_uInt64ToBitVec (n : UInt64) :
    USize32.ofBitVec (n.toBitVec.setWidth 32) = n.toUSize32 := (rfl)

@[simp] theorem USize32.ofBitVec_uSizeToBitVec (n : USize) :
    USize32.ofBitVec (n.toBitVec.setWidth 32) = n.toUSize32 := USize32.toNat.inj (by simp)

@[simp] theorem UInt64.ofBitVec_uISize32ToBitVec (n : USize32) :
    UInt64.ofBitVec (n.toBitVec.setWidth 64) = n.toUInt64 := (rfl)

@[simp] theorem USize.ofBitVec_uISize32ToBitVec (n : USize32) :
    USize.ofBitVec (n.toBitVec.setWidth System.Platform.numBits) = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt8.ofNat_uISize32ToNat (n : USize32) : UInt8.ofNat n.toNat = n.toUInt8 := (rfl)

@[simp] theorem UInt16.ofNat_uISize32ToNat (n : USize32) : UInt16.ofNat n.toNat = n.toUInt16 := (rfl)

@[simp] theorem USize32.ofNat_uInt8ToNat (n : UInt8) : USize32.ofNat n.toNat = n.toUSize32 :=
  USize32.toNat.inj (by simp)

@[simp] theorem USize32.ofNat_uInt16ToNat (n : UInt16) : USize32.ofNat n.toNat = n.toUSize32 :=
  USize32.toNat.inj (by simp)

@[simp] theorem USize32.ofNat_uInt64ToNat (n : UInt64) : USize32.ofNat n.toNat = n.toUSize32 := (rfl)

@[simp] theorem USize32.ofNat_uSizeToNat (n : USize) : USize32.ofNat n.toNat = n.toUSize32 := (rfl)

@[simp] theorem UInt64.ofNat_uISize32ToNat (n : USize32) : UInt64.ofNat n.toNat = n.toUInt64 :=
  UInt64.toNat.inj (by simp)

@[simp] theorem USize.ofNat_uISize32ToNat (n : USize32) : USize.ofNat n.toNat = n.toUSize :=
  USize.toNat.inj (by simp)

theorem USize32.ofNatLT_eq_ofNat (n : Nat) {h} : USize32.ofNatLT n h = USize32.ofNat n :=
  USize32.toNat.inj (by simp [Nat.mod_eq_of_lt h])

theorem USize32.ofNatTruncate_eq_ofNat (n : Nat) (hn : n < USize32.size) :
    USize32.ofNatTruncate n = USize32.ofNat n := by
  simp [ofNatTruncate, hn, USize32.ofNatLT_eq_ofNat]

@[simp] theorem USize32.ofNatTruncate_uInt8ToNat (n : UInt8) : USize32.ofNatTruncate n.toNat = n.toUSize32 := by
  rw [USize32.ofNatTruncate_eq_ofNat, ofNat_uInt8ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)

@[simp] theorem USize32.ofNatTruncate_uInt16ToNat (n : UInt16) : USize32.ofNatTruncate n.toNat = n.toUSize32 := by
  rw [USize32.ofNatTruncate_eq_ofNat, ofNat_uInt16ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)

@[simp] theorem USize32.ofNatTruncate_toNat (n : USize32) : USize32.ofNatTruncate n.toNat = n := by
  rw [USize32.ofNatTruncate_eq_ofNat] <;> simp [n.toNat_lt]

@[simp] theorem UInt64.ofNatTruncate_uISize32ToNat (n : USize32) : UInt64.ofNatTruncate n.toNat = n.toUInt64 := by
  rw [UInt64.ofNatTruncate_eq_ofNat, ofNat_uISize32ToNat]
  exact Nat.lt_trans (n.toNat_lt) (by decide)

@[simp] theorem USize.ofNatTruncate_uISize32ToNat (n : USize32) : USize.ofNatTruncate n.toNat = n.toUSize := by
  rw [USize.ofNatTruncate_eq_ofNat, ofNat_uISize32ToNat]
  exact n.toNat_lt_usizeSize

@[simp] theorem UInt8.toUInt8_toUSize32 (n : UInt8) : n.toUSize32.toUInt8 = n :=
  UInt8.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt16_toUSize32 (n : UInt8) : n.toUSize32.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt8.toUSize32_toUInt16 (n : UInt8) : n.toUInt16.toUSize32 = n.toUSize32 := (rfl)

@[simp] theorem UInt8.toUSize32_toUInt64 (n : UInt8) : n.toUInt64.toUSize32 = n.toUSize32 :=
  USize32.toNat.inj (by simp)

@[simp] theorem UInt8.toUSize32_toUSize (n : UInt8) : n.toUSize.toUSize32 = n.toUSize32 :=
  USize32.toNat.inj (by simp)

@[simp] theorem UInt8.toUInt64_toUSize32 (n : UInt8) : n.toUSize32.toUInt64 = n.toUInt64 := (rfl)

@[simp] theorem UInt8.toUSize_toUSize32 (n : UInt8) : n.toUSize32.toUSize = n.toUSize := (rfl)

@[simp] theorem UInt16.toUInt8_toUSize32 (n : UInt16) : n.toUSize32.toUInt8 = n.toUInt8 := (rfl)

@[simp] theorem UInt16.toUInt16_toUSize32 (n : UInt16) : n.toUSize32.toUInt16 = n :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt16.toUSize32_toUInt8 (n : UInt16) : n.toUInt8.toUSize32 = n.toUSize32 % 256 := (rfl)

@[simp] theorem UInt16.toUSize32_toUInt64 (n : UInt16) : n.toUInt64.toUSize32 = n.toUSize32 :=
  USize32.toNat.inj (by simp)

@[simp] theorem UInt16.toUSize32_toUSize (n : UInt16) : n.toUSize.toUSize32 = n.toUSize32 :=
  USize32.toNat.inj (by simp)

@[simp] theorem UInt16.toUInt64_toUSize32 (n : UInt16) : n.toUSize32.toUInt64 = n.toUInt64 := (rfl)

@[simp] theorem UInt16.toUSize_toUSize32 (n : UInt16) : n.toUSize32.toUSize = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem USize32.toUInt8_toUInt16 (n : USize32) : n.toUInt16.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)

@[simp] theorem USize32.toUInt8_toUInt64 (n : USize32) : n.toUInt64.toUInt8 = n.toUInt8 := (rfl)

@[simp] theorem USize32.toUInt8_toUSize (n : USize32) : n.toUSize.toUInt8 = n.toUInt8 := (rfl)

@[simp] theorem USize32.toUInt16_toUInt8 (n : USize32) : n.toUInt8.toUInt16 = n.toUInt16 % 256 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem USize32.toUInt16_toUInt64 (n : USize32) : n.toUInt64.toUInt16 = n.toUInt16 := (rfl)

@[simp] theorem USize32.toUInt16_toUSize (n : USize32) : n.toUSize.toUInt16 = n.toUInt16 := (rfl)

@[simp] theorem USize32.toUSize32_toUInt8 (n : USize32) : n.toUInt8.toUSize32 = n % 256 := (rfl)

@[simp] theorem USize32.toUSize32_toUInt16 (n : USize32) : n.toUInt16.toUSize32 = n % 65536 := (rfl)

@[simp] theorem USize32.toUSize32_toUInt64 (n : USize32) : n.toUInt64.toUSize32 = n :=
  USize32.toNat.inj (by simp)

@[simp] theorem USize32.toUSize32_toUSize (n : USize32) : n.toUSize.toUSize32 = n :=
  USize32.toNat.inj (by simp)

@[simp] theorem USize32.toUInt64_toUInt8 (n : USize32) : n.toUInt8.toUInt64 = n.toUInt64 % 256 := (rfl)

@[simp] theorem USize32.toUInt64_toUInt16 (n : USize32) : n.toUInt16.toUInt64 = n.toUInt64 % 65536 := (rfl)

@[simp] theorem USize32.toUInt64_toUSize (n : USize32) : n.toUSize.toUInt64 = n.toUInt64 := (rfl)

@[simp] theorem USize32.toUSize_toUInt8 (n : USize32) : n.toUInt8.toUSize = n.toUSize % 256 :=
  USize.toNat.inj (by simp)

@[simp] theorem USize32.toUSize_toUInt16 (n : USize32) : n.toUInt16.toUSize = n.toUSize % 65536 :=
  USize.toNat.inj (by simp)

@[simp] theorem USize32.toUSize_toUInt64 (n : USize32) : n.toUInt64.toUSize = n.toUSize :=
  USize.toNat.inj (by simp)

@[simp] theorem UInt64.toUInt8_toUSize32 (n : UInt64) : n.toUSize32.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)

@[simp] theorem UInt64.toUInt16_toUSize32 (n : UInt64) : n.toUSize32.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem UInt64.toUSize32_toUInt8 (n : UInt64) : n.toUInt8.toUSize32 = n.toUSize32 % 256 :=
  USize32.toNat.inj (by simp)

@[simp] theorem UInt64.toUSize32_toUInt16 (n : UInt64) : n.toUInt16.toUSize32 = n.toUSize32 % 65536 :=
  USize32.toNat.inj (by simp)

@[simp] theorem UInt64.toUSize32_toUSize (n : UInt64) : n.toUSize.toUSize32 = n.toUSize32 :=
  USize32.toNat.inj (by simp)

@[simp] theorem UInt64.toUInt64_toUSize32 (n : UInt64) : n.toUSize32.toUInt64 = n % 4294967296 := (rfl)

@[simp] theorem USize.toUInt8_toUSize32 (n : USize) : n.toUSize32.toUInt8 = n.toUInt8 :=
  UInt8.toNat.inj (by simp)

@[simp] theorem USize.toUInt16_toUSize32 (n : USize) : n.toUSize32.toUInt16 = n.toUInt16 :=
  UInt16.toNat.inj (by simp)

@[simp] theorem USize.toUSize32_toUInt8 (n : USize) : n.toUInt8.toUSize32 = n.toUSize32 % 256 :=
  USize32.toNat.inj (by simp)

@[simp] theorem USize.toUSize32_toUInt16 (n : USize) : n.toUInt16.toUSize32 = n.toUSize32 % 65536 :=
  USize32.toNat.inj (by simp)

@[simp] theorem USize.toUSize32_toUInt64 (n : USize) : n.toUInt64.toUSize32 = n.toUSize32 :=
  USize32.toNat.inj (by simp)

@[simp] theorem USize.toUSize_toUSize32 (n : USize) : n.toUSize32.toUSize = n % 4294967296 := by
  apply USize.toNat.inj
  simp only [USize32.toNat_toUSize, toNat_toUSize32, Nat.reducePow, USize.toNat_mod]
  cases USize.size_eq
  next h => rw [Nat.mod_eq_of_lt (h ▸ n.toNat_lt_size), USize.toNat_ofNat,
      ← USize.size_eq_two_pow, h, Nat.mod_self, Nat.mod_zero]
  next h => rw [USize.toNat_ofNat_of_lt]; simp_all

@[simp] theorem USize32.toNat_ofFin (x : Fin USize32.size) : (USize32.ofFin x).toNat = x.val := (rfl)

theorem USize32.toNat_ofNatTruncate_of_lt {n : Nat} (hn : n < USize32.size) :
    (USize32.ofNatTruncate n).toNat = n := by rw [USize32.ofNatTruncate, dif_pos hn, toNat_ofNatLT]

theorem USize32.toNat_ofNatTruncate_of_le {n : Nat} (hn : USize32.size ≤ n) :
    (USize32.ofNatTruncate n).toNat = USize32.size - 1 := by rw [ofNatTruncate, dif_neg (by omega), toNat_ofNatLT]

@[simp] theorem USize32.toFin_ofNatLT {n : Nat} (hn) : (USize32.ofNatLT n hn).toFin = ⟨n, hn⟩ := (rfl)

@[simp] theorem USize32.toFin.ofNat {n : Nat} : (USize32.ofNat n).toFin = Fin.ofNat _ n := (rfl)

@[simp] theorem USize32.toFin_ofBitVec {b} : (USize32.ofBitVec b).toFin = b.toFin := (rfl)

theorem USize32.toFin_ofNatTruncate_of_lt {n : Nat} (hn : n < USize32.size) :
    (USize32.ofNatTruncate n).toFin = ⟨n, hn⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_lt hn])

theorem USize32.toFin_ofNatTruncate_of_le {n : Nat} (hn : USize32.size ≤ n) :
    (USize32.ofNatTruncate n).toFin = ⟨USize32.size - 1, by decide⟩ :=
  Fin.val_inj.1 (by simp [toNat_ofNatTruncate_of_le hn])

@[simp, int_toBitVec] theorem USize32.toBitVec_ofNatLT {n : Nat} (hn : n < USize32.size) :
    (USize32.ofNatLT n hn).toBitVec = BitVec.ofNatLT n hn := (rfl)

@[simp, int_toBitVec] theorem USize32.toBitVec_ofFin (n : Fin USize32.size) : (USize32.ofFin n).toBitVec = BitVec.ofFin n := (rfl)

@[simp, int_toBitVec] theorem USize32.toBitVec_ofBitVec (n) : (USize32.ofBitVec n).toBitVec = n := (rfl)

theorem USize32.toBitVec_ofNatTruncate_of_lt {n : Nat} (hn : n < USize32.size) :
    (USize32.ofNatTruncate n).toBitVec = BitVec.ofNatLT n hn :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_lt hn])

theorem USize32.toBitVec_ofNatTruncate_of_le {n : Nat} (hn : USize32.size ≤ n) :
    (USize32.ofNatTruncate n).toBitVec = BitVec.ofNatLT (USize32.size - 1) (by decide) :=
  BitVec.eq_of_toNat_eq (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem USize32.toUInt8_ofNatLT {n : Nat} (hn) : (USize32.ofNatLT n hn).toUInt8 = UInt8.ofNat n := (rfl)

@[simp] theorem USize32.toUInt8_ofFin (n) : (USize32.ofFin n).toUInt8 = UInt8.ofNat n.val := (rfl)

@[simp] theorem USize32.toUInt8_ofBitVec (b) : (USize32.ofBitVec b).toUInt8 = UInt8.ofBitVec (b.setWidth _) := (rfl)

@[simp] theorem USize32.toUInt8_ofNat' (n : Nat) : (USize32.ofNat n).toUInt8 = UInt8.ofNat n := UInt8.toNat.inj (by simp)

@[simp] theorem USize32.toUInt8_ofNat {n : Nat} : toUInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toUInt8_ofNat' _

theorem USize32.toUInt8_ofNatTruncate_of_lt {n : Nat} (hn : n < USize32.size) :
    (USize32.ofNatTruncate n).toUInt8 = UInt8.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt8_ofNatLT]

theorem USize32.toUInt8_ofNatTruncate_of_le {n : Nat} (hn : USize32.size ≤ n) :
    (USize32.ofNatTruncate n).toUInt8 = UInt8.ofNatLT (UInt8.size - 1) (by decide) :=
  UInt8.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem USize32.toUInt16_ofNatLT {n : Nat} (hn) : (USize32.ofNatLT n hn).toUInt16 = UInt16.ofNat n := (rfl)

@[simp] theorem USize32.toUInt16_ofFin (n) : (USize32.ofFin n).toUInt16 = UInt16.ofNat n.val := (rfl)

@[simp] theorem USize32.toUInt16_ofBitVec (b) : (USize32.ofBitVec b).toUInt16 = UInt16.ofBitVec (b.setWidth _) := (rfl)

@[simp] theorem USize32.toUInt16_ofNat' (n : Nat) : (USize32.ofNat n).toUInt16 = UInt16.ofNat n := UInt16.toNat.inj (by simp)

@[simp] theorem USize32.toUInt16_ofNat {n : Nat} : toUInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := USize32.toUInt16_ofNat' _

theorem USize32.toUInt16_ofNatTruncate_of_lt {n : Nat} (hn : n < USize32.size) :
    (USize32.ofNatTruncate n).toUInt16 = UInt16.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUInt16_ofNatLT]

theorem USize32.toUInt16_ofNatTruncate_of_le {n : Nat} (hn : USize32.size ≤ n) :
    (USize32.ofNatTruncate n).toUInt16 = UInt16.ofNatLT (UInt16.size - 1) (by decide) :=
  UInt16.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt64.toUSize32_ofNatLT {n : Nat} (hn) : (UInt64.ofNatLT n hn).toUSize32 = USize32.ofNat n := (rfl)

@[simp] theorem USize.toUSize32_ofNatLT {n : Nat} (hn) : (USize.ofNatLT n hn).toUSize32 = USize32.ofNat n := (rfl)

@[simp] theorem UInt64.toUSize32_ofFin (n) : (UInt64.ofFin n).toUSize32 = USize32.ofNat n.val := (rfl)

@[simp] theorem USize.toUSize32_ofFin (n) : (USize.ofFin n).toUSize32 = USize32.ofNat n.val := (rfl)

@[simp] theorem UInt64.toUSize32_ofBitVec (b) : (UInt64.ofBitVec b).toUSize32 = USize32.ofBitVec (b.setWidth _) := (rfl)

@[simp] theorem USize.toUSize32_ofBitVec (b) : (USize.ofBitVec b).toUSize32 = USize32.ofBitVec (b.setWidth _) :=
  USize32.toNat.inj (by simp)

@[simp] theorem UInt64.toUSize32_ofNat' (n : Nat) : (UInt64.ofNat n).toUSize32 = USize32.ofNat n := USize32.toNat.inj (by simp)

@[simp] theorem USize.toUSize32_ofNat' (n : Nat) : (USize.ofNat n).toUSize32 = USize32.ofNat n := USize32.toNat.inj (by simp)

@[simp] theorem UInt64.toUSize32_ofNat {n : Nat} : toUSize32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := UInt64.toUSize32_ofNat' _

@[simp] theorem USize.toUSize32_ofNat {n : Nat} : toUSize32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := USize.toUSize32_ofNat' _

theorem UInt64.toUSize32_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt64.size) :
    (UInt64.ofNatTruncate n).toUSize32 = USize32.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUSize32_ofNatLT]

theorem USize.toUSize32_ofNatTruncate_of_lt {n : Nat} (hn : n < USize.size) :
    (USize.ofNatTruncate n).toUSize32 = USize32.ofNat n := by rw [ofNatTruncate, dif_pos hn, toUSize32_ofNatLT]

theorem UInt64.toUSize32_ofNatTruncate_of_le {n : Nat} (hn : UInt64.size ≤ n) :
    (UInt64.ofNatTruncate n).toUSize32 = USize32.ofNatLT (USize32.size - 1) (by decide) :=
  USize32.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem USize.toUSize32_ofNatTruncate_of_le {n : Nat} (hn : USize.size ≤ n) :
    (USize.ofNatTruncate n).toUSize32 = USize32.ofNatLT (USize32.size - 1) (by decide) :=
  USize32.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt8.toUSize32_ofNatLT {n : Nat} (h) :
    (UInt8.ofNatLT n h).toUSize32 = USize32.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := (rfl)

theorem UInt8.toUSize32_ofFin {n} :
  (UInt8.ofFin n).toUSize32 = USize32.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := (rfl)

@[simp] theorem UInt8.toUSize32_ofBitVec {b} : (UInt8.ofBitVec b).toUSize32 = USize32.ofBitVec (b.setWidth _) := (rfl)

theorem UInt8.toUSize32_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt8.size) :
    (UInt8.ofNatTruncate n).toUSize32 = USize32.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  USize32.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt8.toUSize32_ofNatTruncate_of_le {n : Nat} (hn : UInt8.size ≤ n) :
    (UInt8.ofNatTruncate n).toUSize32 = USize32.ofNatLT (UInt8.size - 1) (by decide) :=
  USize32.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem UInt16.toUSize32_ofNatLT {n : Nat} (h) :
    (UInt16.ofNatLT n h).toUSize32 = USize32.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := (rfl)

theorem UInt16.toUSize32_ofFin {n} :
  (UInt16.ofFin n).toUSize32 = USize32.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := (rfl)

@[simp] theorem UInt16.toUSize32_ofBitVec {b} : (UInt16.ofBitVec b).toUSize32 = USize32.ofBitVec (b.setWidth _) := (rfl)

theorem UInt16.toUSize32_ofNatTruncate_of_lt {n : Nat} (hn : n < UInt16.size) :
    (UInt16.ofNatTruncate n).toUSize32 = USize32.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  USize32.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem UInt16.toUSize32_ofNatTruncate_of_le {n : Nat} (hn : UInt16.size ≤ n) :
    (UInt16.ofNatTruncate n).toUSize32 = USize32.ofNatLT (UInt16.size - 1) (by decide) :=
  USize32.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem USize32.toUInt64_ofNatLT {n : Nat} (h) :
    (USize32.ofNatLT n h).toUInt64 = UInt64.ofNatLT n (Nat.lt_of_lt_of_le h (by decide)) := (rfl)

theorem USize32.toUSize_ofNatLT {n : Nat} (h) :
    (USize32.ofNatLT n h).toUSize = USize.ofNatLT n (Nat.lt_of_lt_of_le h size_le_usizeSize) := (rfl)

theorem USize32.toUInt64_ofFin {n} :
  (USize32.ofFin n).toUInt64 = UInt64.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt (by decide)) := (rfl)

theorem USize32.toUSize_ofFin {n} :
  (USize32.ofFin n).toUSize = USize.ofNatLT n.val (Nat.lt_of_lt_of_le n.isLt size_le_usizeSize) := (rfl)

@[simp] theorem USize32.toUInt64_ofBitVec {b} : (USize32.ofBitVec b).toUInt64 = UInt64.ofBitVec (b.setWidth _) := (rfl)

@[simp] theorem USize32.toUSize_ofBitVec {b} : (USize32.ofBitVec b).toUSize = USize.ofBitVec (b.setWidth _) :=
  USize.toBitVec_inj.1 (by simp)

theorem USize32.toUInt64_ofNatTruncate_of_lt {n : Nat} (hn : n < USize32.size) :
    (USize32.ofNatTruncate n).toUInt64 = UInt64.ofNatLT n (Nat.lt_of_lt_of_le hn (by decide)) :=
  UInt64.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem USize32.toUSize_ofNatTruncate_of_lt {n : Nat} (hn : n < USize32.size) :
    (USize32.ofNatTruncate n).toUSize = USize.ofNatLT n (Nat.lt_of_lt_of_le hn size_le_usizeSize) :=
  USize.toNat.inj (by simp [toNat_ofNatTruncate_of_lt hn])

theorem USize32.toUInt64_ofNatTruncate_of_le {n : Nat} (hn : USize32.size ≤ n) :
    (USize32.ofNatTruncate n).toUInt64 = UInt64.ofNatLT (USize32.size - 1) (by decide) :=
  UInt64.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

theorem USize32.toUSize_ofNatTruncate_of_le {n : Nat} (hn : USize32.size ≤ n) :
    (USize32.ofNatTruncate n).toUSize = USize.ofNatLT (USize32.size - 1) (Nat.lt_of_lt_of_le (by decide) size_le_usizeSize) :=
  USize.toNat.inj (by simp [toNat_ofNatTruncate_of_le hn])

@[simp] theorem UInt8.toUSize32_ofNat' {n : Nat} (hn : n < UInt8.size) : (UInt8.ofNat n).toUSize32 = USize32.ofNat n := by
  rw [← UInt8.ofNatLT_eq_ofNat (h := hn), toUSize32_ofNatLT, USize32.ofNatLT_eq_ofNat]

@[simp] theorem UInt16.toUSize32_ofNat' {n : Nat} (hn : n < UInt16.size) : (UInt16.ofNat n).toUSize32 = USize32.ofNat n := by
  rw [← UInt16.ofNatLT_eq_ofNat (h := hn), toUSize32_ofNatLT, USize32.ofNatLT_eq_ofNat]

@[simp] theorem USize32.toUInt64_ofNat' {n : Nat} (hn : n < USize32.size) : (USize32.ofNat n).toUInt64 = UInt64.ofNat n := by
  rw [← USize32.ofNatLT_eq_ofNat (h := hn), toUInt64_ofNatLT, UInt64.ofNatLT_eq_ofNat]

@[simp] theorem USize32.toUSize_ofNat' {n : Nat} (hn : n < USize32.size) : (USize32.ofNat n).toUSize = USize.ofNat n := by
  rw [← USize32.ofNatLT_eq_ofNat (h := hn), toUSize_ofNatLT, USize.ofNatLT_eq_ofNat]

@[simp] theorem UInt8.toUSize32_ofNat {n : Nat} (hn : n < 256) : toUSize32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt8.toUSize32_ofNat' hn

@[simp] theorem UInt16.toUSize32_ofNat {n : Nat} (hn : n < 65536) : toUSize32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  UInt16.toUSize32_ofNat' hn

@[simp] theorem USize32.toUInt64_ofNat {n : Nat} (hn : n < 4294967296) : toUInt64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  USize32.toUInt64_ofNat' hn

@[simp] theorem USize32.toUSize_ofNat {n : Nat} (hn : n < 4294967296) : toUSize (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  USize32.toUSize_ofNat' hn

@[simp] theorem USize.toUInt64_ofNat {n : Nat} (hn : n < 4294967296) : toUInt64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  USize.toUInt64_ofNat' (Nat.lt_of_lt_of_le hn USize32.size_le_usizeSize)

@[simp] theorem USize32.ofNatLT_finVal (n : Fin USize32.size) : USize32.ofNatLT n.val n.isLt = USize32.ofFin n := (rfl)

@[simp] theorem USize32.ofNatLT_bitVecToNat (n : BitVec 32) : USize32.ofNatLT n.toNat n.isLt = USize32.ofBitVec n := (rfl)

@[simp] theorem USize32.ofNat_finVal (n : Fin USize32.size) : USize32.ofNat n.val = USize32.ofFin n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_finVal]

@[simp] theorem USize32.ofNat_bitVecToNat (n : BitVec 32) : USize32.ofNat n.toNat = USize32.ofBitVec n := by
  rw [← ofNatLT_eq_ofNat (h := n.isLt), ofNatLT_bitVecToNat]

@[simp] theorem USize32.ofNatTruncate_finVal (n : Fin USize32.size) : USize32.ofNatTruncate n.val = USize32.ofFin n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, USize32.ofNat_finVal]

@[simp] theorem USize32.ofNatTruncate_bitVecToNat (n : BitVec 32) : USize32.ofNatTruncate n.toNat = USize32.ofBitVec n := by
  rw [ofNatTruncate_eq_ofNat _ n.isLt, ofNat_bitVecToNat]

@[simp] theorem USize32.ofFin_mk {n : Nat} (hn) : USize32.ofFin (Fin.mk n hn) = USize32.ofNatLT n hn := (rfl)

@[simp] theorem USize32.ofFin_bitVecToFin (n : BitVec 32) : USize32.ofFin n.toFin = USize32.ofBitVec n := (rfl)

@[simp] theorem USize32.ofBitVec_ofNatLT {n : Nat} (hn) : USize32.ofBitVec (BitVec.ofNatLT n hn) = USize32.ofNatLT n hn := (rfl)

@[simp] theorem USize32.ofBitVec_ofFin (n) : USize32.ofBitVec (BitVec.ofFin n) = USize32.ofFin n := (rfl)

@[simp] theorem BitVec.ofNat_uISize32ToNat (n : USize32) : BitVec.ofNat 32 n.toNat = n.toBitVec :=
  BitVec.eq_of_toNat_eq (by simp)

@[simp] protected theorem USize32.toFin_div (a b : USize32) : (a / b).toFin = a.toFin / b.toFin := (rfl)

@[simp] theorem UInt8.toUSize32_div (a b : UInt8) : (a / b).toUSize32 = a.toUSize32 / b.toUSize32 := (rfl)

@[simp] theorem UInt16.toUSize32_div (a b : UInt16) : (a / b).toUSize32 = a.toUSize32 / b.toUSize32 := (rfl)

@[simp] theorem USize32.toUInt64_div (a b : USize32) : (a / b).toUInt64 = a.toUInt64 / b.toUInt64 := (rfl)

@[simp] theorem USize32.toUSize_div (a b : USize32) : (a / b).toUSize = a.toUSize / b.toUSize := (rfl)

theorem USize32.toUInt8_div (a b : USize32) (ha : a < 256) (hb : b < 256) : (a / b).toUInt8 = a.toUInt8 / b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem USize32.toUInt16_div (a b : USize32) (ha : a < 65536) (hb : b < 65536) : (a / b).toUInt16 = a.toUInt16 / b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem UInt64.toUSize32_div (a b : UInt64) (ha : a < 4294967296) (hb : b < 4294967296) : (a / b).toUSize32 = a.toUSize32 / b.toUSize32 :=
  USize32.toNat.inj (by simpa using Nat.div_mod_eq_mod_div_mod ha hb)

theorem UInt64.toUSize_div (a b : UInt64) (ha : a < 4294967296) (hb : b < 4294967296) : (a / b).toUSize = a.toUSize / b.toUSize :=
  USize.toNat.inj (Nat.div_mod_eq_mod_div_mod (Nat.lt_of_lt_of_le ha USize32.size_le_usizeSize) (Nat.lt_of_lt_of_le hb USize32.size_le_usizeSize))

@[simp] protected theorem USize32.toFin_mod (a b : USize32) : (a % b).toFin = a.toFin % b.toFin := (rfl)

@[simp] theorem UInt8.toUSize32_mod (a b : UInt8) : (a % b).toUSize32 = a.toUSize32 % b.toUSize32 := (rfl)

@[simp] theorem UInt16.toUSize32_mod (a b : UInt16) : (a % b).toUSize32 = a.toUSize32 % b.toUSize32 := (rfl)

@[simp] theorem USize32.toUInt64_mod (a b : USize32) : (a % b).toUInt64 = a.toUInt64 % b.toUInt64 := (rfl)

@[simp] theorem USize32.toUSize_mod (a b : USize32) : (a % b).toUSize = a.toUSize % b.toUSize := (rfl)

theorem USize32.toUInt8_mod (a b : USize32) (ha : a < 256) (hb : b < 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem USize32.toUInt16_mod (a b : USize32) (ha : a < 65536) (hb : b < 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem USize32.toUInt8_mod_of_dvd (a b : USize32) (hb : b.toNat ∣ 256) : (a % b).toUInt8 = a.toUInt8 % b.toUInt8 :=
  UInt8.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem USize32.toUInt16_mod_of_dvd (a b : USize32) (hb : b.toNat ∣ 65536) : (a % b).toUInt16 = a.toUInt16 % b.toUInt16 :=
  UInt16.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem USize.toUSize32_mod (a b : USize) (ha : a < 4294967296) (hb : b < 4294967296) : (a % b).toUSize32 = a.toUSize32 % b.toUSize32 := by
  apply USize32.toNat.inj
  simp only [toNat_toUSize32, USize.toNat_mod, Nat.reducePow, USize32.toNat_mod]
  have := Nat.mod_mod_eq_mod_mod_mod ha hb
  obtain (h|h) := USize.size_eq
  · have ha' := h ▸ a.toNat_lt_size
    have hb' := h ▸ b.toNat_lt_size
    rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha'
  · simp_all

theorem USize.toUSize32_mod_of_dvd (a b : USize) (hb : b.toNat ∣ 4294967296) : (a % b).toUSize32 = a.toUSize32 % b.toUSize32 := by
  apply USize32.toNat.inj
  simp only [toNat_toUSize32, USize.toNat_mod, Nat.reducePow, USize32.toNat_mod]
  have := Nat.mod_mod_eq_mod_mod_mod_of_dvd (a := a.toNat) hb
  obtain (h|h) := USize.size_eq
  · have ha' := h ▸ a.toNat_lt_size
    have hb' := h ▸ b.toNat_lt_size
    rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha'
  · simp_all

theorem UInt64.toUSize32_mod (a b : UInt64) (ha : a < 4294967296) (hb : b < 4294967296) : (a % b).toUSize32 = a.toUSize32 % b.toUSize32 :=
  USize32.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod ha hb)

theorem UInt64.toUSize_mod (a b : UInt64) (ha : a < 4294967296) (hb : b < 4294967296) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (Nat.mod_mod_eq_mod_mod_mod (Nat.lt_of_lt_of_le ha USize32.size_le_usizeSize) (Nat.lt_of_lt_of_le hb USize32.size_le_usizeSize))

theorem UInt64.toUSize32_mod_of_dvd (a b : UInt64) (hb : b.toNat ∣ 4294967296) : (a % b).toUSize32 = a.toUSize32 % b.toUSize32 :=
  USize32.toNat.inj (by simpa using Nat.mod_mod_eq_mod_mod_mod_of_dvd hb)

theorem UInt64.toUSize_mod_of_dvd (a b : UInt64) (hb : b.toNat ∣ 4294967296) : (a % b).toUSize = a.toUSize % b.toUSize :=
  USize.toNat.inj (Nat.mod_mod_eq_mod_mod_mod_of_dvd (Nat.dvd_trans hb USize32.size_dvd_usizeSize))

@[simp] protected theorem USize32.toFin_add (a b : USize32) : (a + b).toFin = a.toFin + b.toFin := (rfl)

@[simp] theorem USize32.toUInt8_add (a b : USize32) : (a + b).toUInt8 = a.toUInt8 + b.toUInt8 := UInt8.toNat.inj (by simp)

@[simp] theorem USize32.toUInt16_add (a b : USize32) : (a + b).toUInt16 = a.toUInt16 + b.toUInt16 := UInt16.toNat.inj (by simp)

@[simp] theorem UInt64.toUSize32_add (a b : UInt64) : (a + b).toUSize32 = a.toUSize32 + b.toUSize32 := USize32.toNat.inj (by simp)

@[simp] theorem USize.toUSize32_add (a b : USize) : (a + b).toUSize32 = a.toUSize32 + b.toUSize32 := USize32.toNat.inj (by simp)

@[simp] theorem UInt8.toUSize32_add (a b : UInt8) : (a + b).toUSize32 = (a.toUSize32 + b.toUSize32) % 256 := USize32.toNat.inj (by simp)

@[simp] theorem UInt16.toUSize32_add (a b : UInt16) : (a + b).toUSize32 = (a.toUSize32 + b.toUSize32) % 65536 := USize32.toNat.inj (by simp)

@[simp] theorem USize32.toUInt64_add (a b : USize32) : (a + b).toUInt64 = (a.toUInt64 + b.toUInt64) % 4294967296 := UInt64.toNat.inj (by simp)

@[simp] theorem USize32.toUSize_add (a b : USize32) : (a + b).toUSize = (a.toUSize + b.toUSize) % 4294967296 :=
  USize.toNat.inj (by cases System.Platform.numBits_eq <;> simp_all [USize.toNat_ofNat])

@[simp] protected theorem USize32.toFin_sub (a b : USize32) : (a - b).toFin = a.toFin - b.toFin := (rfl)

@[simp] protected theorem USize32.toFin_mul (a b : USize32) : (a * b).toFin = a.toFin * b.toFin := (rfl)

@[simp] theorem USize32.toUInt8_mul (a b : USize32) : (a * b).toUInt8 = a.toUInt8 * b.toUInt8 := UInt8.toNat.inj (by simp)

@[simp] theorem USize32.toUInt16_mul (a b : USize32) : (a * b).toUInt16 = a.toUInt16 * b.toUInt16 := UInt16.toNat.inj (by simp)

@[simp] theorem UInt64.toUSize32_mul (a b : UInt64) : (a * b).toUSize32 = a.toUSize32 * b.toUSize32 := USize32.toNat.inj (by simp)

@[simp] theorem USize.toUSize32_mul (a b : USize) : (a * b).toUSize32 = a.toUSize32 * b.toUSize32 := USize32.toNat.inj (by simp)

@[simp] theorem UInt8.toUSize32_mul (a b : UInt8) : (a * b).toUSize32 = (a.toUSize32 * b.toUSize32) % 256 := USize32.toNat.inj (by simp)

@[simp] theorem UInt16.toUSize32_mul (a b : UInt16) : (a * b).toUSize32 = (a.toUSize32 * b.toUSize32) % 65536 := USize32.toNat.inj (by simp)

@[simp] theorem USize32.toUInt64_mul (a b : USize32) : (a * b).toUInt64 = (a.toUInt64 * b.toUInt64) % 4294967296 := UInt64.toNat.inj (by simp)

@[simp] theorem USize32.toUSize_mul (a b : USize32) : (a * b).toUSize = (a.toUSize * b.toUSize) % 4294967296 :=
  USize.toNat.inj (by cases System.Platform.numBits_eq <;> simp_all [USize.toNat_ofNat])

theorem USize32.toUInt8_eq (a b : USize32) : a.toUInt8 = b.toUInt8 ↔ a % 256 = b % 256 := by
  simp [← UInt8.toNat_inj, ← USize32.toNat_inj]

theorem USize32.toUInt16_eq (a b : USize32) : a.toUInt16 = b.toUInt16 ↔ a % 65536 = b % 65536 := by
  simp [← UInt16.toNat_inj, ← USize32.toNat_inj]

theorem UInt64.toUSize32_eq (a b : UInt64) : a.toUSize32 = b.toUSize32 ↔ a % 4294967296 = b % 4294967296 := by
  simp [← USize32.toNat_inj, ← UInt64.toNat_inj]

theorem USize.toUSize32_eq (a b : USize) : a.toUSize32 = b.toUSize32 ↔ a % 4294967296 = b % 4294967296 := by
  simp [← USize32.toNat_inj, ← USize.toNat_inj, USize.toNat_ofNat]
  have := Nat.mod_eq_of_lt a.toNat_lt_two_pow_numBits
  have := Nat.mod_eq_of_lt b.toNat_lt_two_pow_numBits
  cases System.Platform.numBits_eq <;> simp_all [Nat.mod_eq_of_lt]

theorem UInt8.toUSize32_eq_mod_256_iff (a : UInt8) (b : USize32) : a.toUSize32 = b % 256 ↔ a = b.toUInt8 := by
  simp [← UInt8.toNat_inj, ← USize32.toNat_inj]

theorem UInt16.toUSize32_eq_mod_65536_iff (a : UInt16) (b : USize32) : a.toUSize32 = b % 65536 ↔ a = b.toUInt16 := by
  simp [← UInt16.toNat_inj, ← USize32.toNat_inj]

theorem USize32.toUInt64_eq_mod_4294967296_iff (a : USize32) (b : UInt64) : a.toUInt64 = b % 4294967296 ↔ a = b.toUSize32 := by
  simp [← USize32.toNat_inj, ← UInt64.toNat_inj]

theorem USize32.toUSize_eq_mod_4294967296_iff (a : USize32) (b : USize) : a.toUSize = b % 4294967296 ↔ a = b.toUSize32 := by
  simp [← USize32.toNat_inj, ← USize.toNat_inj, USize.toNat_ofNat]
  have := Nat.mod_eq_of_lt b.toNat_lt_two_pow_numBits
  cases System.Platform.numBits_eq <;> simp_all [Nat.mod_eq_of_lt]

theorem UInt8.toUSize32_inj {a b : UInt8} : a.toUSize32 = b.toUSize32 ↔ a = b :=
  ⟨fun h => by rw [← toUInt8_toUSize32 a, h, toUInt8_toUSize32], by rintro rfl; rfl⟩

theorem UInt16.toUSize32_inj {a b : UInt16} : a.toUSize32 = b.toUSize32 ↔ a = b :=
  ⟨fun h => by rw [← toUInt16_toUSize32 a, h, toUInt16_toUSize32], by rintro rfl; rfl⟩

theorem USize32.toUInt64_inj {a b : USize32} : a.toUInt64 = b.toUInt64 ↔ a = b :=
  ⟨fun h => by rw [← toUSize32_toUInt64 a, h, toUSize32_toUInt64], by rintro rfl; rfl⟩

theorem USize32.toUSize_inj {a b : USize32} : a.toUSize = b.toUSize ↔ a = b :=
  ⟨fun h => by rw [← toUSize32_toUSize a, h, toUSize32_toUSize], by rintro rfl; rfl⟩

theorem USize32.lt_iff_toFin_lt {a b : USize32} : a < b ↔ a.toFin < b.toFin := Iff.rfl

theorem USize32.le_iff_toFin_le {a b : USize32} : a ≤ b ↔ a.toFin ≤ b.toFin := Iff.rfl

@[simp] theorem UInt8.toUSize32_lt {a b : UInt8} : a.toUSize32 < b.toUSize32 ↔ a < b := by
  simp [lt_iff_toNat_lt, USize32.lt_iff_toNat_lt]

@[simp] theorem UInt16.toUSize32_lt {a b : UInt16} : a.toUSize32 < b.toUSize32 ↔ a < b := by
  simp [lt_iff_toNat_lt, USize32.lt_iff_toNat_lt]

@[simp] theorem USize32.toUInt64_lt {a b : USize32} : a.toUInt64 < b.toUInt64 ↔ a < b := by
  simp [lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt]

@[simp] theorem USize32.toUSize_lt {a b : USize32} : a.toUSize < b.toUSize ↔ a < b := by
  simp [lt_iff_toNat_lt, USize.lt_iff_toNat_lt]

@[simp] theorem USize32.toUInt8_lt {a b : USize32} : a.toUInt8 < b.toUInt8 ↔ a % 256 < b % 256 := by
  simp [lt_iff_toNat_lt, UInt8.lt_iff_toNat_lt]

@[simp] theorem USize32.toUInt16_lt {a b : USize32} : a.toUInt16 < b.toUInt16 ↔ a % 65536 < b % 65536 := by
  simp [lt_iff_toNat_lt, UInt16.lt_iff_toNat_lt]

@[simp] theorem UInt64.toUSize32_lt {a b : UInt64} : a.toUSize32 < b.toUSize32 ↔ a % 4294967296 < b % 4294967296 := by
  simp [lt_iff_toNat_lt, USize32.lt_iff_toNat_lt]

@[simp] theorem USize.toUSize32_lt {a b : USize} : a.toUSize32 < b.toUSize32 ↔ a % 4294967296 < b % 4294967296 := by
  rw [← USize32.toUSize_lt, toUSize_toUSize32]
  simp [lt_iff_toNat_lt]

@[simp] theorem UInt8.toUSize32_le {a b : UInt8} : a.toUSize32 ≤ b.toUSize32 ↔ a ≤ b := by
  simp [le_iff_toNat_le, USize32.le_iff_toNat_le]

@[simp] theorem UInt16.toUSize32_le {a b : UInt16} : a.toUSize32 ≤ b.toUSize32 ↔ a ≤ b := by
  simp [le_iff_toNat_le, USize32.le_iff_toNat_le]

@[simp] theorem USize32.toUInt64_le {a b : USize32} : a.toUInt64 ≤ b.toUInt64 ↔ a ≤ b := by
  simp [le_iff_toNat_le, UInt64.le_iff_toNat_le]

@[simp] theorem USize32.toUSize_le {a b : USize32} : a.toUSize ≤ b.toUSize ↔ a ≤ b := by
  simp [le_iff_toNat_le, USize.le_iff_toNat_le]

@[simp] theorem USize32.toUInt8_le {a b : USize32} : a.toUInt8 ≤ b.toUInt8 ↔ a % 256 ≤ b % 256 := by
  simp [le_iff_toNat_le, UInt8.le_iff_toNat_le]

@[simp] theorem USize32.toUInt16_le {a b : USize32} : a.toUInt16 ≤ b.toUInt16 ↔ a % 65536 ≤ b % 65536 := by
  simp [le_iff_toNat_le, UInt16.le_iff_toNat_le]

@[simp] theorem UInt64.toUSize32_le {a b : UInt64} : a.toUSize32 ≤ b.toUSize32 ↔ a % 4294967296 ≤ b % 4294967296 := by
  simp [le_iff_toNat_le, USize32.le_iff_toNat_le]

@[simp] theorem USize.toUSize32_le {a b : USize} : a.toUSize32 ≤ b.toUSize32 ↔ a % 4294967296 ≤ b % 4294967296 := by
  rw [← USize32.toUSize_le, toUSize_toUSize32]
  simp [le_iff_toNat_le]

@[simp] theorem USize32.toUInt8_neg (a : USize32) : (-a).toUInt8 = -a.toUInt8 := UInt8.toBitVec_inj.1 (by simp)

@[simp] theorem USize32.toUInt16_neg (a : USize32) : (-a).toUInt16 = -a.toUInt16 := UInt16.toBitVec_inj.1 (by simp)

@[simp] theorem UInt64.toUSize32_neg (a : UInt64) : (-a).toUSize32 = -a.toUSize32 := USize32.toBitVec_inj.1 (by simp)

@[simp] theorem USize.toUSize32_neg (a : USize) : (-a).toUSize32 = -a.toUSize32 := USize32.toBitVec_inj.1 (by simp)

@[simp] theorem UInt8.toUSize32_neg (a : UInt8) : (-a).toUSize32 = -a.toUSize32 % 256 := by
  simp [UInt8.toUSize32_eq_mod_256_iff]

@[simp] theorem UInt16.toUSize32_neg (a : UInt16) : (-a).toUSize32 = -a.toUSize32 % 65536 := by
  simp [UInt16.toUSize32_eq_mod_65536_iff]

@[simp] theorem USize32.toUInt64_neg (a : USize32) : (-a).toUInt64 = -a.toUInt64 % 4294967296 := by
  simp [USize32.toUInt64_eq_mod_4294967296_iff]

@[simp] theorem USize32.toUSize_neg (a : USize32) : (-a).toUSize = -a.toUSize % 4294967296 := by
  simp [USize32.toUSize_eq_mod_4294967296_iff]

@[simp] theorem USize32.toNat_neg (a : USize32) : (-a).toNat = (USize32.size - a.toNat) % USize32.size := (rfl)

protected theorem USize32.sub_eq_add_neg (a b : USize32) : a - b = a + (-b) := USize32.toBitVec_inj.1 (BitVec.sub_eq_add_neg _ _)

protected theorem USize32.add_neg_eq_sub {a b : USize32} : a + -b = a - b := USize32.toBitVec_inj.1 BitVec.add_neg_eq_sub

theorem USize32.neg_one_eq : (-1 : USize32) = 4294967295 := (rfl)

theorem USize32.toBitVec_zero : toBitVec 0 = 0#32 := (rfl)

theorem USize32.toBitVec_one : toBitVec 1 = 1#32 := (rfl)

theorem USize32.neg_eq_neg_one_mul (a : USize32) : -a = -1 * a := by
  apply USize32.toBitVec_inj.1
  rw [USize32.toBitVec_neg, USize32.toBitVec_mul, USize32.toBitVec_neg, USize32.toBitVec_one, BitVec.neg_eq_neg_one_mul]

theorem USize32.sub_eq_add_mul (a b : USize32) : a - b = a + 4294967295 * b := by
  rw [USize32.sub_eq_add_neg, neg_eq_neg_one_mul, neg_one_eq]

@[simp] theorem USize32.ofNat_usizeSize_sub_one : USize32.ofNat (USize.size - 1) = 4294967295 := USize32.toNat.inj (by simp)

@[simp] theorem USize32.toUInt8_sub (a b : USize32) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := by
  simp [USize32.sub_eq_add_neg, UInt8.sub_eq_add_neg]

@[simp] theorem USize32.toUInt16_sub (a b : USize32) : (a - b).toUInt16 = a.toUInt16 - b.toUInt16 := by
  simp [USize32.sub_eq_add_neg, UInt16.sub_eq_add_neg]

@[simp] theorem UInt64.toUSize32_sub (a b : UInt64) : (a - b).toUSize32 = a.toUSize32 - b.toUSize32 := by
  simp [UInt64.sub_eq_add_neg, USize32.sub_eq_add_neg]

@[simp] theorem USize.toUSize32_sub (a b : USize) : (a - b).toUSize32 = a.toUSize32 - b.toUSize32 := by
  simp [USize.sub_eq_add_neg, USize32.sub_eq_add_neg]

@[simp] theorem UInt8.toUSize32_sub (a b : UInt8) : (a - b).toUSize32 = (a.toUSize32 - b.toUSize32) % 256 := by
  simp [UInt8.toUSize32_eq_mod_256_iff]

@[simp] theorem UInt16.toUSize32_sub (a b : UInt16) : (a - b).toUSize32 = (a.toUSize32 - b.toUSize32) % 65536 := by
  simp [UInt16.toUSize32_eq_mod_65536_iff]

@[simp] theorem USize32.toUInt64_sub (a b : USize32) : (a - b).toUInt64 = (a.toUInt64 - b.toUInt64) % 4294967296 := by
  simp [USize32.toUInt64_eq_mod_4294967296_iff]

@[simp] theorem USize32.toUSize_sub (a b : USize32) : (a - b).toUSize = (a.toUSize - b.toUSize) % 4294967296 := by
  simp [USize32.toUSize_eq_mod_4294967296_iff]

@[simp] theorem USize32.ofBitVec_neg (b : BitVec 32) : USize32.ofBitVec (-b) = -USize32.ofBitVec b := (rfl)

@[simp] theorem USize32.ofFin_div (a b : Fin USize32.size) : USize32.ofFin (a / b) = USize32.ofFin a / USize32.ofFin b := (rfl)

@[simp] theorem USize32.ofBitVec_div (a b : BitVec 32) : USize32.ofBitVec (a / b) = USize32.ofBitVec a / USize32.ofBitVec b := (rfl)

@[simp] theorem USize32.ofFin_mod (a b : Fin USize32.size) : USize32.ofFin (a % b) = USize32.ofFin a % USize32.ofFin b := (rfl)

@[simp] theorem USize32.ofBitVec_mod (a b : BitVec 32) : USize32.ofBitVec (a % b) = USize32.ofBitVec a % USize32.ofBitVec b := (rfl)

theorem USize32.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : USize32) : USize32.ofNat a = b ↔ a % 2 ^ 32 = b.toNat := by
  simp [← USize32.toNat_inj]

@[simp] theorem USize32.ofNat_div {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    USize32.ofNat (a / b) = USize32.ofNat a / USize32.ofNat b := by
  simp [USize32.ofNat_eq_iff_mod_eq_toNat, Nat.div_mod_eq_mod_div_mod ha hb]

@[simp] theorem USize32.ofNatLT_div {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    USize32.ofNatLT (a / b) (Nat.div_lt_of_lt ha) = USize32.ofNatLT a ha / USize32.ofNatLT b hb := by
  simp [USize32.ofNatLT_eq_ofNat, USize32.ofNat_div ha hb]

@[simp] theorem USize32.ofNat_mod {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    USize32.ofNat (a % b) = USize32.ofNat a % USize32.ofNat b := by
  simp [USize32.ofNat_eq_iff_mod_eq_toNat, Nat.mod_mod_eq_mod_mod_mod ha hb]

@[simp] theorem USize32.ofNatLT_mod {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    USize32.ofNatLT (a % b) (Nat.mod_lt_of_lt ha) = USize32.ofNatLT a ha % USize32.ofNatLT b hb := by
  simp [USize32.ofNatLT_eq_ofNat, USize32.ofNat_mod ha hb]

@[simp] theorem USize32.ofInt_one : ofInt 1 = 1 := (rfl)

@[simp] theorem USize32.ofInt_neg_one : ofInt (-1) = -1 := (rfl)

@[simp] theorem USize32.ofNat_add (a b : Nat) : USize32.ofNat (a + b) = USize32.ofNat a + USize32.ofNat b := by
  simp [USize32.ofNat_eq_iff_mod_eq_toNat]

@[simp] theorem USize32.ofInt_add (x y : Int) : USize32.ofInt (x + y) = USize32.ofInt x + USize32.ofInt y := by
  dsimp only [USize32.ofInt]
  rw [Int.add_emod]
  have h₁ : 0 ≤ x % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ x % 2 ^ 32 + y % 2 ^ 32 := Int.add_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_add h₁ h₂]
  have : (2 ^ 32 : Int).toNat = 2 ^ 32 := (rfl)
  rw [this, USize32.ofNat_mod_size, USize32.ofNat_add]

@[simp] theorem USize32.ofNatLT_add {a b : Nat} (hab : a + b < 2 ^ 32) :
    USize32.ofNatLT (a + b) hab = USize32.ofNatLT a (Nat.lt_of_add_right_lt hab) + USize32.ofNatLT b (Nat.lt_of_add_left_lt hab) := by
  simp [USize32.ofNatLT_eq_ofNat]

@[simp] theorem USize32.ofFin_add (a b : Fin USize32.size) : USize32.ofFin (a + b) = USize32.ofFin a + USize32.ofFin b := (rfl)

@[simp] theorem USize32.ofBitVec_add (a b : BitVec 32) : USize32.ofBitVec (a + b) = USize32.ofBitVec a + USize32.ofBitVec b := (rfl)

@[simp] theorem USize32.ofFin_sub (a b : Fin USize32.size) : USize32.ofFin (a - b) = USize32.ofFin a - USize32.ofFin b := (rfl)

@[simp] theorem USize32.ofBitVec_sub (a b : BitVec 32) : USize32.ofBitVec (a - b) = USize32.ofBitVec a - USize32.ofBitVec b := (rfl)

@[simp] protected theorem USize32.add_sub_cancel (a b : USize32) : a + b - b = a := USize32.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)

theorem USize32.ofNat_sub {a b : Nat} (hab : b ≤ a) : USize32.ofNat (a - b) = USize32.ofNat a - USize32.ofNat b := by
  rw [(Nat.sub_add_cancel hab ▸ USize32.ofNat_add (a - b) b :), USize32.add_sub_cancel]

theorem USize32.ofNatLT_sub {a b : Nat} (ha : a < 2 ^ 32) (hab : b ≤ a) :
    USize32.ofNatLT (a - b) (Nat.sub_lt_of_lt ha) = USize32.ofNatLT a ha - USize32.ofNatLT b (Nat.lt_of_le_of_lt hab ha) := by
  simp [USize32.ofNatLT_eq_ofNat, USize32.ofNat_sub hab]

@[simp] theorem USize32.ofNat_mul (a b : Nat) : USize32.ofNat (a * b) = USize32.ofNat a * USize32.ofNat b := by
  simp [USize32.ofNat_eq_iff_mod_eq_toNat]

@[simp] theorem USize32.ofInt_mul (x y : Int) : ofInt (x * y) = ofInt x * ofInt y := by
  dsimp only [USize32.ofInt]
  rw [Int.mul_emod]
  have h₁ : 0 ≤ x % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ (x % 2 ^ 32) * (y % 2 ^ 32) := Int.mul_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_mul h₁ h₂]
  have : (2 ^ 32 : Int).toNat = 2 ^ 32 := (rfl)
  rw [this, USize32.ofNat_mod_size, USize32.ofNat_mul]

@[simp] theorem USize32.ofNatLT_mul {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hab : a * b < 2 ^ 32) :
    USize32.ofNatLT (a * b) hab = USize32.ofNatLT a ha * USize32.ofNatLT b hb := by
  simp [USize32.ofNatLT_eq_ofNat]

@[simp] theorem USize32.ofFin_mul (a b : Fin USize32.size) : USize32.ofFin (a * b) = USize32.ofFin a * USize32.ofFin b := (rfl)

@[simp] theorem USize32.ofBitVec_mul (a b : BitVec 32) : USize32.ofBitVec (a * b) = USize32.ofBitVec a * USize32.ofBitVec b := (rfl)

theorem USize32.ofFin_lt_iff_lt {a b : Fin USize32.size} : USize32.ofFin a < USize32.ofFin b ↔ a < b := Iff.rfl

theorem USize32.ofFin_le_iff_le {a b : Fin USize32.size} : USize32.ofFin a ≤ USize32.ofFin b ↔ a ≤ b := Iff.rfl

theorem USize32.ofBitVec_lt_iff_lt {a b : BitVec 32} : USize32.ofBitVec a < USize32.ofBitVec b ↔ a < b := Iff.rfl

theorem USize32.ofBitVec_le_iff_le {a b : BitVec 32} : USize32.ofBitVec a ≤ USize32.ofBitVec b ↔ a ≤ b := Iff.rfl

theorem USize32.ofNatLT_lt_iff_lt {a b : Nat} (ha : a < USize32.size) (hb : b < USize32.size) :
    USize32.ofNatLT a ha < USize32.ofNatLT b hb ↔ a < b := Iff.rfl

theorem USize32.ofNatLT_le_iff_le {a b : Nat} (ha : a < USize32.size) (hb : b < USize32.size) :
    USize32.ofNatLT a ha ≤ USize32.ofNatLT b hb ↔ a ≤ b := Iff.rfl

theorem USize32.ofNat_lt_iff_lt {a b : Nat} (ha : a < USize32.size) (hb : b < USize32.size) :
    USize32.ofNat a < USize32.ofNat b ↔ a < b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_lt_iff_lt]

theorem USize32.ofNat_le_iff_le {a b : Nat} (ha : a < USize32.size) (hb : b < USize32.size) :
    USize32.ofNat a ≤ USize32.ofNat b ↔ a ≤ b := by
  rw [← ofNatLT_eq_ofNat (h := ha), ← ofNatLT_eq_ofNat (h := hb), ofNatLT_le_iff_le]

theorem USize32.toNat_one : (1 : USize32).toNat = 1 := (rfl)

theorem USize32.zero_lt_one : (0 : USize32) < 1 := by simp

theorem USize32.zero_ne_one : (0 : USize32) ≠ 1 := by simp

protected theorem USize32.add_assoc (a b c : USize32) : a + b + c = a + (b + c) :=
  USize32.toBitVec_inj.1 (BitVec.add_assoc _ _ _)

instance : Std.Associative (α := USize32) (· + ·) := ⟨USize32.add_assoc⟩

protected theorem USize32.add_comm (a b : USize32) : a + b = b + a := USize32.toBitVec_inj.1 (BitVec.add_comm _ _)

instance : Std.Commutative (α := USize32) (· + ·) := ⟨USize32.add_comm⟩

@[simp] protected theorem USize32.add_zero (a : USize32) : a + 0 = a := USize32.toBitVec_inj.1 (BitVec.add_zero _)

@[simp] protected theorem USize32.zero_add (a : USize32) : 0 + a = a := USize32.toBitVec_inj.1 (BitVec.zero_add _)

instance : Std.LawfulIdentity (α := USize32) (· + ·) 0 where
  left_id := USize32.zero_add
  right_id := USize32.add_zero

@[simp] protected theorem USize32.sub_zero (a : USize32) : a - 0 = a := USize32.toBitVec_inj.1 (BitVec.sub_zero _)

@[simp] protected theorem USize32.zero_sub (a : USize32) : 0 - a = -a := USize32.toBitVec_inj.1 (BitVec.zero_sub _)

@[simp] protected theorem USize32.sub_self (a : USize32) : a - a = 0 := USize32.toBitVec_inj.1 (BitVec.sub_self _)

protected theorem USize32.add_left_neg (a : USize32) : -a + a = 0 := USize32.toBitVec_inj.1 (BitVec.add_left_neg _)

protected theorem USize32.add_right_neg (a : USize32) : a + -a = 0 := USize32.toBitVec_inj.1 (BitVec.add_right_neg _)

@[simp] protected theorem USize32.neg_zero : -(0 : USize32) = 0 := (rfl)

@[simp] protected theorem USize32.sub_add_cancel (a b : USize32) : a - b + b = a :=
  USize32.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)

protected theorem USize32.eq_sub_iff_add_eq {a b c : USize32} : a = c - b ↔ a + b = c := by
  simpa [← USize32.toBitVec_inj] using BitVec.eq_sub_iff_add_eq

protected theorem USize32.sub_eq_iff_eq_add {a b c : USize32} : a - b = c ↔ a = c + b := by
  simpa [← USize32.toBitVec_inj] using BitVec.sub_eq_iff_eq_add

@[simp] protected theorem USize32.neg_neg {a : USize32} : - -a = a := USize32.toBitVec_inj.1 BitVec.neg_neg

@[simp] protected theorem USize32.neg_inj {a b : USize32} : -a = -b ↔ a = b := by simp [← USize32.toBitVec_inj]
@[simp] protected theorem UInt64.neg_inj {a b : UInt64} : -a = -b ↔ a = b := by simp [← UInt64.toBitVec_inj]

@[simp] protected theorem USize32.neg_ne_zero {a : USize32} : -a ≠ 0 ↔ a ≠ 0 := by simp [← USize32.toBitVec_inj]
@[simp] protected theorem UInt64.neg_ne_zero {a : UInt64} : -a ≠ 0 ↔ a ≠ 0 := by simp [← UInt64.toBitVec_inj]

protected theorem USize32.neg_add {a b : USize32} : - (a + b) = -a - b := USize32.toBitVec_inj.1 BitVec.neg_add

@[simp] protected theorem USize32.sub_neg {a b : USize32} : a - -b = a + b := USize32.toBitVec_inj.1 BitVec.sub_neg

@[simp] protected theorem USize32.neg_sub {a b : USize32} : -(a - b) = b - a := by
  rw [USize32.sub_eq_add_neg, USize32.neg_add, USize32.sub_neg, USize32.add_comm, ← USize32.sub_eq_add_neg]

@[simp] protected theorem USize32.ofInt_neg (x : Int) : ofInt (-x) = -ofInt x := by
  rw [Int.neg_eq_neg_one_mul, ofInt_mul, ofInt_neg_one, ← USize32.neg_eq_neg_one_mul]

@[simp] protected theorem USize32.add_left_inj {a b : USize32} (c : USize32) : (a + c = b + c) ↔ a = b := by
  simp [← USize32.toBitVec_inj]

@[simp] protected theorem USize32.add_right_inj {a b : USize32} (c : USize32) : (c + a = c + b) ↔ a = b := by
  simp [← USize32.toBitVec_inj]

@[simp] protected theorem USize32.sub_left_inj {a b : USize32} (c : USize32) : (a - c = b - c) ↔ a = b := by
  simp [← USize32.toBitVec_inj]

@[simp] protected theorem USize32.sub_right_inj {a b : USize32} (c : USize32) : (c - a = c - b) ↔ a = b := by
  simp [← USize32.toBitVec_inj]

@[simp] theorem USize32.add_eq_right {a b : USize32} : a + b = b ↔ a = 0 := by
  simp [← USize32.toBitVec_inj]

@[simp] theorem USize32.add_eq_left {a b : USize32} : a + b = a ↔ b = 0 := by
  simp [← USize32.toBitVec_inj]

@[simp] theorem USize32.right_eq_add {a b : USize32} : b = a + b ↔ a = 0 := by
  simp [← USize32.toBitVec_inj]

@[simp] theorem USize32.left_eq_add {a b : USize32} : a = a + b ↔ b = 0 := by
  simp [← USize32.toBitVec_inj]

protected theorem USize32.mul_comm (a b : USize32) : a * b = b * a := USize32.toBitVec_inj.1 (BitVec.mul_comm _ _)

instance : Std.Commutative (α := USize32) (· * ·) := ⟨USize32.mul_comm⟩

protected theorem USize32.mul_assoc (a b c : USize32) : a * b * c = a * (b * c) := USize32.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)

instance : Std.Associative (α := USize32) (· * ·) := ⟨USize32.mul_assoc⟩

@[simp] theorem USize32.mul_one (a : USize32) : a * 1 = a := USize32.toBitVec_inj.1 (BitVec.mul_one _)

@[simp] theorem USize32.one_mul (a : USize32) : 1 * a = a := USize32.toBitVec_inj.1 (BitVec.one_mul _)

instance : Std.LawfulCommIdentity (α := USize32) (· * ·) 1 where
  right_id := USize32.mul_one

@[simp] theorem USize32.mul_zero {a : USize32} : a * 0 = 0 := USize32.toBitVec_inj.1 BitVec.mul_zero

@[simp] theorem USize32.zero_mul {a : USize32} : 0 * a = 0 := USize32.toBitVec_inj.1 BitVec.zero_mul

@[simp] protected theorem USize32.pow_zero (x : USize32) : x ^ 0 = 1 := (rfl)

protected theorem USize32.pow_succ (x : USize32) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)

@[simp, int_toBitVec] protected theorem USize32.toBitVec_pow (a : USize32) (n : Nat) : (a ^ n).toBitVec = a.toBitVec ^ n := by
  induction n <;> simp [*, USize32.pow_succ, BitVec.pow_succ]

@[simp] protected theorem USize32.ofBitVec_pow (a : BitVec 32) (n : Nat) : ofBitVec (a ^ n) = ofBitVec a ^ n := by
  induction n <;> simp [*, USize32.pow_succ, BitVec.pow_succ]

protected theorem USize32.mul_add {a b c : USize32} : a * (b + c) = a * b + a * c :=
    USize32.toBitVec_inj.1 BitVec.mul_add

protected theorem USize32.add_mul {a b c : USize32} : (a + b) * c = a * c + b * c := by
  rw [USize32.mul_comm, USize32.mul_add, USize32.mul_comm a c, USize32.mul_comm c b]

protected theorem USize32.mul_succ {a b : USize32} : a * (b + 1) = a * b + a := by simp [USize32.mul_add]

protected theorem USize32.succ_mul {a b : USize32} : (a + 1) * b = a * b + b := by simp [USize32.add_mul]

protected theorem USize32.two_mul {a : USize32} : 2 * a = a + a := USize32.toBitVec_inj.1 BitVec.two_mul

protected theorem USize32.mul_two {a : USize32} : a * 2 = a + a := USize32.toBitVec_inj.1 BitVec.mul_two

protected theorem USize32.neg_mul (a b : USize32) : -a * b = -(a * b) := USize32.toBitVec_inj.1 (BitVec.neg_mul _ _)

protected theorem USize32.mul_neg (a b : USize32) : a * -b = -(a * b) := USize32.toBitVec_inj.1 (BitVec.mul_neg _ _)

protected theorem USize32.neg_mul_neg (a b : USize32) : -a * -b = a * b := USize32.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)

protected theorem USize32.neg_mul_comm (a b : USize32) : -a * b = a * -b := USize32.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)

protected theorem USize32.mul_sub {a b c : USize32} : a * (b - c) = a * b - a * c := USize32.toBitVec_inj.1 BitVec.mul_sub

protected theorem USize32.sub_mul {a b c : USize32} : (a - b) * c = a * c - b * c := by
  rw [USize32.mul_comm, USize32.mul_sub, USize32.mul_comm, USize32.mul_comm c]

theorem USize32.neg_add_mul_eq_mul_not {a b : USize32} : -(a + a * b) = a * ~~~b :=
  USize32.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not

theorem USize32.neg_mul_not_eq_add_mul {a b : USize32} : -(a * ~~~b) = a + a * b :=
  USize32.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul

protected theorem USize32.le_of_lt {a b : USize32} : a < b → a ≤ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le] using Nat.le_of_lt

protected theorem USize32.lt_of_le_of_ne {a b : USize32} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← USize32.toNat_inj] using Nat.lt_of_le_of_ne

protected theorem USize32.lt_iff_le_and_ne {a b : USize32} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toNat_lt, le_iff_toNat_le, ← USize32.toNat_inj] using Nat.lt_iff_le_and_ne

@[simp] protected theorem USize32.not_lt_zero {a : USize32} : ¬a < 0 := by simp [USize32.lt_iff_toBitVec_lt]
@[simp] protected theorem UInt64.not_lt_zero {a : UInt64} : ¬a < 0 := by simp [UInt64.lt_iff_toBitVec_lt]

@[simp] protected theorem USize32.zero_le {a : USize32} : 0 ≤ a := by simp [← USize32.not_lt]
@[simp] protected theorem UInt64.zero_le {a : UInt64} : 0 ≤ a := by simp [← UInt64.not_lt]

@[simp] protected theorem USize32.le_zero_iff {a : USize32} : a ≤ 0 ↔ a = 0 := by
  simp [USize32.le_iff_toBitVec_le, ← USize32.toBitVec_inj]

@[simp] protected theorem USize32.lt_one_iff {a : USize32} : a < 1 ↔ a = 0 := by
  simp [USize32.lt_iff_toBitVec_lt, ← USize32.toBitVec_inj]

@[simp] protected theorem USize32.zero_div {a : USize32} : 0 / a = 0 := USize32.toBitVec_inj.1 BitVec.zero_udiv

@[simp] protected theorem USize32.div_zero {a : USize32} : a / 0 = 0 := USize32.toBitVec_inj.1 BitVec.udiv_zero

@[simp] protected theorem USize32.div_one {a : USize32} : a / 1 = a := USize32.toBitVec_inj.1 BitVec.udiv_one

protected theorem USize32.div_self {a : USize32} : a / a = if a = 0 then 0 else 1 := by
  simp [← USize32.toBitVec_inj, apply_ite]

@[simp] protected theorem USize32.mod_zero {a : USize32} : a % 0 = a := USize32.toBitVec_inj.1 BitVec.umod_zero

@[simp] protected theorem USize32.zero_mod {a : USize32} : 0 % a = 0 := USize32.toBitVec_inj.1 BitVec.zero_umod

@[simp] protected theorem USize32.mod_one {a : USize32} : a % 1 = 0 := USize32.toBitVec_inj.1 BitVec.umod_one

@[simp] protected theorem USize32.mod_self {a : USize32} : a % a = 0 := USize32.toBitVec_inj.1 BitVec.umod_self

protected theorem USize32.pos_iff_ne_zero {a : USize32} : 0 < a ↔ a ≠ 0 := by simp [USize32.lt_iff_le_and_ne, Eq.comm]

protected theorem USize32.lt_of_le_of_lt {a b c : USize32} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_le_of_lt

protected theorem USize32.lt_of_lt_of_le {a b c : USize32} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toNat_le, lt_iff_toNat_lt] using Nat.lt_of_lt_of_le

protected theorem USize32.lt_or_lt_of_ne {a b : USize32} : a ≠ b → a < b ∨ b < a := by
  simpa [lt_iff_toNat_lt, ← USize32.toNat_inj] using Nat.lt_or_lt_of_ne

protected theorem USize32.lt_or_le (a b : USize32) : a < b ∨ b ≤ a := by
  simp [lt_iff_toNat_lt, le_iff_toNat_le]; omega

protected theorem USize32.le_or_lt (a b : USize32) : a ≤ b ∨ b < a := (b.lt_or_le a).symm

protected theorem USize32.le_of_eq {a b : USize32} : a = b → a ≤ b := (· ▸ USize32.le_rfl)

protected theorem USize32.le_iff_lt_or_eq {a b : USize32} : a ≤ b ↔ a < b ∨ a = b := by
  simpa [← USize32.toNat_inj, le_iff_toNat_le, lt_iff_toNat_lt] using Nat.le_iff_lt_or_eq

protected theorem USize32.lt_or_eq_of_le {a b : USize32} : a ≤ b → a < b ∨ a = b := USize32.le_iff_lt_or_eq.mp

protected theorem USize32.sub_le {a b : USize32} (hab : b ≤ a) : a - b ≤ a := by
  simp [le_iff_toNat_le, USize32.toNat_sub_of_le _ _ hab]

protected theorem USize32.sub_lt {a b : USize32} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  rw [lt_iff_toNat_lt, USize32.toNat_sub_of_le _ _ hab]
  refine Nat.sub_lt ?_ (USize32.lt_iff_toNat_lt.1 hb)
  exact USize32.lt_iff_toNat_lt.1 (USize32.lt_of_lt_of_le hb hab)

theorem USize32.lt_add_one {c : USize32} (h : c ≠ -1) : c < c + 1 :=
  USize32.lt_iff_toBitVec_lt.2 (BitVec.lt_add_one (by simpa [← USize32.toBitVec_inj] using h))

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/Data/SInt/Lemmas.lean
-- Target: Hax/MissingLean/Init/Data/SInt/Lemmas_Int128.lean
-- ──────────────────────────────────────────────────────────────────────

set_option maxRecDepth 4000

declare_int_theorems ISize32 32

theorem ISize32.toInt.inj {x y : ISize32} (h : x.toInt = y.toInt) : x = y := ISize32.toBitVec.inj (BitVec.eq_of_toInt_eq h)

theorem ISize32.toInt_inj {x y : ISize32} : x.toInt = y.toInt ↔ x = y := ⟨ISize32.toInt.inj, fun h => h ▸ rfl⟩

@[simp, int_toBitVec] theorem ISize32.toBitVec_neg (x : ISize32) : (-x).toBitVec = -x.toBitVec := (rfl)

@[simp] theorem ISize32.toBitVec_zero : toBitVec 0 = 0#32 := (rfl)

theorem ISize32.toBitVec_one : (1 : ISize32).toBitVec = 1#32 := (rfl)

@[simp, int_toBitVec] theorem ISize32.toBitVec_ofInt (i : Int) : (ofInt i).toBitVec = BitVec.ofInt _ i := (rfl)

@[simp] protected theorem ISize32.neg_zero : -(0 : ISize32) = 0 := (rfl)

@[simp] theorem ISize32.toInt_ofInt {n : Int} : toInt (ofInt n) = n.bmod ISize32.size := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt]

@[simp] theorem ISize32.toInt_ofNat' {n : Nat} : toInt (ofNat n) = (n : Int).bmod ISize32.size := by
  rw [toInt, toBitVec_ofNat', BitVec.toInt_ofNat']

theorem ISize32.toInt_ofNat {n : Nat} : toInt (no_index (OfNat.ofNat n)) = (n : Int).bmod ISize32.size := by
  rw [toInt, toBitVec_ofNat, BitVec.toInt_ofNat]

theorem ISize32.toInt_ofInt_of_le {n : Int} (hn : -2^31 ≤ n) (hn' : n < 2^31) : toInt (ofInt n) = n := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt_eq_self (by decide) hn hn']

theorem ISize32.neg_ofInt {n : Int} : -ofInt n = ofInt (-n) :=
  toBitVec.inj (by simp [BitVec.ofInt_neg])

theorem ISize32.ofInt_eq_ofNat {n : Nat} : ofInt n = ofNat n := toBitVec.inj (by simp)

theorem ISize32.neg_ofNat {n : Nat} : -ofNat n = ofInt (-n) := by
  rw [← neg_ofInt, ofInt_eq_ofNat]

theorem ISize32.toNatClampNeg_ofNat_of_lt {n : Nat} (h : n < 2 ^ 31) : toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, ← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega), Int.toNat_natCast]

theorem ISize32.toInt_ofNat_of_lt {n : Nat} (h : n < 2 ^ 31) : toInt (ofNat n) = n := by
  rw [← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega)]

theorem ISize32.toInt_zero : toInt 0 = 0 := by simp

theorem ISize32.toInt_minValue : ISize32.minValue.toInt = -2^31 := (rfl)

theorem ISize32.toInt_maxValue : ISize32.maxValue.toInt = 2 ^ 31 - 1 := (rfl)

@[simp] theorem ISize32.toNatClampNeg_minValue : ISize32.minValue.toNatClampNeg = 0 := (rfl)

@[simp, int_toBitVec] theorem USize32.toBitVec_toISize32 (x : USize32) : x.toISize32.toBitVec = x.toBitVec := (rfl)

@[simp] theorem ISize32.ofBitVec_uISize32ToBitVec (x : USize32) : ISize32.ofBitVec x.toBitVec = x.toISize32 := (rfl)

@[simp] theorem USize32.toUSize32_toISize32 (x : USize32) : x.toISize32.toUSize32 = x := (rfl)

@[simp] theorem ISize32.toNat_toInt (x : ISize32) : x.toInt.toNat = x.toNatClampNeg := (rfl)

@[simp] theorem ISize32.toInt_toBitVec (x : ISize32) : x.toBitVec.toInt = x.toInt := (rfl)

@[simp, int_toBitVec] theorem Int8.toBitVec_toISize32 (x : Int8) : x.toISize32.toBitVec = x.toBitVec.signExtend 32 := (rfl)

@[simp, int_toBitVec] theorem Int16.toBitVec_toISize32 (x : Int16) : x.toISize32.toBitVec = x.toBitVec.signExtend 32 := (rfl)

@[simp, int_toBitVec] theorem ISize32.toBitVec_toInt8 (x : ISize32) : x.toInt8.toBitVec = x.toBitVec.signExtend 8 := (rfl)

@[simp, int_toBitVec] theorem ISize32.toBitVec_toInt16 (x : ISize32) : x.toInt16.toBitVec = x.toBitVec.signExtend 16 := (rfl)

@[simp, int_toBitVec] theorem ISize32.toBitVec_toInt64 (x : ISize32) : x.toInt64.toBitVec = x.toBitVec.signExtend 64 := (rfl)

@[simp, int_toBitVec] theorem ISize32.toBitVec_toISize (x : ISize32) : x.toISize.toBitVec = x.toBitVec.signExtend System.Platform.numBits := (rfl)

@[simp, int_toBitVec] theorem Int64.toBitVec_toISize32 (x : Int64) : x.toISize32.toBitVec = x.toBitVec.signExtend 32 := (rfl)

@[simp, int_toBitVec] theorem ISize.toBitVec_toISize32 (x : ISize) : x.toISize32.toBitVec = x.toBitVec.signExtend 32 := (rfl)

theorem ISize32.toInt_lt (x : ISize32) : x.toInt < 2 ^ 31 := Int.lt_of_mul_lt_mul_left BitVec.two_mul_toInt_lt (by decide)

theorem ISize32.le_toInt (x : ISize32) : -2 ^ 31 ≤ x.toInt := Int.le_of_mul_le_mul_left BitVec.le_two_mul_toInt (by decide)

theorem ISize32.toInt_le (x : ISize32) : x.toInt ≤ ISize32.maxValue.toInt := Int.le_of_lt_add_one x.toInt_lt

theorem ISize32.minValue_le_toInt (x : ISize32) : ISize32.minValue.toInt ≤ x.toInt := x.le_toInt

theorem ISize32.iSizeMinValue_le_toInt (x : ISize32) : ISize.minValue.toInt ≤ x.toInt :=
  Int.le_trans (Int.le_trans ISize.toInt_minValue_le (by decide)) x.le_toInt

theorem ISize32.toInt_le_iSizeMaxValue (x : ISize32) : x.toInt ≤ ISize.maxValue.toInt :=
  Int.le_trans x.toInt_le (Int.le_trans (by decide) ISize.le_toInt_maxValue)

theorem ISize32.toNatClampNeg_lt (x : ISize32) : x.toNatClampNeg < 2 ^ 31 := (Int.toNat_lt' (by decide)).2 x.toInt_lt

@[simp] theorem Int8.toInt_toISize32 (x : Int8) : x.toISize32.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)

@[simp] theorem Int16.toInt_toISize32 (x : Int16) : x.toISize32.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)

@[simp] theorem ISize32.toInt_toInt8 (x : ISize32) : x.toInt8.toInt = x.toInt.bmod (2 ^ 8) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)

@[simp] theorem ISize32.toInt_toInt16 (x : ISize32) : x.toInt16.toInt = x.toInt.bmod (2 ^ 16) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)

@[simp] theorem ISize32.toInt_toInt64 (x : ISize32) : x.toInt64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)

@[simp] theorem ISize32.toInt_toISize (x : ISize32) : x.toISize.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem Int64.toInt_toISize32 (x : Int64) : x.toISize32.toInt = x.toInt.bmod (2 ^ 32) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)

@[simp] theorem ISize.toInt_toISize32 (x : ISize) : x.toISize32.toInt = x.toInt.bmod (2 ^ 32) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem Int8.toNatClampNeg_toISize32 (x : Int8) : x.toISize32.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toISize32

@[simp] theorem Int16.toNatClampNeg_toISize32 (x : Int16) : x.toISize32.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toISize32

@[simp] theorem ISize32.toNatClampNeg_toInt64 (x : ISize32) : x.toInt64.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt64

@[simp] theorem ISize32.toNatClampNeg_toISize (x : ISize32) : x.toISize.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toISize

@[simp] theorem ISize32.toISize32_toUSize32 (x : ISize32) : x.toUSize32.toISize32 = x := (rfl)

theorem ISize32.toNat_toBitVec (x : ISize32) : x.toBitVec.toNat = x.toUSize32.toNat := (rfl)

theorem ISize32.toNat_toBitVec_of_le {x : ISize32} (hx : 0 ≤ x) : x.toBitVec.toNat = x.toNatClampNeg :=
  (x.toBitVec.toNat_toInt_of_sle hx).symm

theorem ISize32.toNat_toUSize32_of_le {x : ISize32} (hx : 0 ≤ x) : x.toUSize32.toNat = x.toNatClampNeg := by
  rw [← toNat_toBitVec, toNat_toBitVec_of_le hx]

theorem ISize32.toFin_toBitVec (x : ISize32) : x.toBitVec.toFin = x.toUSize32.toFin := (rfl)

@[simp, int_toBitVec] theorem ISize32.toBitVec_toUSize32 (x : ISize32) : x.toUSize32.toBitVec = x.toBitVec := (rfl)

@[simp] theorem USize32.ofBitVec_isize32ToBitVec (x : ISize32) : USize32.ofBitVec x.toBitVec = x.toUSize32 := (rfl)

@[simp] theorem ISize32.ofBitVec_toBitVec (x : ISize32) : ISize32.ofBitVec x.toBitVec = x := (rfl)

@[simp] theorem Int8.ofBitVec_isize32ToBitVec (x : ISize32) : Int8.ofBitVec (x.toBitVec.signExtend 8) = x.toInt8 := (rfl)

@[simp] theorem Int16.ofBitVec_isize32ToBitVec (x : ISize32) : Int16.ofBitVec (x.toBitVec.signExtend 16) = x.toInt16 := (rfl)

@[simp] theorem ISize32.ofBitVec_int8ToBitVec (x : Int8) : ISize32.ofBitVec (x.toBitVec.signExtend 32) = x.toISize32 := (rfl)

@[simp] theorem ISize32.ofBitVec_int16ToBitVec (x : Int16) : ISize32.ofBitVec (x.toBitVec.signExtend 32) = x.toISize32 := (rfl)

@[simp] theorem ISize32.ofBitVec_int64ToBitVec (x : Int64) : ISize32.ofBitVec (x.toBitVec.signExtend 32) = x.toISize32 := (rfl)

@[simp] theorem ISize32.ofBitVec_iSizeToBitVec (x : ISize) : ISize32.ofBitVec (x.toBitVec.signExtend 32) = x.toISize32 := (rfl)

@[simp] theorem Int64.ofBitVec_isize32ToBitVec (x : ISize32) : Int64.ofBitVec (x.toBitVec.signExtend 64) = x.toInt64 := (rfl)

@[simp] theorem ISize.ofBitVec_isize32ToBitVec (x : ISize32) : ISize.ofBitVec (x.toBitVec.signExtend System.Platform.numBits) = x.toISize := (rfl)

@[simp] theorem ISize32.toBitVec_ofIntLE (x : Int) (h₁ h₂) : (ISize32.ofIntLE x h₁ h₂).toBitVec = BitVec.ofInt 32 x := (rfl)

@[simp] theorem ISize32.toInt_bmod (x : ISize32) : x.toInt.bmod 4294967296 = x.toInt := Int.bmod_eq_of_le x.le_toInt x.toInt_lt

@[simp] theorem ISize32.toInt_bmod_18446744073709551616 (x : ISize32) : x.toInt.bmod 18446744073709551616 = x.toInt :=
  Int.bmod_eq_of_le (Int.le_trans (by decide) x.le_toInt) (Int.lt_of_lt_of_le x.toInt_lt (by decide))

@[simp] theorem ISize32.toInt_bmod_two_pow_numBits (x : ISize32) : x.toInt.bmod (2 ^ System.Platform.numBits) = x.toInt := by
  refine Int.bmod_eq_of_le (Int.le_trans ?_ x.iSizeMinValue_le_toInt)
    (Int.lt_of_le_sub_one (Int.le_trans x.toInt_le_iSizeMaxValue ?_))
  all_goals cases System.Platform.numBits_eq <;> simp_all [ISize.toInt_minValue, ISize.toInt_maxValue]

@[simp] theorem BitVec.ofInt_isize32ToInt (x : ISize32) : BitVec.ofInt 32 x.toInt = x.toBitVec := BitVec.eq_of_toInt_eq (by simp)

@[simp] theorem ISize32.ofIntLE_toInt (x : ISize32) : ISize32.ofIntLE x.toInt x.minValue_le_toInt x.toInt_le = x := ISize32.toBitVec.inj (by simp)

theorem Int8.ofIntLE_isize32ToInt (x : ISize32) {h₁ h₂} : Int8.ofIntLE x.toInt h₁ h₂ = x.toInt8 := (rfl)

theorem Int16.ofIntLE_isize32ToInt (x : ISize32) {h₁ h₂} : Int16.ofIntLE x.toInt h₁ h₂ = x.toInt16 := (rfl)

@[simp] theorem ISize32.ofIntLE_int8ToInt (x : Int8) :
    ISize32.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toISize32 := (rfl)

@[simp] theorem ISize32.ofIntLE_int16ToInt (x : Int16) :
    ISize32.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toISize32 := (rfl)

theorem ISize32.ofIntLE_int64ToInt (x : Int64) {h₁ h₂} : ISize32.ofIntLE x.toInt h₁ h₂ = x.toISize32 := (rfl)

theorem ISize32.ofIntLE_iSizeToInt (x : ISize) {h₁ h₂} : ISize32.ofIntLE x.toInt h₁ h₂ = x.toISize32 := (rfl)

@[simp] theorem Int64.ofIntLE_isize32ToInt (x : ISize32) :
    Int64.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt64 := (rfl)

@[simp] theorem ISize.ofIntLE_isize32ToInt (x : ISize32) :
    ISize.ofIntLE x.toInt x.iSizeMinValue_le_toInt x.toInt_le_iSizeMaxValue = x.toISize := (rfl)

@[simp] theorem ISize32.ofInt_toInt (x : ISize32) : ISize32.ofInt x.toInt = x := ISize32.toBitVec.inj (by simp)

@[simp] theorem Int8.ofInt_isize32ToInt (x : ISize32) : Int8.ofInt x.toInt = x.toInt8 := (rfl)

@[simp] theorem Int16.ofInt_isize32ToInt (x : ISize32) : Int16.ofInt x.toInt = x.toInt16 := (rfl)

@[simp] theorem ISize32.ofInt_int8ToInt (x : Int8) : ISize32.ofInt x.toInt = x.toISize32 := (rfl)

@[simp] theorem ISize32.ofInt_int16ToInt (x : Int16) : ISize32.ofInt x.toInt = x.toISize32 := (rfl)

@[simp] theorem ISize32.ofInt_int64ToInt (x : Int64) : ISize32.ofInt x.toInt = x.toISize32 := (rfl)

@[simp] theorem ISize32.ofInt_iSizeToInt (x : ISize) : ISize32.ofInt x.toInt = x.toISize32 := (rfl)

@[simp] theorem Int64.ofInt_isize32ToInt (x : ISize32) : Int64.ofInt x.toInt = x.toInt64 := (rfl)

@[simp] theorem ISize.ofInt_isize32ToInt (x : ISize32) : ISize.ofInt x.toInt = x.toISize := (rfl)

@[simp] theorem ISize32.toInt_ofIntLE {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂).toInt = x := by
  rw [ofIntLE, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]

theorem ISize32.ofIntLE_eq_ofIntTruncate {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂) = ofIntTruncate x := by
  rw [ofIntTruncate, dif_pos h₁, dif_pos h₂]

theorem ISize32.ofIntLE_eq_ofInt {n : Int} (h₁ h₂) : ISize32.ofIntLE n h₁ h₂ = ISize32.ofInt n := (rfl)

theorem ISize32.toInt_ofIntTruncate {x : Int} (h₁ : ISize32.minValue.toInt ≤ x)
    (h₂ : x ≤ ISize32.maxValue.toInt) : (ISize32.ofIntTruncate x).toInt = x := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toInt_ofIntLE]

@[simp] theorem ISize32.ofIntTruncate_toInt (x : ISize32) : ISize32.ofIntTruncate x.toInt = x :=
  ISize32.toInt.inj (toInt_ofIntTruncate x.minValue_le_toInt x.toInt_le)

@[simp] theorem ISize32.ofIntTruncate_int8ToInt (x : Int8) : ISize32.ofIntTruncate x.toInt = x.toISize32 :=
  ISize32.toInt.inj (by
    rw [toInt_ofIntTruncate, Int8.toInt_toISize32]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))

@[simp] theorem ISize32.ofIntTruncate_int16ToInt (x : Int16) : ISize32.ofIntTruncate x.toInt = x.toISize32 :=
  ISize32.toInt.inj (by
    rw [toInt_ofIntTruncate, Int16.toInt_toISize32]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))

@[simp] theorem Int64.ofIntTruncate_isize32ToInt (x : ISize32) : Int64.ofIntTruncate x.toInt = x.toInt64 :=
  Int64.toInt.inj (by
    rw [toInt_ofIntTruncate, ISize32.toInt_toInt64]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))

@[simp] theorem ISize.ofIntTruncate_isize32ToInt (x : ISize32) : ISize.ofIntTruncate x.toInt = x.toISize :=
  ISize.toInt.inj (by
    rw [toInt_ofIntTruncate, ISize32.toInt_toISize]
    · exact x.iSizeMinValue_le_toInt
    · exact x.toInt_le_iSizeMaxValue)

theorem ISize32.le_iff_toInt_le {x y : ISize32} : x ≤ y ↔ x.toInt ≤ y.toInt := BitVec.sle_iff_toInt_le

theorem ISize32.lt_iff_toInt_lt {x y : ISize32} : x < y ↔ x.toInt < y.toInt := BitVec.slt_iff_toInt_lt

theorem ISize32.cast_toNatClampNeg (x : ISize32) (hx : 0 ≤ x) : x.toNatClampNeg = x.toInt := by
  rw [toNatClampNeg, toInt, Int.toNat_of_nonneg (by simpa using le_iff_toInt_le.1 hx)]

theorem ISize32.ofNat_toNatClampNeg (x : ISize32) (hx : 0 ≤ x) : ISize32.ofNat x.toNatClampNeg = x :=
  ISize32.toInt.inj (by rw [ISize32.toInt_ofNat_of_lt x.toNatClampNeg_lt, cast_toNatClampNeg _ hx])

theorem ISize32.ofNat_int8ToNatClampNeg (x : Int8) (hx : 0 ≤ x) : ISize32.ofNat x.toNatClampNeg = x.toISize32 :=
  ISize32.toInt.inj (by rw [ISize32.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int8.cast_toNatClampNeg _ hx, Int8.toInt_toISize32])

theorem ISize32.ofNat_int16ToNatClampNeg (x : Int16) (hx : 0 ≤ x) : ISize32.ofNat x.toNatClampNeg = x.toISize32 :=
  ISize32.toInt.inj (by rw [ISize32.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int16.cast_toNatClampNeg _ hx, Int16.toInt_toISize32])

theorem Int64.ofNat_isize32ToNatClampNeg (x : ISize32) (hx : 0 ≤ x) : Int64.ofNat x.toNatClampNeg = x.toInt64 :=
  Int64.toInt.inj (by rw [Int64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    ISize32.cast_toNatClampNeg _ hx, ISize32.toInt_toInt64])

theorem ISize.ofNat_isize32ToNatClampNeg (x : ISize32) (hx : 0 ≤ x) : ISize.ofNat x.toNatClampNeg = x.toISize :=
  ISize.toInt.inj (by rw [ISize.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    ISize32.cast_toNatClampNeg _ hx, ISize32.toInt_toISize])

@[simp] theorem Int8.toInt8_toISize32 (n : Int8) : n.toISize32.toInt8 = n :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int8.toInt16_toISize32 (n : Int8) : n.toISize32.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int8.toISize32_toInt16 (n : Int8) : n.toInt16.toISize32 = n.toISize32 :=
  ISize32.toInt.inj (by simp)

@[simp] theorem Int8.toISize32_toInt64 (n : Int8) : n.toInt64.toISize32 = n.toISize32 :=
  ISize32.toInt.inj (by simp)

@[simp] theorem Int8.toISize32_toISize (n : Int8) : n.toISize.toISize32 = n.toISize32 :=
  ISize32.toInt.inj (by simp)

@[simp] theorem Int8.toInt64_toISize32 (n : Int8) : n.toISize32.toInt64 = n.toInt64 :=
  Int64.toInt.inj (by simp)

@[simp] theorem Int8.toISize_toISize32 (n : Int8) : n.toISize32.toISize = n.toISize :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int16.toInt8_toISize32 (n : Int16) : n.toISize32.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int16.toInt16_toISize32 (n : Int16) : n.toISize32.toInt16 = n :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int16.toISize32_toInt64 (n : Int16) : n.toInt64.toISize32 = n.toISize32 :=
  ISize32.toInt.inj (by simp)

@[simp] theorem Int16.toISize32_toISize (n : Int16) : n.toISize.toISize32 = n.toISize32 :=
  ISize32.toInt.inj (by simp)

@[simp] theorem Int16.toInt64_toISize32 (n : Int16) : n.toISize32.toInt64 = n.toInt64 :=
  Int64.toInt.inj (by simp)

@[simp] theorem Int16.toISize_toISize32 (n : Int16) : n.toISize32.toISize = n.toISize :=
  ISize.toInt.inj (by simp)

@[simp] theorem ISize32.toInt8_toInt16 (n : ISize32) : n.toInt16.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem ISize32.toInt8_toInt64 (n : ISize32) : n.toInt64.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem ISize32.toInt8_toISize (n : ISize32) : n.toISize.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem ISize32.toInt16_toInt64 (n : ISize32) : n.toInt64.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem ISize32.toInt16_toISize (n : ISize32) : n.toISize.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem ISize32.toISize32_toInt64 (n : ISize32) : n.toInt64.toISize32 = n :=
  ISize32.toInt.inj (by simp)

@[simp] theorem ISize32.toISize32_toISize (n : ISize32) : n.toISize.toISize32 = n :=
  ISize32.toInt.inj (by simp)

@[simp] theorem ISize32.toInt64_toISize (n : ISize32) : n.toISize.toInt64 = n.toInt64 :=
  Int64.toInt.inj (by simp)

@[simp] theorem ISize32.toISize_toInt64 (n : ISize32) : n.toInt64.toISize = n.toISize :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int64.toInt8_toISize32 (n : Int64) : n.toISize32.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem Int64.toInt16_toISize32 (n : Int64) : n.toISize32.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem Int64.toISize32_toISize (n : Int64) : n.toISize.toISize32 = n.toISize32 :=
  ISize32.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem ISize.toInt8_toISize32 (n : ISize) : n.toISize32.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem ISize.toInt16_toISize32 (n : ISize) : n.toISize32.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem ISize.toISize32_toInt64 (n : ISize) : n.toInt64.toISize32 = n.toISize32 :=
  ISize32.toInt.inj (by simp)

theorem USize32.toISize32_ofNatLT {n : Nat} (hn) : (USize32.ofNatLT n hn).toISize32 = ISize32.ofNat n :=
  ISize32.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat])

@[simp] theorem USize32.toISize32_ofNat' {n : Nat} : (USize32.ofNat n).toISize32 = ISize32.ofNat n := (rfl)

@[simp] theorem USize32.toISize32_ofNat {n : Nat} : toISize32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := (rfl)

@[simp] theorem USize32.toISize32_ofBitVec (b) : (USize32.ofBitVec b).toISize32 = ISize32.ofBitVec b := (rfl)

@[simp, int_toBitVec] theorem ISize32.toBitVec_ofBitVec (b) : (ISize32.ofBitVec b).toBitVec = b := (rfl)

theorem ISize32.toBitVec_ofIntTruncate {n : Int} (h₁ : ISize32.minValue.toInt ≤ n) (h₂ : n ≤ ISize32.maxValue.toInt) :
    (ISize32.ofIntTruncate n).toBitVec = BitVec.ofInt _ n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toBitVec_ofIntLE]

@[simp] theorem ISize32.toInt_ofBitVec (b) : (ISize32.ofBitVec b).toInt = b.toInt := (rfl)

@[simp] theorem ISize32.toNatClampNeg_ofIntLE {n : Int} (h₁ h₂) : (ISize32.ofIntLE n h₁ h₂).toNatClampNeg = n.toNat := by
  rw [ofIntLE, toNatClampNeg, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]

@[simp] theorem ISize32.toNatClampNeg_ofBitVec (b) : (ISize32.ofBitVec b).toNatClampNeg = b.toInt.toNat := (rfl)

theorem ISize32.toNatClampNeg_ofInt_of_le {n : Int} (h₁ : -2 ^ 31 ≤ n) (h₂ : n < 2 ^ 31) :
    (ISize32.ofInt n).toNatClampNeg = n.toNat := by rw [toNatClampNeg, toInt_ofInt_of_le h₁ h₂]

theorem ISize32.toNatClampNeg_ofIntTruncate_of_lt {n : Int} (h₁ : n < 2 ^ 31) :
    (ISize32.ofIntTruncate n).toNatClampNeg = n.toNat := by
  rw [ofIntTruncate]
  split
  · rw [dif_pos (by rw [toInt_maxValue]; omega), toNatClampNeg_ofIntLE]
  next h =>
    rw [toNatClampNeg_minValue, eq_comm, Int.toNat_eq_zero]
    rw [toInt_minValue] at h
    omega

@[simp] theorem ISize32.toUSize32_ofBitVec (b) : (ISize32.ofBitVec b).toUSize32 = USize32.ofBitVec b := (rfl)

@[simp] theorem ISize32.toUSize32_ofNat' {n} : (ISize32.ofNat n).toUSize32 = USize32.ofNat n := (rfl)

@[simp] theorem ISize32.toUSize32_ofNat {n} : toUSize32 (OfNat.ofNat n) = OfNat.ofNat n := (rfl)

theorem ISize32.toInt8_ofIntLE {n} (h₁ h₂) : (ISize32.ofIntLE n h₁ h₂).toInt8 = Int8.ofInt n := Int8.toInt.inj (by simp)

@[simp] theorem ISize32.toInt8_ofBitVec (b) : (ISize32.ofBitVec b).toInt8 = Int8.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem ISize32.toInt8_ofNat' {n} : (ISize32.ofNat n).toInt8 = Int8.ofNat n :=
  Int8.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem ISize32.toInt8_ofInt {n} : (ISize32.ofInt n).toInt8 = Int8.ofInt n :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem ISize32.toInt8_ofNat {n} : toInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt8_ofNat'

theorem ISize32.toInt8_ofIntTruncate {n : Int} (h₁ : -2 ^ 31 ≤ n) (h₂ : n < 2 ^ 31) :
    (ISize32.ofIntTruncate n).toInt8 = Int8.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt8_ofIntLE]

theorem ISize32.toInt16_ofIntLE {n} (h₁ h₂) : (ISize32.ofIntLE n h₁ h₂).toInt16 = Int16.ofInt n := Int16.toInt.inj (by simp)

@[simp] theorem ISize32.toInt16_ofBitVec (b) : (ISize32.ofBitVec b).toInt16 = Int16.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem ISize32.toInt16_ofNat' {n} : (ISize32.ofNat n).toInt16 = Int16.ofNat n :=
  Int16.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem ISize32.toInt16_ofInt {n} : (ISize32.ofInt n).toInt16 = Int16.ofInt n :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem ISize32.toInt16_ofNat {n} : toInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt16_ofNat'

theorem ISize32.toInt16_ofIntTruncate {n : Int} (h₁ : -2 ^ 31 ≤ n) (h₂ : n < 2 ^ 31) :
    (ISize32.ofIntTruncate n).toInt16 = Int16.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt16_ofIntLE]

theorem Int64.toISize32_ofIntLE {n} (h₁ h₂) : (Int64.ofIntLE n h₁ h₂).toISize32 = ISize32.ofInt n := ISize32.toInt.inj (by simp)

theorem ISize.toISize32_ofIntLE {n} (h₁ h₂) : (ISize.ofIntLE n h₁ h₂).toISize32 = ISize32.ofInt n := ISize32.toInt.inj (by simp)

@[simp] theorem Int64.toISize32_ofBitVec (b) : (Int64.ofBitVec b).toISize32 = ISize32.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem ISize.toISize32_ofBitVec (b) : (ISize.ofBitVec b).toISize32 = ISize32.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int64.toISize32_ofNat' {n} : (Int64.ofNat n).toISize32 = ISize32.ofNat n :=
  ISize32.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem ISize.toISize32_ofNat' {n} : (ISize.ofNat n).toISize32 = ISize32.ofNat n := by
  apply ISize32.toBitVec.inj
  simp only [toBitVec_toISize32, toBitVec_ofNat', ISize32.toBitVec_ofNat']
  rw [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_ofNat_of_le]
  all_goals cases System.Platform.numBits_eq <;> simp_all

@[simp] theorem Int64.toISize32_ofInt {n} : (Int64.ofInt n).toISize32 = ISize32.ofInt n :=
  ISize32.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))

@[simp] theorem ISize.toISize32_ofInt {n} : (ISize.ofInt n).toISize32 = ISize32.ofInt n := by
  apply ISize32.toInt.inj
  simp only [toInt_toISize32, toInt_ofInt, Nat.reducePow, ISize32.toInt_ofInt]
  exact Int.bmod_bmod_of_dvd USize32.size_dvd_usizeSize

@[simp] theorem Int64.toISize32_ofNat {n} : toISize32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toISize32_ofNat'

@[simp] theorem ISize.toISize32_ofNat {n} : toISize32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toISize32_ofNat'

theorem Int64.toISize32_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (Int64.ofIntTruncate n).toISize32 = ISize32.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toISize32_ofIntLE]

theorem ISize.toISize32_ofIntTruncate {n : Int} (h₁ : -2 ^ (System.Platform.numBits - 1) ≤ n)
    (h₂ : n < 2 ^ (System.Platform.numBits - 1)) : (ISize.ofIntTruncate n).toISize32 = ISize32.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate, toISize32_ofIntLE]
  · exact toInt_minValue ▸ h₁
  · rw [toInt_maxValue]
    omega

@[simp, int_toBitVec] theorem ISize32.toBitVec_minValue : minValue.toBitVec = BitVec.intMin _ := (rfl)

@[simp, int_toBitVec] theorem ISize32.toBitVec_maxValue : maxValue.toBitVec = BitVec.intMax _ := (rfl)

@[simp] theorem ISize32.toInt8_neg (x : ISize32) : (-x).toInt8 = -x.toInt8 := Int8.toBitVec.inj (by simp)

@[simp] theorem ISize32.toInt16_neg (x : ISize32) : (-x).toInt16 = -x.toInt16 := Int16.toBitVec.inj (by simp)

@[simp] theorem Int64.toISize32_neg (x : Int64) : (-x).toISize32 = -x.toISize32 := ISize32.toBitVec.inj (by simp)

@[simp] theorem ISize.toISize32_neg (x : ISize) : (-x).toISize32 = -x.toISize32 :=
  ISize32.toBitVec.inj (by rw [toBitVec_toISize32, toBitVec_neg, ISize32.toBitVec_neg, toBitVec_toISize32,
    BitVec.signExtend_neg_of_le (by cases System.Platform.numBits_eq <;> simp_all)])

@[simp] theorem Int8.toISize32_neg_of_ne {x : Int8} (hx : x ≠ -128) : (-x).toISize32 = -x.toISize32 :=
  ISize32.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int8.toBitVec.inj h)))

@[simp] theorem Int16.toISize32_neg_of_ne {x : Int16} (hx : x ≠ -32768) : (-x).toISize32 = -x.toISize32 :=
  ISize32.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int16.toBitVec.inj h)))

@[simp] theorem ISize32.toISize_neg_of_ne {x : ISize32} (hx : x ≠ -2147483648) : (-x).toISize = -x.toISize :=
  ISize.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (ISize32.toBitVec.inj h)))

@[simp] theorem ISize32.toInt64_neg_of_ne {x : ISize32} (hx : x ≠ -2147483648) : (-x).toInt64 = -x.toInt64 :=
  Int64.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _  (fun h => hx (ISize32.toBitVec.inj h)))

theorem Int8.toISize32_ofIntLE {n : Int} (h₁ h₂) :
    (Int8.ofIntLE n h₁ h₂).toISize32 = ISize32.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  ISize32.toInt.inj (by simp)

@[simp] theorem Int8.toISize32_ofBitVec (b) : (Int8.ofBitVec b).toISize32 = ISize32.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int8.toISize32_ofInt {n : Int} (h₁ : Int8.minValue.toInt ≤ n) (h₂ : n ≤ Int8.maxValue.toInt) :
    (Int8.ofInt n).toISize32 = ISize32.ofInt n := by rw [← Int8.ofIntLE_eq_ofInt h₁ h₂, toISize32_ofIntLE, ISize32.ofIntLE_eq_ofInt]

@[simp] theorem Int8.toISize32_ofNat' {n : Nat} (h : n ≤ Int8.maxValue.toInt) :
    (Int8.ofNat n).toISize32 = ISize32.ofNat n := by
  rw [← ofInt_eq_ofNat, toISize32_ofInt (by simp [toInt_minValue]) h, ISize32.ofInt_eq_ofNat]

@[simp] theorem Int8.toISize32_ofNat {n : Nat} (h : n ≤ 127) :
    toISize32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int8.toISize32_ofNat' (by rw [toInt_maxValue]; omega)

theorem Int16.toISize32_ofIntLE {n : Int} (h₁ h₂) :
    (Int16.ofIntLE n h₁ h₂).toISize32 = ISize32.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  ISize32.toInt.inj (by simp)

@[simp] theorem Int16.toISize32_ofBitVec (b) : (Int16.ofBitVec b).toISize32 = ISize32.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int16.toISize32_ofInt {n : Int} (h₁ : Int16.minValue.toInt ≤ n) (h₂ : n ≤ Int16.maxValue.toInt) :
    (Int16.ofInt n).toISize32 = ISize32.ofInt n := by rw [← Int16.ofIntLE_eq_ofInt h₁ h₂, toISize32_ofIntLE, ISize32.ofIntLE_eq_ofInt]

@[simp] theorem Int16.toISize32_ofNat' {n : Nat} (h : n ≤ Int16.maxValue.toInt) :
    (Int16.ofNat n).toISize32 = ISize32.ofNat n := by
  rw [← ofInt_eq_ofNat, toISize32_ofInt (by simp [toInt_minValue]) h, ISize32.ofInt_eq_ofNat]

@[simp] theorem Int16.toISize32_ofNat {n : Nat} (h : n ≤ 32767) :
    toISize32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int16.toISize32_ofNat' (by rw [toInt_maxValue]; omega)

theorem ISize32.toInt64_ofIntLE {n : Int} (h₁ h₂) :
    (ISize32.ofIntLE n h₁ h₂).toInt64 = Int64.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int64.toInt.inj (by simp)

theorem ISize32.toISize_ofIntLE {n : Int} (h₁ h₂) :
    (ISize32.ofIntLE n h₁ h₂).toISize = ISize.ofIntLE n (Int.le_trans minValue.iSizeMinValue_le_toInt h₁)
      (Int.le_trans h₂ maxValue.toInt_le_iSizeMaxValue) :=
  ISize.toInt.inj (by simp)

@[simp] theorem ISize32.toInt64_ofBitVec (b) : (ISize32.ofBitVec b).toInt64 = Int64.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem ISize32.toISize_ofBitVec (b) : (ISize32.ofBitVec b).toISize = ISize.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem ISize32.toInt64_ofInt {n : Int} (h₁ : ISize32.minValue.toInt ≤ n) (h₂ : n ≤ ISize32.maxValue.toInt) :
    (ISize32.ofInt n).toInt64 = Int64.ofInt n := by rw [← ISize32.ofIntLE_eq_ofInt h₁ h₂, toInt64_ofIntLE, Int64.ofIntLE_eq_ofInt]

@[simp] theorem ISize32.toISize_ofInt {n : Int} (h₁ : ISize32.minValue.toInt ≤ n) (h₂ : n ≤ ISize32.maxValue.toInt) :
    (ISize32.ofInt n).toISize = ISize.ofInt n := by rw [← ISize32.ofIntLE_eq_ofInt h₁ h₂, toISize_ofIntLE, ISize.ofIntLE_eq_ofInt]

@[simp] theorem ISize32.toInt64_ofNat' {n : Nat} (h : n ≤ ISize32.maxValue.toInt) :
    (ISize32.ofNat n).toInt64 = Int64.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt64_ofInt (by simp [toInt_minValue]) h, Int64.ofInt_eq_ofNat]

@[simp] theorem ISize32.toISize_ofNat' {n : Nat} (h : n ≤ ISize32.maxValue.toInt) :
    (ISize32.ofNat n).toISize = ISize.ofNat n := by
  rw [← ofInt_eq_ofNat, toISize_ofInt (by simp [toInt_minValue]) h, ISize.ofInt_eq_ofNat]

@[simp] theorem ISize32.toInt64_ofNat {n : Nat} (h : n ≤ 2147483647) :
    toInt64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := ISize32.toInt64_ofNat' (by rw [toInt_maxValue]; omega)

@[simp] theorem ISize32.toISize_ofNat {n : Nat} (h : n ≤ 2147483647) :
    toISize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := ISize32.toISize_ofNat' (by rw [toInt_maxValue]; omega)

@[simp] theorem ISize32.ofIntLE_bitVecToInt (n : BitVec 32) :
    ISize32.ofIntLE n.toInt (by exact n.le_toInt) (by exact n.toInt_le) = ISize32.ofBitVec n :=
  ISize32.toBitVec.inj (by simp)

theorem ISize32.ofBitVec_ofNatLT (n : Nat) (hn) : ISize32.ofBitVec (BitVec.ofNatLT n hn) = ISize32.ofNat n :=
  ISize32.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat hn])

@[simp] theorem ISize32.ofBitVec_ofNat (n : Nat) : ISize32.ofBitVec (BitVec.ofNat 32 n) = ISize32.ofNat n := (rfl)

@[simp] theorem ISize32.ofBitVec_ofInt (n : Int) : ISize32.ofBitVec (BitVec.ofInt 32 n) = ISize32.ofInt n := (rfl)

@[simp] theorem ISize32.ofNat_bitVecToNat (n : BitVec 32) : ISize32.ofNat n.toNat = ISize32.ofBitVec n :=
  ISize32.toBitVec.inj (by simp)

@[simp] theorem ISize32.ofInt_bitVecToInt (n : BitVec 32) : ISize32.ofInt n.toInt = ISize32.ofBitVec n :=
  ISize32.toBitVec.inj (by simp)

@[simp] theorem ISize32.ofIntTruncate_bitVecToInt (n : BitVec 32) : ISize32.ofIntTruncate n.toInt = ISize32.ofBitVec n :=
  ISize32.toBitVec.inj (by simp [toBitVec_ofIntTruncate (n.le_toInt) (n.toInt_le)])

@[simp] theorem ISize32.toInt_neg (n : ISize32) : (-n).toInt = (-n.toInt).bmod (2 ^ 32) := BitVec.toInt_neg

@[simp] theorem ISize32.toNatClampNeg_eq_zero_iff {n : ISize32} : n.toNatClampNeg = 0 ↔ n ≤ 0 := by
  rw [toNatClampNeg, Int.toNat_eq_zero, le_iff_toInt_le, toInt_zero]

@[simp] protected theorem ISize32.not_le {n m : ISize32} : ¬n ≤ m ↔ m < n := by simp [le_iff_toInt_le, lt_iff_toInt_lt]
@[simp] protected theorem Int64.not_le {n m : Int64} : ¬n ≤ m ↔ m < n := by simp [le_iff_toInt_le, lt_iff_toInt_lt]

@[simp] theorem ISize32.neg_nonpos_iff (n : ISize32) : -n ≤ 0 ↔ n = minValue ∨ 0 ≤ n := by
  rw [le_iff_toBitVec_sle, toBitVec_zero, toBitVec_neg, BitVec.neg_sle_zero (by decide)]
  simp [← toBitVec_inj, le_iff_toBitVec_sle, BitVec.intMin_eq_neg_two_pow]

@[simp] theorem ISize32.toNatClampNeg_pos_iff (n : ISize32) : 0 < n.toNatClampNeg ↔ 0 < n := by simp [Nat.pos_iff_ne_zero]
@[simp] theorem Int64.toNatClampNeg_pos_iff (n : Int64) : 0 < n.toNatClampNeg ↔ 0 < n := by simp [Nat.pos_iff_ne_zero]

@[simp] theorem ISize32.toInt_div (a b : ISize32) : (a / b).toInt = (a.toInt.tdiv b.toInt).bmod (2 ^ 32) := by
  rw [← toInt_toBitVec, ISize32.toBitVec_div, BitVec.toInt_sdiv, toInt_toBitVec, toInt_toBitVec]

theorem ISize32.toInt_div_of_ne_left (a b : ISize32) (h : a ≠ minValue) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, ISize32.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inl (by simpa [← toBitVec_inj] using h)

theorem ISize32.toInt_div_of_ne_right (a b : ISize32) (h : b ≠ -1) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, ISize32.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inr (by simpa [← toBitVec_inj] using h)

theorem Int8.toISize32_ne_minValue (a : Int8) : a.toISize32 ≠ ISize32.minValue :=
  have := a.le_toInt; by simp [← ISize32.toInt_inj]; omega

theorem Int16.toISize32_ne_minValue (a : Int16) : a.toISize32 ≠ ISize32.minValue :=
  have := a.le_toInt; by simp [← ISize32.toInt_inj]; omega

theorem ISize32.toInt64_ne_minValue (a : ISize32) : a.toInt64 ≠ Int64.minValue :=
  have := a.le_toInt; by simp [← Int64.toInt_inj]; omega

theorem ISize32.toISize_ne_minValue (a : ISize32) (ha : a ≠ minValue) : a.toISize ≠ ISize.minValue := by
  have := a.le_toInt
  have := ISize.toInt_minValue_le
  simp [← ISize.toInt_inj, ← ISize32.toInt_inj] at ⊢ ha; omega

theorem Int8.toISize32_ne_neg_one (a : Int8) (ha : a ≠ -1) : a.toISize32 ≠ -1 :=
  ne_of_apply_ne ISize32.toInt8 (by simpa using ha)

theorem Int16.toISize32_ne_neg_one (a : Int16) (ha : a ≠ -1) : a.toISize32 ≠ -1 :=
  ne_of_apply_ne ISize32.toInt16 (by simpa using ha)

theorem ISize32.toInt64_ne_neg_one (a : ISize32) (ha : a ≠ -1) : a.toInt64 ≠ -1 :=
  ne_of_apply_ne Int64.toISize32 (by simpa using ha)

theorem ISize32.toISize_ne_neg_one (a : ISize32) (ha : a ≠ -1) : a.toISize ≠ -1 :=
  ne_of_apply_ne ISize.toISize32 (by simpa using ha)

theorem Int8.toISize32_div_of_ne_left (a b : Int8) (ha : a ≠ minValue) : (a / b).toISize32 = a.toISize32 / b.toISize32 :=
  ISize32.toInt_inj.1 (by rw [toInt_toISize32, toInt_div_of_ne_left _ _ ha,
    ISize32.toInt_div_of_ne_left _ _ a.toISize32_ne_minValue, toInt_toISize32, toInt_toISize32])

theorem Int16.toISize32_div_of_ne_left (a b : Int16) (ha : a ≠ minValue) : (a / b).toISize32 = a.toISize32 / b.toISize32 :=
  ISize32.toInt_inj.1 (by rw [toInt_toISize32, toInt_div_of_ne_left _ _ ha,
    ISize32.toInt_div_of_ne_left _ _ a.toISize32_ne_minValue, toInt_toISize32, toInt_toISize32])

theorem ISize32.toInt64_div_of_ne_left (a b : ISize32) (ha : a ≠ minValue) : (a / b).toInt64 = a.toInt64 / b.toInt64 :=
  Int64.toInt_inj.1 (by rw [toInt_toInt64, toInt_div_of_ne_left _ _ ha,
    Int64.toInt_div_of_ne_left _ _ a.toInt64_ne_minValue, toInt_toInt64, toInt_toInt64])

theorem ISize32.toISize_div_of_ne_left (a b : ISize32) (ha : a ≠ minValue) : (a / b).toISize = a.toISize / b.toISize :=
  ISize.toInt_inj.1 (by rw [toInt_toISize, toInt_div_of_ne_left _ _ ha,
    ISize.toInt_div_of_ne_left _ _ (a.toISize_ne_minValue ha), toInt_toISize, toInt_toISize])

theorem Int8.toISize32_div_of_ne_right (a b : Int8) (hb : b ≠ -1) : (a / b).toISize32 = a.toISize32 / b.toISize32 :=
  ISize32.toInt_inj.1 (by rw [toInt_toISize32, toInt_div_of_ne_right _ _ hb,
    ISize32.toInt_div_of_ne_right _ _ (b.toISize32_ne_neg_one hb), toInt_toISize32, toInt_toISize32])

theorem Int16.toISize32_div_of_ne_right (a b : Int16) (hb : b ≠ -1) : (a / b).toISize32 = a.toISize32 / b.toISize32 :=
  ISize32.toInt_inj.1 (by rw [toInt_toISize32, toInt_div_of_ne_right _ _ hb,
    ISize32.toInt_div_of_ne_right _ _ (b.toISize32_ne_neg_one hb), toInt_toISize32, toInt_toISize32])

theorem ISize32.toInt64_div_of_ne_right (a b : ISize32) (hb : b ≠ -1) : (a / b).toInt64 = a.toInt64 / b.toInt64 :=
  Int64.toInt_inj.1 (by rw [toInt_toInt64, toInt_div_of_ne_right _ _ hb,
    Int64.toInt_div_of_ne_right _ _ (b.toInt64_ne_neg_one hb), toInt_toInt64, toInt_toInt64])

theorem ISize32.toISize_div_of_ne_right (a b : ISize32) (hb : b ≠ -1) : (a / b).toISize = a.toISize / b.toISize :=
  ISize.toInt_inj.1 (by rw [toInt_toISize, toInt_div_of_ne_right _ _ hb,
    ISize.toInt_div_of_ne_right _ _ (b.toISize_ne_neg_one hb), toInt_toISize, toInt_toISize])

@[simp] theorem ISize32.minValue_div_neg_one : minValue / -1 = minValue := (rfl)

@[simp] theorem ISize32.toInt_add (a b : ISize32) : (a + b).toInt = (a.toInt + b.toInt).bmod (2 ^ 32) := by
  rw [← toInt_toBitVec, ISize32.toBitVec_add, BitVec.toInt_add, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem ISize32.toInt8_add (a b : ISize32) : (a + b).toInt8 = a.toInt8 + b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem ISize32.toInt16_add (a b : ISize32) : (a + b).toInt16 = a.toInt16 + b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem ISize.toISize32_add (a b : ISize) : (a + b).toISize32 = a.toISize32 + b.toISize32 :=
  ISize32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem Int64.toISize32_add (a b : Int64) : (a + b).toISize32 = a.toISize32 + b.toISize32 :=
  ISize32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem ISize32.toInt_mul (a b : ISize32) : (a * b).toInt = (a.toInt * b.toInt).bmod (2 ^ 32) := by
  rw [← toInt_toBitVec, ISize32.toBitVec_mul, BitVec.toInt_mul, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem ISize32.toInt8_mul (a b : ISize32) : (a * b).toInt8 = a.toInt8 * b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

@[simp] theorem ISize32.toInt16_mul (a b : ISize32) : (a * b).toInt16 = a.toInt16 * b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

@[simp] theorem ISize.toISize32_mul (a b : ISize) : (a * b).toISize32 = a.toISize32 * b.toISize32 :=
  ISize32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

@[simp] theorem Int64.toISize32_mul (a b : Int64) : (a * b).toISize32 = a.toISize32 * b.toISize32 :=
  ISize32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

protected theorem ISize32.sub_eq_add_neg (a b : ISize32) : a - b = a + -b := ISize32.toBitVec.inj (by simp [BitVec.sub_eq_add_neg])

@[simp] theorem ISize32.toInt_sub (a b : ISize32) : (a - b).toInt = (a.toInt - b.toInt).bmod (2 ^ 32) := by
  simp [ISize32.sub_eq_add_neg, Int.sub_eq_add_neg]

@[simp] theorem ISize32.toInt8_sub (a b : ISize32) : (a - b).toInt8 = a.toInt8 - b.toInt8 := by
  simp [ISize32.sub_eq_add_neg, Int8.sub_eq_add_neg]

@[simp] theorem ISize32.toInt16_sub (a b : ISize32) : (a - b).toInt16 = a.toInt16 - b.toInt16 := by
  simp [ISize32.sub_eq_add_neg, Int16.sub_eq_add_neg]

@[simp] theorem ISize.toISize32_sub (a b : ISize) : (a - b).toISize32 = a.toISize32 - b.toISize32 := by
  simp [ISize.sub_eq_add_neg, ISize32.sub_eq_add_neg]

@[simp] theorem Int64.toISize32_sub (a b : Int64) : (a - b).toISize32 = a.toISize32 - b.toISize32 := by
  simp [Int64.sub_eq_add_neg, ISize32.sub_eq_add_neg]

@[simp] theorem Int8.toISize32_lt {a b : Int8} : a.toISize32 < b.toISize32 ↔ a < b := by
  simp [lt_iff_toInt_lt, ISize32.lt_iff_toInt_lt]

@[simp] theorem Int16.toISize32_lt {a b : Int16} : a.toISize32 < b.toISize32 ↔ a < b := by
  simp [lt_iff_toInt_lt, ISize32.lt_iff_toInt_lt]

@[simp] theorem ISize32.toInt64_lt {a b : ISize32} : a.toInt64 < b.toInt64 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int64.lt_iff_toInt_lt]

@[simp] theorem ISize32.toISize_lt {a b : ISize32} : a.toISize < b.toISize ↔ a < b := by
  simp [lt_iff_toInt_lt, ISize.lt_iff_toInt_lt]

@[simp] theorem Int8.toISize32_le {a b : Int8} : a.toISize32 ≤ b.toISize32 ↔ a ≤ b := by
  simp [le_iff_toInt_le, ISize32.le_iff_toInt_le]

@[simp] theorem Int16.toISize32_le {a b : Int16} : a.toISize32 ≤ b.toISize32 ↔ a ≤ b := by
  simp [le_iff_toInt_le, ISize32.le_iff_toInt_le]

@[simp] theorem ISize32.toInt64_le {a b : ISize32} : a.toInt64 ≤ b.toInt64 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int64.le_iff_toInt_le]

@[simp] theorem ISize32.toISize_le {a b : ISize32} : a.toISize ≤ b.toISize ↔ a ≤ b := by
  simp [le_iff_toInt_le, ISize.le_iff_toInt_le]

@[simp] theorem ISize32.ofBitVec_neg (a : BitVec 32) : ISize32.ofBitVec (-a) = -ISize32.ofBitVec a := (rfl)

@[simp] theorem ISize32.ofInt_neg (a : Int) : ISize32.ofInt (-a) = -ISize32.ofInt a := ISize32.toInt_inj.1 (by simp)

theorem ISize32.ofInt_eq_iff_bmod_eq_toInt (a : Int) (b : ISize32) : ISize32.ofInt a = b ↔ a.bmod (2 ^ 32) = b.toInt := by
  simp [← ISize32.toInt_inj]

@[simp] theorem ISize32.ofBitVec_add (a b : BitVec 32) : ISize32.ofBitVec (a + b) = ISize32.ofBitVec a + ISize32.ofBitVec b := (rfl)

@[simp] theorem ISize32.ofInt_add (a b : Int) : ISize32.ofInt (a + b) = ISize32.ofInt a + ISize32.ofInt b := by
  simp [ISize32.ofInt_eq_iff_bmod_eq_toInt]

@[simp] theorem ISize32.ofNat_add (a b : Nat) : ISize32.ofNat (a + b) = ISize32.ofNat a + ISize32.ofNat b := by
  simp [← ISize32.ofInt_eq_ofNat]

theorem ISize32.ofIntLE_add {a b : Int} {hab₁ hab₂} : ISize32.ofIntLE (a + b) hab₁ hab₂ = ISize32.ofInt a + ISize32.ofInt b := by
  simp [ISize32.ofIntLE_eq_ofInt]

@[simp] theorem ISize32.ofBitVec_sub (a b : BitVec 32) : ISize32.ofBitVec (a - b) = ISize32.ofBitVec a - ISize32.ofBitVec b := (rfl)

@[simp] theorem ISize32.ofInt_sub (a b : Int) : ISize32.ofInt (a - b) = ISize32.ofInt a - ISize32.ofInt b := by
  simp [ISize32.ofInt_eq_iff_bmod_eq_toInt]

@[simp] theorem ISize32.ofNat_sub (a b : Nat) (hab : b ≤ a) : ISize32.ofNat (a - b) = ISize32.ofNat a - ISize32.ofNat b := by
  simp [← ISize32.ofInt_eq_ofNat, Int.ofNat_sub hab]

theorem ISize32.ofIntLE_sub {a b : Int} {hab₁ hab₂} : ISize32.ofIntLE (a - b) hab₁ hab₂ = ISize32.ofInt a - ISize32.ofInt b := by
  simp [ISize32.ofIntLE_eq_ofInt]

@[simp] theorem ISize32.ofBitVec_mul (a b : BitVec 32) : ISize32.ofBitVec (a * b) = ISize32.ofBitVec a * ISize32.ofBitVec b := (rfl)

@[simp] theorem ISize32.ofInt_mul (a b : Int) : ISize32.ofInt (a * b) = ISize32.ofInt a * ISize32.ofInt b := by
  simp [ISize32.ofInt_eq_iff_bmod_eq_toInt]

@[simp] theorem ISize32.ofNat_mul (a b : Nat) : ISize32.ofNat (a * b) = ISize32.ofNat a * ISize32.ofNat b := by
  simp [← ISize32.ofInt_eq_ofNat]

theorem ISize32.ofIntLE_mul {a b : Int} {hab₁ hab₂} : ISize32.ofIntLE (a * b) hab₁ hab₂ = ISize32.ofInt a * ISize32.ofInt b := by
  simp [ISize32.ofIntLE_eq_ofInt]

theorem ISize32.toInt_minValue_lt_zero : minValue.toInt < 0 := by decide

theorem ISize32.toInt_maxValue_add_one : maxValue.toInt + 1 = 2 ^ 31 := (rfl)

@[simp] theorem ISize32.ofBitVec_sdiv (a b : BitVec 32) : ISize32.ofBitVec (a.sdiv b) = ISize32.ofBitVec a / ISize32.ofBitVec b := (rfl)

theorem ISize32.ofInt_tdiv {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : ISize32.ofInt (a.tdiv b) = ISize32.ofInt a / ISize32.ofInt b := by
  rw [ISize32.ofInt_eq_iff_bmod_eq_toInt, toInt_div, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂

theorem ISize32.ofInt_eq_ofIntLE_div {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize32.ofInt (a.tdiv b) = ISize32.ofIntLE a ha₁ ha₂ / ISize32.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tdiv ha₁ ha₂ hb₁ hb₂]

theorem ISize32.ofNat_div {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ISize32.ofNat (a / b) = ISize32.ofNat a / ISize32.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tdiv,
    ofInt_tdiv (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)

@[simp] theorem ISize32.ofBitVec_srem (a b : BitVec 32) : ISize32.ofBitVec (a.srem b) = ISize32.ofBitVec a % ISize32.ofBitVec b := (rfl)

@[simp] theorem ISize32.toInt_bmod_size (a : ISize32) : a.toInt.bmod size = a.toInt := BitVec.toInt_bmod_cancel _

theorem ISize32.ofIntLE_le_iff_le {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize32.ofIntLE a ha₁ ha₂ ≤ ISize32.ofIntLE b hb₁ hb₂ ↔ a ≤ b := by simp [le_iff_toInt_le]

theorem ISize32.ofInt_le_iff_le {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : ISize32.ofInt a ≤ ISize32.ofInt b ↔ a ≤ b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_le_iff_le]

theorem ISize32.ofNat_le_iff_le {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ISize32.ofNat a ≤ ISize32.ofNat b ↔ a ≤ b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_le_iff_le (by simp) _ (by simp), Int.ofNat_le]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)

theorem ISize32.ofBitVec_le_iff_sle (a b : BitVec 32) : ISize32.ofBitVec a ≤ ISize32.ofBitVec b ↔ a.sle b := Iff.rfl

theorem ISize32.ofIntLE_lt_iff_lt {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize32.ofIntLE a ha₁ ha₂ < ISize32.ofIntLE b hb₁ hb₂ ↔ a < b := by simp [lt_iff_toInt_lt]

theorem ISize32.ofInt_lt_iff_lt {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : ISize32.ofInt a < ISize32.ofInt b ↔ a < b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_lt_iff_lt]

theorem ISize32.ofNat_lt_iff_lt {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ISize32.ofNat a < ISize32.ofNat b ↔ a < b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_lt_iff_lt (by simp) _ (by simp), Int.ofNat_lt]
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 ha)

theorem ISize32.ofBitVec_lt_iff_slt (a b : BitVec 32) : ISize32.ofBitVec a < ISize32.ofBitVec b ↔ a.slt b := Iff.rfl

theorem ISize32.toNatClampNeg_one : (1 : ISize32).toNatClampNeg = 1 := (rfl)

theorem ISize32.toInt_one : (1 : ISize32).toInt = 1 := (rfl)

theorem ISize32.zero_lt_one : (0 : ISize32) < 1 := by simp

theorem ISize32.zero_ne_one : (0 : ISize32) ≠ 1 := by simp

protected theorem ISize32.add_assoc (a b c : ISize32) : a + b + c = a + (b + c) :=
  ISize32.toBitVec_inj.1 (BitVec.add_assoc _ _ _)

instance : Std.Associative (α := ISize32) (· + ·) := ⟨ISize32.add_assoc⟩

protected theorem ISize32.add_comm (a b : ISize32) : a + b = b + a := ISize32.toBitVec_inj.1 (BitVec.add_comm _ _)

instance : Std.Commutative (α := ISize32) (· + ·) := ⟨ISize32.add_comm⟩

@[simp] protected theorem ISize32.add_zero (a : ISize32) : a + 0 = a := ISize32.toBitVec_inj.1 (BitVec.add_zero _)

@[simp] protected theorem ISize32.zero_add (a : ISize32) : 0 + a = a := ISize32.toBitVec_inj.1 (BitVec.zero_add _)

instance : Std.LawfulIdentity (α := ISize32) (· + ·) 0 where
  left_id := ISize32.zero_add
  right_id := ISize32.add_zero

@[simp] protected theorem ISize32.sub_zero (a : ISize32) : a - 0 = a := ISize32.toBitVec_inj.1 (BitVec.sub_zero _)

@[simp] protected theorem ISize32.zero_sub (a : ISize32) : 0 - a = -a := ISize32.toBitVec_inj.1 (BitVec.zero_sub _)

@[simp] protected theorem ISize32.sub_self (a : ISize32) : a - a = 0 := ISize32.toBitVec_inj.1 (BitVec.sub_self _)

protected theorem ISize32.add_left_neg (a : ISize32) : -a + a = 0 := ISize32.toBitVec_inj.1 (BitVec.add_left_neg _)

protected theorem ISize32.add_right_neg (a : ISize32) : a + -a = 0 := ISize32.toBitVec_inj.1 (BitVec.add_right_neg _)

@[simp] protected theorem ISize32.sub_add_cancel (a b : ISize32) : a - b + b = a :=
  ISize32.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)

protected theorem ISize32.eq_sub_iff_add_eq {a b c : ISize32} : a = c - b ↔ a + b = c := by
  simpa [← ISize32.toBitVec_inj] using BitVec.eq_sub_iff_add_eq

protected theorem ISize32.sub_eq_iff_eq_add {a b c : ISize32} : a - b = c ↔ a = c + b := by
  simpa [← ISize32.toBitVec_inj] using BitVec.sub_eq_iff_eq_add

@[simp] protected theorem ISize32.neg_neg {a : ISize32} : - -a = a := ISize32.toBitVec_inj.1 BitVec.neg_neg

@[simp] protected theorem ISize32.neg_inj {a b : ISize32} : -a = -b ↔ a = b := by simp [← ISize32.toBitVec_inj]
@[simp] protected theorem Int64.neg_inj {a b : Int64} : -a = -b ↔ a = b := by simp [← Int64.toBitVec_inj]

@[simp] protected theorem ISize32.neg_ne_zero {a : ISize32} : -a ≠ 0 ↔ a ≠ 0 := by simp [← ISize32.toBitVec_inj]
@[simp] protected theorem Int64.neg_ne_zero {a : Int64} : -a ≠ 0 ↔ a ≠ 0 := by simp [← Int64.toBitVec_inj]

protected theorem ISize32.neg_add {a b : ISize32} : - (a + b) = -a - b := ISize32.toBitVec_inj.1 BitVec.neg_add

@[simp] protected theorem ISize32.sub_neg {a b : ISize32} : a - -b = a + b := ISize32.toBitVec_inj.1 BitVec.sub_neg

@[simp] protected theorem ISize32.neg_sub {a b : ISize32} : -(a - b) = b - a := by
  rw [ISize32.sub_eq_add_neg, ISize32.neg_add, ISize32.sub_neg, ISize32.add_comm, ← ISize32.sub_eq_add_neg]

protected theorem ISize32.sub_sub (a b c : ISize32) : a - b - c = a - (b + c) := by
  simp [ISize32.sub_eq_add_neg, ISize32.add_assoc, ISize32.neg_add]

@[simp] protected theorem ISize32.add_left_inj {a b : ISize32} (c : ISize32) : (a + c = b + c) ↔ a = b := by
  simp [← ISize32.toBitVec_inj]

@[simp] protected theorem ISize32.add_right_inj {a b : ISize32} (c : ISize32) : (c + a = c + b) ↔ a = b := by
  simp [← ISize32.toBitVec_inj]

@[simp] protected theorem ISize32.sub_left_inj {a b : ISize32} (c : ISize32) : (a - c = b - c) ↔ a = b := by
  simp [← ISize32.toBitVec_inj]

@[simp] protected theorem ISize32.sub_right_inj {a b : ISize32} (c : ISize32) : (c - a = c - b) ↔ a = b := by
  simp [← ISize32.toBitVec_inj]

@[simp] theorem ISize32.add_eq_right {a b : ISize32} : a + b = b ↔ a = 0 := by
  simp [← ISize32.toBitVec_inj]

@[simp] theorem ISize32.add_eq_left {a b : ISize32} : a + b = a ↔ b = 0 := by
  simp [← ISize32.toBitVec_inj]

@[simp] theorem ISize32.right_eq_add {a b : ISize32} : b = a + b ↔ a = 0 := by
  simp [← ISize32.toBitVec_inj]

@[simp] theorem ISize32.left_eq_add {a b : ISize32} : a = a + b ↔ b = 0 := by
  simp [← ISize32.toBitVec_inj]

protected theorem ISize32.mul_comm (a b : ISize32) : a * b = b * a := ISize32.toBitVec_inj.1 (BitVec.mul_comm _ _)

instance : Std.Commutative (α := ISize32) (· * ·) := ⟨ISize32.mul_comm⟩

protected theorem ISize32.mul_assoc (a b c : ISize32) : a * b * c = a * (b * c) := ISize32.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)

instance : Std.Associative (α := ISize32) (· * ·) := ⟨ISize32.mul_assoc⟩

@[simp] theorem ISize32.mul_one (a : ISize32) : a * 1 = a := ISize32.toBitVec_inj.1 (BitVec.mul_one _)

@[simp] theorem ISize32.one_mul (a : ISize32) : 1 * a = a := ISize32.toBitVec_inj.1 (BitVec.one_mul _)

instance : Std.LawfulCommIdentity (α := ISize32) (· * ·) 1 where
  right_id := ISize32.mul_one

@[simp] theorem ISize32.mul_zero {a : ISize32} : a * 0 = 0 := ISize32.toBitVec_inj.1 BitVec.mul_zero

@[simp] theorem ISize32.zero_mul {a : ISize32} : 0 * a = 0 := ISize32.toBitVec_inj.1 BitVec.zero_mul

@[simp] protected theorem ISize32.pow_zero (x : ISize32) : x ^ 0 = 1 := (rfl)

protected theorem ISize32.pow_succ (x : ISize32) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)

protected theorem ISize32.mul_add {a b c : ISize32} : a * (b + c) = a * b + a * c :=
    ISize32.toBitVec_inj.1 BitVec.mul_add

protected theorem ISize32.add_mul {a b c : ISize32} : (a + b) * c = a * c + b * c := by
  rw [ISize32.mul_comm, ISize32.mul_add, ISize32.mul_comm a c, ISize32.mul_comm c b]

protected theorem ISize32.mul_succ {a b : ISize32} : a * (b + 1) = a * b + a := by simp [ISize32.mul_add]

protected theorem ISize32.succ_mul {a b : ISize32} : (a + 1) * b = a * b + b := by simp [ISize32.add_mul]

protected theorem ISize32.two_mul {a : ISize32} : 2 * a = a + a := ISize32.toBitVec_inj.1 BitVec.two_mul

protected theorem ISize32.mul_two {a : ISize32} : a * 2 = a + a := ISize32.toBitVec_inj.1 BitVec.mul_two

protected theorem ISize32.neg_mul (a b : ISize32) : -a * b = -(a * b) := ISize32.toBitVec_inj.1 (BitVec.neg_mul _ _)

protected theorem ISize32.mul_neg (a b : ISize32) : a * -b = -(a * b) := ISize32.toBitVec_inj.1 (BitVec.mul_neg _ _)

protected theorem ISize32.neg_mul_neg (a b : ISize32) : -a * -b = a * b := ISize32.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)

protected theorem ISize32.neg_mul_comm (a b : ISize32) : -a * b = a * -b := ISize32.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)

protected theorem ISize32.mul_sub {a b c : ISize32} : a * (b - c) = a * b - a * c := ISize32.toBitVec_inj.1 BitVec.mul_sub

protected theorem ISize32.sub_mul {a b c : ISize32} : (a - b) * c = a * c - b * c := by
  rw [ISize32.mul_comm, ISize32.mul_sub, ISize32.mul_comm, ISize32.mul_comm c]

theorem ISize32.neg_add_mul_eq_mul_not {a b : ISize32} : -(a + a * b) = a * ~~~b :=
  ISize32.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not

theorem ISize32.neg_mul_not_eq_add_mul {a b : ISize32} : -(a * ~~~b) = a + a * b :=
  ISize32.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul

protected theorem ISize32.le_of_lt {a b : ISize32} : a < b → a ≤ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le] using Int.le_of_lt

protected theorem ISize32.lt_of_le_of_ne {a b : ISize32} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← ISize32.toInt_inj] using (Int.lt_iff_le_and_ne.2 ⟨·, ·⟩)

protected theorem ISize32.lt_iff_le_and_ne {a b : ISize32} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← ISize32.toInt_inj] using Int.lt_iff_le_and_ne

@[simp] protected theorem ISize32.lt_irrefl {a : ISize32} : ¬a < a := by simp [lt_iff_toInt_lt]
@[simp] protected theorem Int64.lt_irrefl {a : Int64} : ¬a < a := by simp [lt_iff_toInt_lt]

protected theorem ISize32.lt_of_le_of_lt {a b c : ISize32} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_le_of_lt

protected theorem ISize32.lt_of_lt_of_le {a b c : ISize32} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_lt_of_le

@[simp] theorem ISize32.minValue_le (a : ISize32) : minValue ≤ a := by simpa [le_iff_toInt_le] using a.minValue_le_toInt

@[simp] theorem ISize32.le_maxValue (a : ISize32) : a ≤ maxValue := by simpa [le_iff_toInt_le] using a.toInt_le

@[simp] theorem ISize32.not_lt_minValue {a : ISize32} : ¬a < minValue :=
  fun h => ISize32.lt_irrefl (ISize32.lt_of_le_of_lt a.minValue_le h)

@[simp] theorem ISize32.not_maxValue_lt {a : ISize32} : ¬maxValue < a :=
  fun h => ISize32.lt_irrefl (ISize32.lt_of_lt_of_le h a.le_maxValue)

@[simp] protected theorem ISize32.le_refl (a : ISize32) : a ≤ a := by simp [ISize32.le_iff_toInt_le]
@[simp] protected theorem Int64.le_refl (a : Int64) : a ≤ a := by simp [Int64.le_iff_toInt_le]

protected theorem ISize32.le_rfl {a : ISize32} : a ≤ a := ISize32.le_refl _

protected theorem ISize32.le_antisymm_iff {a b : ISize32} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨by rintro rfl; simp, by simpa [← ISize32.toInt_inj, le_iff_toInt_le] using Int.le_antisymm⟩

protected theorem ISize32.le_antisymm {a b : ISize32} : a ≤ b → b ≤ a → a = b := by simpa using ISize32.le_antisymm_iff.2

@[simp] theorem ISize32.le_minValue_iff {a : ISize32} : a ≤ minValue ↔ a = minValue :=
  ⟨fun h => ISize32.le_antisymm h a.minValue_le, by rintro rfl; simp⟩

@[simp] theorem ISize32.maxValue_le_iff {a : ISize32} : maxValue ≤ a ↔ a = maxValue :=
  ⟨fun h => ISize32.le_antisymm a.le_maxValue h, by rintro rfl; simp⟩

@[simp] protected theorem ISize32.zero_div {a : ISize32} : 0 / a = 0 := ISize32.toBitVec_inj.1 BitVec.zero_sdiv

@[simp] protected theorem ISize32.div_zero {a : ISize32} : a / 0 = 0 := ISize32.toBitVec_inj.1 BitVec.sdiv_zero

@[simp] protected theorem ISize32.div_one {a : ISize32} : a / 1 = a := ISize32.toBitVec_inj.1 BitVec.sdiv_one

protected theorem ISize32.div_self {a : ISize32} : a / a = if a = 0 then 0 else 1 := by
  simp [← ISize32.toBitVec_inj, apply_ite]

@[simp] protected theorem ISize32.mod_zero {a : ISize32} : a % 0 = a := ISize32.toBitVec_inj.1 BitVec.srem_zero

@[simp] protected theorem ISize32.zero_mod {a : ISize32} : 0 % a = 0 := ISize32.toBitVec_inj.1 BitVec.zero_srem

@[simp] protected theorem ISize32.mod_one {a : ISize32} : a % 1 = 0 := ISize32.toBitVec_inj.1 BitVec.srem_one

@[simp] protected theorem ISize32.mod_self {a : ISize32} : a % a = 0 := ISize32.toBitVec_inj.1 BitVec.srem_self

@[simp] protected theorem ISize32.not_lt {a b : ISize32} : ¬ a < b ↔ b ≤ a := by
  simp [lt_iff_toBitVec_slt, le_iff_toBitVec_sle, BitVec.sle_eq_not_slt]

protected theorem ISize32.le_trans {a b c : ISize32} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [le_iff_toInt_le] using Int.le_trans

protected theorem ISize32.lt_trans {a b c : ISize32} : a < b → b < c → a < c := by
  simpa [lt_iff_toInt_lt] using Int.lt_trans

protected theorem ISize32.le_total (a b : ISize32) : a ≤ b ∨ b ≤ a := by
  simpa [le_iff_toInt_le] using Int.le_total _ _

protected theorem ISize32.lt_asymm {a b : ISize32} : a < b → ¬b < a :=
  fun hab hba => ISize32.lt_irrefl (ISize32.lt_trans hab hba)

instance ISize32.instIsLinearOrder : IsLinearOrder ISize32 := by
  apply IsLinearOrder.of_le
  case le_antisymm => constructor; apply ISize32.le_antisymm
  case le_total => constructor; apply ISize32.le_total
  case le_trans => constructor; apply ISize32.le_trans

instance : LawfulOrderLT ISize32 where
  lt_iff := by
    simp [← ISize32.not_le, Decidable.imp_iff_not_or, Std.Total.total]

protected theorem ISize32.add_neg_eq_sub {a b : ISize32} : a + -b = a - b := ISize32.toBitVec_inj.1 BitVec.add_neg_eq_sub

theorem ISize32.neg_eq_neg_one_mul (a : ISize32) : -a = -1 * a := ISize32.toInt_inj.1 (by simp)

@[simp] protected theorem ISize32.add_sub_cancel (a b : ISize32) : a + b - b = a := ISize32.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)

protected theorem ISize32.lt_or_lt_of_ne {a b : ISize32} : a ≠ b → a < b ∨ b < a := by
  simp [lt_iff_toInt_lt, ← ISize32.toInt_inj]; omega

protected theorem ISize32.lt_or_le (a b : ISize32) : a < b ∨ b ≤ a := by
  simp [lt_iff_toInt_lt, le_iff_toInt_le]; omega

protected theorem ISize32.le_or_lt (a b : ISize32) : a ≤ b ∨ b < a := (b.lt_or_le a).symm

protected theorem ISize32.le_of_eq {a b : ISize32} : a = b → a ≤ b := (· ▸ ISize32.le_rfl)

protected theorem ISize32.le_iff_lt_or_eq {a b : ISize32} : a ≤ b ↔ a < b ∨ a = b := by
  simp [← ISize32.toInt_inj, le_iff_toInt_le, lt_iff_toInt_lt]; omega

protected theorem ISize32.lt_or_eq_of_le {a b : ISize32} : a ≤ b → a < b ∨ a = b := ISize32.le_iff_lt_or_eq.mp

theorem ISize32.toInt_eq_toNatClampNeg {a : ISize32} (ha : 0 ≤ a) : a.toInt = a.toNatClampNeg := by
  simpa only [← toNat_toInt, Int.eq_natCast_toNat, le_iff_toInt_le] using ha

@[simp] theorem USize32.toISize32_add (a b : USize32) : (a + b).toISize32 = a.toISize32 + b.toISize32 := (rfl)

@[simp] theorem USize32.toISize32_neg (a : USize32) : (-a).toISize32 = -a.toISize32 := (rfl)

@[simp] theorem USize32.toISize32_sub (a b : USize32) : (a - b).toISize32 = a.toISize32 - b.toISize32 := (rfl)

@[simp] theorem USize32.toISize32_mul (a b : USize32) : (a * b).toISize32 = a.toISize32 * b.toISize32 := (rfl)

@[simp] theorem ISize32.toUSize32_add (a b : ISize32) : (a + b).toUSize32 = a.toUSize32 + b.toUSize32 := (rfl)

@[simp] theorem ISize32.toUSize32_neg (a : ISize32) : (-a).toUSize32 = -a.toUSize32 := (rfl)

@[simp] theorem ISize32.toUSize32_sub (a b : ISize32) : (a - b).toUSize32 = a.toUSize32 - b.toUSize32 := (rfl)

@[simp] theorem ISize32.toUSize32_mul (a b : ISize32) : (a * b).toUSize32 = a.toUSize32 * b.toUSize32 := (rfl)

theorem ISize32.toNatClampNeg_le {a b : ISize32} (hab : a ≤ b) : a.toNatClampNeg ≤ b.toNatClampNeg := by
  rw [← ISize32.toNat_toInt, ← ISize32.toNat_toInt]
  exact Int.toNat_le_toNat (ISize32.le_iff_toInt_le.1 hab)

theorem ISize32.toUSize32_le {a b : ISize32} (ha : 0 ≤ a) (hab : a ≤ b) : a.toUSize32 ≤ b.toUSize32 := by
  rw [USize32.le_iff_toNat_le, toNat_toUSize32_of_le ha, toNat_toUSize32_of_le (ISize32.le_trans ha hab)]
  exact ISize32.toNatClampNeg_le hab

theorem ISize32.zero_le_ofNat_of_lt {a : Nat} (ha : a < 2 ^ 31) : 0 ≤ ISize32.ofNat a := by
  rw [le_iff_toInt_le, toInt_ofNat_of_lt ha, ISize32.toInt_zero]
  exact Int.natCast_nonneg _

protected theorem ISize32.sub_nonneg_of_le {a b : ISize32} (hb : 0 ≤ b) (hab : b ≤ a) : 0 ≤ a - b := by
  rw [← ofNat_toNatClampNeg _ hb, ← ofNat_toNatClampNeg _ (ISize32.le_trans hb hab),
    ← ofNat_sub _ _ (ISize32.toNatClampNeg_le hab)]
  exact ISize32.zero_le_ofNat_of_lt (Nat.sub_lt_of_lt a.toNatClampNeg_lt)

theorem ISize32.toNatClampNeg_sub_of_le {a b : ISize32} (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b).toNatClampNeg = a.toNatClampNeg - b.toNatClampNeg := by
  rw [← toNat_toUSize32_of_le (ISize32.sub_nonneg_of_le hb hab), toUSize32_sub,
    USize32.toNat_sub_of_le _ _ (ISize32.toUSize32_le hb hab),
    ← toNat_toUSize32_of_le (ISize32.le_trans hb hab), ← toNat_toUSize32_of_le hb]

theorem ISize32.toInt_sub_of_le (a b : ISize32) (hb : 0 ≤ b) (h : b ≤ a) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [ISize32.toInt_eq_toNatClampNeg (ISize32.sub_nonneg_of_le hb h),
    ISize32.toInt_eq_toNatClampNeg (ISize32.le_trans hb h), ISize32.toInt_eq_toNatClampNeg hb,
    ISize32.toNatClampNeg_sub_of_le hb h, Int.ofNat_sub]
  exact ISize32.toNatClampNeg_le h

protected theorem ISize32.sub_le {a b : ISize32} (hb : 0 ≤ b) (hab : b ≤ a) : a - b ≤ a := by
  simp_all [le_iff_toInt_le, ISize32.toInt_sub_of_le _ _ hb hab]; omega

protected theorem ISize32.sub_lt {a b : ISize32} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  simp_all [lt_iff_toInt_lt, ISize32.toInt_sub_of_le _ _ (ISize32.le_of_lt hb) hab]; omega

protected theorem ISize32.ne_of_lt {a b : ISize32} : a < b → a ≠ b := by
  simpa [ISize32.lt_iff_toInt_lt, ← ISize32.toInt_inj] using Int.ne_of_lt

@[simp] theorem ISize32.toInt_mod (a b : ISize32) : (a % b).toInt = a.toInt.tmod b.toInt := by
  rw [← toInt_toBitVec, ISize32.toBitVec_mod, BitVec.toInt_srem, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem Int8.toISize32_mod (a b : Int8) : (a % b).toISize32 = a.toISize32 % b.toISize32 := ISize32.toInt.inj (by simp)

@[simp] theorem Int16.toISize32_mod (a b : Int16) : (a % b).toISize32 = a.toISize32 % b.toISize32 := ISize32.toInt.inj (by simp)

@[simp] theorem ISize32.toInt64_mod (a b : ISize32) : (a % b).toInt64 = a.toInt64 % b.toInt64 := Int64.toInt.inj (by simp)

@[simp] theorem ISize32.toISize_mod (a b : ISize32) : (a % b).toISize = a.toISize % b.toISize := ISize.toInt.inj (by simp)

theorem ISize32.ofInt_tmod {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : ISize32.ofInt (a.tmod b) = ISize32.ofInt a % ISize32.ofInt b := by
  rw [ISize32.ofInt_eq_iff_bmod_eq_toInt, ← toInt_bmod_size, toInt_mod, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂

theorem ISize32.ofInt_eq_ofIntLE_mod {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize32.ofInt (a.tmod b) = ISize32.ofIntLE a ha₁ ha₂ % ISize32.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tmod ha₁ ha₂ hb₁ hb₂]

theorem ISize32.ofNat_mod {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ISize32.ofNat (a % b) = ISize32.ofNat a % ISize32.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tmod,
    ofInt_tmod (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/GrindInstances/ToInt.lean
-- Target: Hax/MissingLean/Init/GrindInstances/ToInt.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean.Grind

instance : ToInt USize32 (.uint 32) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := USize32.toNat_inj.mp (Int.ofNat_inj.mp w)
  toInt_mem x := by simpa using Int.lt_toNat.mp (USize32.toNat_lt x)

@[simp] theorem toInt_uisize32 (x : USize32) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Zero USize32 (.uint 32) where
  toInt_zero := by simp

instance : ToInt.OfNat USize32 (.uint 32) where
  toInt_ofNat x := by simp; rfl

instance : ToInt.Add USize32 (.uint 32) where
  toInt_add x y := by simp

instance : ToInt.Mul USize32 (.uint 32) where
  toInt_mul x y := by simp

instance : ToInt.Mod USize32 (.uint 32) where
  toInt_mod x y := by simp

instance : ToInt.Div USize32 (.uint 32) where
  toInt_div x y := by simp

instance : ToInt.LE USize32 (.uint 32) where
  le_iff x y := by simpa using USize32.le_iff_toBitVec_le

instance : ToInt.LT USize32 (.uint 32) where
  lt_iff x y := by simpa using USize32.lt_iff_toBitVec_lt

instance : ToInt ISize32 (.sint 32) where
  toInt x := x.toInt
  toInt_inj x y w := ISize32.toInt_inj.mp w
  toInt_mem x := by simp; exact ⟨ISize32.le_toInt x, ISize32.toInt_lt x⟩

@[simp] theorem toInt_isize32 (x : ISize32) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Zero ISize32 (.sint 32) where
  toInt_zero := by
    -- simp -- FIXME: succeeds, but generates a `(kernel) application type mismatch` error!
    change (0 : ISize32).toInt = _
    rw [ISize32.toInt_zero]

instance : ToInt.OfNat ISize32 (.sint 32) where
  toInt_ofNat x := by
    rw [toInt_isize32, ISize32.toInt_ofNat, ISize32.size, Int.bmod_eq_emod, IntInterval.wrap]
    simp
    split <;> omega

instance : ToInt.Add ISize32 (.sint 32) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.Mul ISize32 (.sint 32) where
  toInt_mul x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.LE ISize32 (.sint 32) where
  le_iff x y := by simpa using ISize32.le_iff_toInt_le

instance : ToInt.LT ISize32 (.sint 32) where
  lt_iff x y := by simpa using ISize32.lt_iff_toInt_lt

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/GrindInstances/Ring/SInt.lean
-- Target: Hax/MissingLean/Init/GrindInstances/Ring/SInt.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean Grind

@[expose]
def ISize32.natCast : NatCast ISize32 where
  natCast x := ISize32.ofNat x

@[expose]
def ISize32.intCast : IntCast ISize32 where
  intCast x := ISize32.ofInt x

attribute [local instance] ISize32.intCast in
theorem ISize32.intCast_neg (i : Int) : ((-i : Int) : ISize32) = -(i : ISize32) :=
  ISize32.ofInt_neg _

attribute [local instance] ISize32.intCast in
theorem ISize32.intCast_ofNat (x : Nat) : (OfNat.ofNat (α := Int) x : ISize32) = OfNat.ofNat x := ISize32.ofInt_eq_ofNat

attribute [local instance] ISize32.natCast ISize32.intCast in
instance : CommRing ISize32 where
  nsmul := ⟨(· * ·)⟩
  zsmul := ⟨(· * ·)⟩
  add_assoc := ISize32.add_assoc
  add_comm := ISize32.add_comm
  add_zero := ISize32.add_zero
  neg_add_cancel := ISize32.add_left_neg
  mul_assoc := ISize32.mul_assoc
  mul_comm := ISize32.mul_comm
  mul_one := ISize32.mul_one
  one_mul := ISize32.one_mul
  left_distrib _ _ _ := ISize32.mul_add
  right_distrib _ _ _ := ISize32.add_mul
  zero_mul _ := ISize32.zero_mul
  mul_zero _ := ISize32.mul_zero
  sub_eq_add_neg := ISize32.sub_eq_add_neg
  pow_zero := ISize32.pow_zero
  pow_succ := ISize32.pow_succ
  ofNat_succ x := ISize32.ofNat_add x 1
  intCast_neg := ISize32.ofInt_neg
  neg_zsmul i x := by
    change (-i : Int) * x = - (i * x)
    simp [ISize32.intCast_neg, ISize32.neg_mul]
  zsmul_natCast_eq_nsmul n a := congrArg (· * a) (ISize32.intCast_ofNat _)

instance : IsCharP ISize32 (2 ^ 32) := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = ISize32.ofInt x := rfl
    rw [this]
    simp [ISize32.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_bmod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, Int.ofNat_dvd_right])

example : ToInt.Add ISize32 (.sint 32) := inferInstance

example : ToInt.Neg ISize32 (.sint 32) := inferInstance

example : ToInt.Sub ISize32 (.sint 32) := inferInstance

instance : ToInt.Pow ISize32 (.sint 32) := ToInt.pow_of_semiring (by simp)

-- ──────────────────────────────────────────────────────────────────────
-- Source: Init/GrindInstances/Ring/UInt.lean
-- Target: Hax/MissingLean/Init/GrindInstances/Ring/UInt.lean
-- ──────────────────────────────────────────────────────────────────────

open Lean Grind

set_option autoImplicit true

namespace USize32

/-- Variant of `USize32.ofNat_mod_size` replacing `2 ^ 32` with `4294967296`.-/
theorem ofNat_mod_size' : ofNat (x % 4294967296) = ofNat x := ofNat_mod_size

@[expose]
def natCast : NatCast USize32 where
  natCast x := USize32.ofNat x

@[expose]
def intCast : IntCast USize32 where
  intCast x := USize32.ofInt x

attribute [local instance] natCast intCast

theorem intCast_neg (x : Int) : ((-x : Int) : USize32) = - (x : USize32) := by
  simp only [Int.cast, IntCast.intCast, USize32.ofInt_neg]

theorem intCast_ofNat (x : Nat) : (OfNat.ofNat (α := Int) x : USize32) = OfNat.ofNat x := by
    -- A better proof would be welcome!
    simp only [Int.cast, IntCast.intCast]
    rw [USize32.ofInt]
    rw [Int.toNat_emod (Int.zero_le_ofNat x) (by decide)]
    erw [Int.toNat_natCast]
    rw [Int.toNat_pow_of_nonneg (by decide)]
    simp only [ofNat, BitVec.ofNat, Fin.Internal.ofNat_eq_ofNat, Fin.ofNat, Int.reduceToNat, Nat.dvd_refl,
      Nat.mod_mod_of_dvd, instOfNat]

end USize32

attribute [local instance] USize32.natCast USize32.intCast in
instance : CommRing USize32 where
  nsmul := ⟨(· * ·)⟩
  zsmul := ⟨(· * ·)⟩
  add_assoc := USize32.add_assoc
  add_comm := USize32.add_comm
  add_zero := USize32.add_zero
  neg_add_cancel := USize32.add_left_neg
  mul_assoc := USize32.mul_assoc
  mul_comm := USize32.mul_comm
  mul_one := USize32.mul_one
  one_mul := USize32.one_mul
  left_distrib _ _ _ := USize32.mul_add
  right_distrib _ _ _ := USize32.add_mul
  zero_mul _ := USize32.zero_mul
  mul_zero _ := USize32.mul_zero
  sub_eq_add_neg := USize32.sub_eq_add_neg
  pow_zero := USize32.pow_zero
  pow_succ := USize32.pow_succ
  ofNat_succ x := USize32.ofNat_add x 1
  intCast_neg := USize32.ofInt_neg
  intCast_ofNat := USize32.intCast_ofNat
  neg_zsmul i a := by
    change (-i : Int) * a = - (i * a)
    simp [USize32.intCast_neg, USize32.neg_mul]
  zsmul_natCast_eq_nsmul n a := congrArg (· * a) (USize32.intCast_ofNat _)

instance : IsCharP USize32 4294967296 := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = USize32.ofNat x := rfl
    simp [this, USize32.ofNat_eq_iff_mod_eq_toNat])

-- Verify we can derive the instances showing how `toInt` interacts with operations:
example : ToInt.Add USize32 (.uint 32) := inferInstance
example : ToInt.Neg USize32 (.uint 32) := inferInstance
example : ToInt.Sub USize32 (.uint 32) := inferInstance

instance : ToInt.Pow USize32 (.uint 32) := ToInt.pow_of_semiring (by simp)
