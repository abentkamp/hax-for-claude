import Hax

namespace Aeneas

abbrev Result := RustM
abbrev Error := _root_.Error
abbrev ControlFlow := core_models.ops.control_flow.ControlFlow

namespace Result

def ok {α : Type} (v : α) : Result α := .ok v

end Result

def lift {α : Type} (x : α) : Result α := .ok x

namespace Std

abbrev Usize := USize64
abbrev U64 := UInt64

scoped notation:max n "#usize" => (USize64.ofNat n)
scoped notation:max n "#u64" => (UInt64.ofNat n)

-- Checked arithmetic returning Result
instance : HMul Usize Usize (Result Usize) where
  hMul x y := x *? y

instance : HAdd Usize Usize (Result Usize) where
  hAdd x y := x +? y

instance : HMul U64 U64 (Result U64) where
  hMul x y := x *? y

instance : HAdd U64 U64 (Result U64) where
  hAdd x y := x +? y

-- LT / DecidableLT for Usize (comparison used in if-conditions)
instance : LT Usize := inferInstanceAs (LT USize64)
instance : DecidableLT Usize := inferInstanceAs (DecidableLT USize64)

-- XOR for U64 (pure, already available on UInt64)
instance : HXor U64 U64 U64 := inferInstanceAs (HXor UInt64 UInt64 UInt64)

end Std

end Aeneas
