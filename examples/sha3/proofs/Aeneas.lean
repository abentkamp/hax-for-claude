import Hax

namespace Aeneas

namespace Std

abbrev Usize := USize64
abbrev U64 := UInt64

scoped notation:max n "#usize" => (USize64.ofNat n)
scoped notation:max n "#u64" => (UInt64.ofNat n)

-- Checked arithmetic: returns RustM (will be aliased to Result later)
instance : HMul Usize Usize (RustM Usize) where
  hMul x y := x *? y

instance : HAdd Usize Usize (RustM Usize) where
  hAdd x y := x +? y

instance : HMul U64 U64 (RustM U64) where
  hMul x y := x *? y

instance : HAdd U64 U64 (RustM U64) where
  hAdd x y := x +? y

-- LT / DecidableLT for Usize (comparison used in if-conditions)
instance : LT Usize := inferInstanceAs (LT USize64)
instance : DecidableLT Usize := inferInstanceAs (DecidableLT USize64)

-- XOR for U64 (pure, already available on UInt64, but re-state for clarity)
instance : HXor U64 U64 U64 := inferInstanceAs (HXor UInt64 UInt64 UInt64)

end Std

end Aeneas
