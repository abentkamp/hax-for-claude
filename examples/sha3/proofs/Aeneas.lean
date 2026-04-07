import Hax

namespace Aeneas

namespace Std

abbrev Usize := USize64
abbrev U64 := UInt64

scoped notation:max n "#usize" => (USize64.ofNat n)
scoped notation:max n "#u64" => (UInt64.ofNat n)

end Std

end Aeneas
