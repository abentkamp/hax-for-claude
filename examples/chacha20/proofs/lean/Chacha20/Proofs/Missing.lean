-- Missing core-model specs, to be upstreamed into the Hax library.
--
-- These mirror the specs on the `specs` branch of `cryspen/rust-core-models`
-- (lean/CoreModels/Spec/Core/{Array,Convert}.lean). The slice→`[T; N]`
-- `try_from` is modelled via `rust_primitives.slice.array_from_fn`; proving its
-- spec requires the `array_from_fn` spec. That proof is deferred here (`sorry`)
-- and will be provided once these live in the Hax library.
import Aeneas
import CoreModels
import Chacha20.Extraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
open Std.Do

set_option mvcgen.warning false
set_option maxHeartbeats 1000000

namespace CoreModels

/-- The slice→`[T; N]` `try_from` (modelled via `array_from_fn`) succeeds,
returning `Ok`, whenever the slice has length `N`.

Deferred (`sorry`): the corresponding proved spec on the `rust-core-models`
`specs` branch phrases the result as `Ok (Std.Array.make N s.val _)`, which needs
the `array_from_fn` spec; the existential form below is all we need for
panic-freedom. -/
@[spec]
theorem core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from_spec
    {T : Type} {N : Std.Usize} (cpy : core.marker.Copy T) (s : Slice T)
    (hlen : s.val.length = N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from N cpy s
    ⦃ ⇓ r => ⌜ ∃ a, r = core.result.Result.Ok a ⌝ ⦄ := by
  sorry

/-- Indexing a slice by a `Range<usize>` (`s[start..end]`): panic-free when
`start ≤ end ≤ s.length`, and the result has length `end - start`. -/
@[spec]
theorem core.Slice.Insts.CoreOpsIndexIndex.index_range_spec {T : Type} [Inhabited T]
    (s : Slice T) (r : core.ops.range.Range Std.Usize)
    (h0 : r.start.val < r.end.val) (h1 : r.end.val ≤ s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s r
    ⦃ ⇓ r' => ⌜ r'.val.length = r.end.val - r.start.val ⌝ ⦄ := by
  mvcgen [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_slice, rust_primitives.slice.slice_length,
    -Slice.subslice_spec.mvcgen_spec, Slice.subslice]
    <;> scalar_tac

/-- `Result::unwrap` is panic-free when the value is known to be `Ok`. -/
@[spec]
theorem core.result.Result.unwrap_ok_spec {T E : Type}
    (dbg : core.fmt.Debug E) (r : core.result.Result T E)
    (h : ∃ a, r = core.result.Result.Ok a) :
    ⦃ ⌜ True ⌝ ⦄
    core.result.Result.unwrap dbg r
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  obtain ⟨a, rfl⟩ := h
  simp only [core.result.Result.unwrap]
  mvcgen

end CoreModels
