-- Missing core-model specs, to be upstreamed into the Hax library.
--
-- These mirror the specs on the `specs` branch of `cryspen/rust-core-models`
-- (lean/CoreModels/Spec/Core/{Array,Convert}.lean). The slice→`[T; N]`
-- `try_from` is modelled via `rust_primitives.slice.array_from_fn`; its spec is
-- proved here (`array_from_fn` succeeds because every element read is in range,
-- shown by induction on the `foldlM` over `range N`).
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

/-- `array_from_fn`'s `foldlM` over `range` succeeds: every step indexes the
(unchanged) slice `x` at an in-range position, so it never fails. -/
private theorem foldlM_index_ok {T : Type} (x : Slice T) (hx : x.val.length ≤ Usize.max) :
    ∀ (l : List Nat) (acc : List T × Slice T), acc.2 = x → (∀ i ∈ l, i < x.val.length) →
      ∃ res : List T × Slice T,
        l.foldlM (fun (s : List T × Slice T) (i : Nat) => do
          let d ← (do let t ← Slice.index_usize s.2 ⟨BitVec.ofNat _ i⟩; Result.ok (t, s.2))
          Result.ok (s.1 ++ [d.1], d.2)) acc = Result.ok res ∧ res.2 = x := by
  intro l
  induction l with
  | nil => exact fun acc h _ => ⟨acc, rfl, h⟩
  | cons i l ih =>
    intro acc hacc hall
    have hi : i < x.val.length := hall i (by simp)
    have hidx : (⟨BitVec.ofNat _ i⟩ : Usize).val = i := by
      simp only [UScalar.val, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; scalar_tac
    have hlt : (⟨BitVec.ofNat _ i⟩ : Usize).val < acc.2.val.length := by rw [hacc, hidx]; exact hi
    obtain ⟨t, ht⟩ : ∃ t, Slice.index_usize acc.2 ⟨BitVec.ofNat _ i⟩ = Result.ok t := by
      simp only [Slice.index_usize, Std.Slice.getElem?_Usize_eq]
      rw [List.getElem?_eq_getElem hlt]; exact ⟨_, rfl⟩
    simp only [List.foldlM_cons, ht, bind_tc_ok]
    exact ih (acc.1 ++ [t], acc.2) hacc (fun j hj => hall j (by simp [hj]))

/-- The slice→`[T; N]` `try_from` (modelled via `array_from_fn`) succeeds (returns
`Ok`) whenever the slice has length `N`: every element read is in range. -/
private theorem array_from_fn_ok {T : Type} (N : Std.Usize) (cpy : core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    ∃ a, rust_primitives.slice.array_from_fn N
      (core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
        N cpy) s = Result.ok a := by
  have hx : s.val.length ≤ Usize.max := by scalar_tac
  obtain ⟨res, hres, -⟩ := foldlM_index_ok s hx (List.range N.val) ([], s) rfl
    (fun i hi => by rw [List.mem_range] at hi; omega)
  unfold rust_primitives.slice.array_from_fn
  simp only
    [core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT,
     core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut,
     rust_primitives.slice.slice_index]
  split
  · rename_i e heq; rw [hres] at heq; exact absurd heq (by simp)
  · rename_i heq; rw [hres] at heq; exact absurd heq (by simp)
  · exact ⟨_, rfl⟩

/-- The slice→`[T; N]` `try_from` (modelled via `array_from_fn`) succeeds,
returning `Ok`, whenever the slice has length `N`. -/
@[spec]
theorem core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from_spec
    {T : Type} {N : Std.Usize} (cpy : core.marker.Copy T) (s : Slice T)
    (hlen : s.val.length = N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from N cpy s
    ⦃ ⇓ r => ⌜ ∃ a, r = core.result.Result.Ok a ⌝ ⦄ := by
  obtain ⟨a, ha⟩ := array_from_fn_ok N cpy s hlen
  have hN : (⟨BitVec.ofNat _ s.val.length⟩ : Usize) = N := by
    apply UScalar.eq_of_val_eq
    simp only [UScalar.val, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by scalar_tac)]; exact hlen
  unfold core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
  simp only [core.slice.Slice.len, rust_primitives.sequence.seq_len, Slice.len]
  mvcgen [ha, hN] <;> simp_all [Slice.length]

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
