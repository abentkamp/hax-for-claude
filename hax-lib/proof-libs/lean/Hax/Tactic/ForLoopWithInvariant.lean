import Hax.MissingAeneas
import CoreModels

/-! # `for_loop_with_invariant`

This file implements a tactic `for_loop_with_invariant` allows us to replace occurrences of
Aeneas's `loop` constant with a simpler construct `forLoopWithInvariant`, provided that
the original Rust loops is a for-loop. For now, we only support for-loops over `usize`
without early returns. -/

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Std.Do Elab Parser Tactic Meta
open Aeneas CoreModels
open Aeneas.Std hiding namespace core alloc
namespace Hax

/-- A `for i in s..e` loop carrying its invariant as a marker.

Generic over the loop index type `ι` (any integer type with a `Step ι`
instance — `usize`, `i32`, …). The argument `body : ι → β → Result β` takes the
current index and accumulator and returns the new accumulator. The iterator and
`ControlFlow` plumbing live entirely inside this definition. The argument `_inv`
is a marker read off by the `for_loop_with_invariant` tactic and by spec lemmas;
it has no computational role. -/
def forLoopWithInvariant {ι β : Type} (StepInst : core.iter.range.Step ι)
    (_inv : ι → β → Result Prop)
    (body : ι → β → Result β)
    (iter : core.ops.range.Range ι) (init : β) :
    Result β :=
  loop (fun x : core.ops.range.Range ι × β => do
    let (o, r) ←
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        StepInst x.1
    match o with
    | core.option.Option.None => Result.ok (ControlFlow.done x.2)
    | core.option.Option.Some i => do
        let acc' ← body i x.2
        Result.ok (ControlFlow.cont (r, acc'))) (iter, init)

/-! ## Spec lemmas for `forLoopWithInvariant`

These let `hax_mvcgen` discharge `for i in s..e` loops after the
`for_loop_with_invariant` tactic has rewritten them. Everything is generic over
the loop index type `A` via a measure `v : A → ℤ` (instantiated with the scalar
value embedded in `ℤ`), so it works uniformly for every integer type. The only
type-specific facts are three hypotheses about the `Step A` dictionary
(`clone`, `partial_cmp`, `forward_checked`), discharged once per integer type in
the `@[spec]` instances at the end. -/

section Spec
open Result ControlFlow

private abbrev ResultPS :=
  PostShape.except Aeneas.Std.Error (PostShape.except PUnit PostShape.pure)

private theorem triple_noThrow_elim {α} {x : Result α} {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp] using h

private theorem triple_noThrow_exists_ok {α} {x : Result α} {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail e, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])

private theorem triple_of_ok {α} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Triple, WP.wp, hp, PredTrans.apply]

/-- The `loop` underlying a range for-loop, driven purely by the measure `v`.
Generic over the index type `A`: the body is required to advance the measure by
exactly `1` on each `cont` step, and the induction is on the number of remaining
steps `(v e - v start).toNat`. -/
theorem loop_range_spec {A β : Type} (v : A → ℤ)
    (body : (core.ops.range.Range A × β) →
      Result (ControlFlow (core.ops.range.Range A × β) β))
    (init : β) (s e : A) (inv : A → β → Result Prop)
    (h_le : v s ≤ v e)
    (h_init : (inv s init).holds)
    (h_step : ∀ acc (i : A), v s ≤ v i → v i ≤ v e →
      (inv i acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      body ({ start := i, «end» := e }, acc)
      ⦃ ⇓ r => match r with
        | .cont (iter', acc') =>
          ⌜ v i < v e ∧ iter'.«end» = e ∧ v iter'.start = v i + 1
            ∧ (inv iter'.start acc').holds ⌝
        | .done y => ⌜ (inv e y).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    loop body ({ start := s, «end» := e }, init)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  suffices gen : ∀ (n : Nat) (acc : β) (start : A),
    (v e - v start).toNat = n → v s ≤ v start → v start ≤ v e →
    (inv start acc).holds →
    ⦃ ⌜ True ⌝ ⦄ loop body ({ start := start, «end» := e }, acc)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ by
    exact gen _ init s rfl (le_refl _) h_le h_init
  intro n
  induction n with
  | zero =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok hs
    have hpost := triple_noThrow_elim hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .cont (iter', acc') => simp at hpost; exact absurd hpost.1 (by omega)
    | .done y => simp at hpost; exact triple_of_ok rfl hpost
  | succ n ih =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok hs
    have hpost := triple_noThrow_elim hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .done y => simp at hpost; exact triple_of_ok rfl hpost
    | .cont (iter', acc') =>
      simp at hpost
      obtain ⟨hlt, hend, hstart, hinv'⟩ := hpost
      have hiter : iter' = { start := iter'.start, «end» := e } := by
        cases iter'; cases hend; rfl
      rw [hiter]
      exact ih acc' iter'.start
        (by rw [hstart]; omega) (by rw [hstart]; omega) (by rw [hstart]; omega) hinv'

/-- `Iterator::next` for a range `[i, e)`, characterised by the measure `v` and
three facts about the `Step A` dictionary. -/
theorem iteratorRange_next_spec {A : Type} (v : A → ℤ)
    (St : core.iter.range.Step A) (i e : A) {Q}
    (h_clone : St.cloneCloneInst.clone i = ok i)
    (h_cmp : St.corecmpPartialOrdInst.partial_cmp i e
      = ok (some (if v i < v e then core.cmp.Ordering.Less
        else if v i = v e then core.cmp.Ordering.Equal else core.cmp.Ordering.Greater)))
    (h_fwd : v i < v e →
      ∃ i', St.forward_checked i 1#usize = ok (some i') ∧ v i' = v i + 1)
    (h_lt : (h : v i < v e) →
      ∀ (t : A), v t = v i + 1 →
        (Q.1 (some i, { start := t, «end» := e })).down)
    (h_ge : v i ≥ v e →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core.IteratorRange.next St { start := i, «end» := e }
    ⦃ Q ⦄ := by
  unfold core.IteratorRange.next
  simp only [h_cmp]
  by_cases h : v i < v e
  · obtain ⟨i', hfw, hv'⟩ := h_fwd h
    simp only [h, ↓reduceIte, bind_tc_ok, h_clone, hfw]
    exact (by simpa [Triple, WP.wp, PredTrans.apply] using h_lt h i' hv')
  · simp only [h, ↓reduceIte, bind_tc_ok]
    split <;> exact (by simpa [Triple, WP.wp, PredTrans.apply] using h_ge (not_lt.mp h))

/-- Spec for `forLoopWithInvariant`, generic over the index type `A`. The three
`Step`-dictionary hypotheses (`h_clone`, `h_cmp`, `h_fwd`) are discharged once
per integer type; the loop-carried invariant `inv` advances by one index per
iteration. -/
theorem forLoopWithInvariant_spec {A β : Type} (v : A → ℤ)
    (St : core.iter.range.Step A)
    (body : A → β → Result β) (init : β) (s e : A) (inv : A → β → Result Prop)
    (h_le : v s ≤ v e)
    (h_inj : ∀ x y : A, v x = v y → x = y)
    (h_clone : ∀ i : A, St.cloneCloneInst.clone i = ok i)
    (h_cmp : ∀ x y : A, St.corecmpPartialOrdInst.partial_cmp x y
      = ok (some (if v x < v y then core.cmp.Ordering.Less
        else if v x = v y then core.cmp.Ordering.Equal else core.cmp.Ordering.Greater)))
    (h_fwd : ∀ i : A, v s ≤ v i → v i < v e →
      ∃ i', St.forward_checked i 1#usize = ok (some i') ∧ v i' = v i + 1)
    (h_init : (inv s init).holds)
    (h_step : ∀ acc (i : A), v s ≤ v i → v i < v e →
      (inv i acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      body i acc
      ⦃ ⇓ r => ⌜ ∀ (i' : A), v i' = v i + 1 → (inv i' r).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    forLoopWithInvariant St inv body { start := s, «end» := e } init
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  unfold forLoopWithInvariant
  apply loop_range_spec v _ init s e inv h_le h_init
  intro acc i hsi hie hinv
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next, h_cmp i e]
  by_cases h : v i < v e
  · -- i < e: `next` yields the current index, `body` runs, the loop continues
    obtain ⟨i', hfw, hv'⟩ := h_fwd i hsi h
    have hbody := h_step acc i hsi h hinv
    obtain ⟨r, hr⟩ := triple_noThrow_exists_ok hbody
    have hh := (triple_noThrow_elim hbody hr) i' hv'
    simp only [h, ↓reduceIte, h_clone, hfw, hr, bind_tc_ok]
    simp [hr, hv', bind_tc_ok, Triple, WP.wp, PredTrans.apply]
    simpa [Result.holds, Triple, WP.wp, PredTrans.apply] using hh
  · -- i ≥ e: with `i ≤ e` and `v` injective this is `i = e`; the loop is done
    have hie' : i = e := h_inj i e (le_antisymm hie (not_lt.mp h))
    subst hie'
    simp [bind_tc_ok, Triple, WP.wp, PredTrans.apply]
    simpa [Result.holds, Triple, WP.wp, PredTrans.apply] using hinv

/-! ### `@[spec]` instances per integer type

Each instance instantiates `forLoopWithInvariant_spec` with the scalar value
embedded in `ℤ` and discharges the four `Step`-dictionary facts. The invariant
hypotheses are phrased over `(·.val : ℤ)` so a single form covers signed and
unsigned uniformly. -/

/-- `for i in s..e` over `usize`. -/
@[spec]
theorem forLoopWithInvariant_spec_usize {β : Type}
    (body : Std.Usize → β → Result β) (init : β) (s e : Std.Usize)
    (inv : Std.Usize → β → Result Prop)
    (h_le : (s.val : ℤ) ≤ (e.val : ℤ))
    (h_init : (inv s init).holds)
    (h_step : ∀ acc (i : Std.Usize), (s.val : ℤ) ≤ (i.val : ℤ) → (i.val : ℤ) < (e.val : ℤ) →
      (inv i acc).holds →
      ⦃ ⌜ True ⌝ ⦄ body i acc
      ⦃ ⇓ r => ⌜ ∀ i', (i'.val : ℤ) = (i.val : ℤ) + 1 → (inv i' r).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    forLoopWithInvariant core.Usize.Insts.CoreIterRangeStep inv body
      { start := s, «end» := e } init
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  refine forLoopWithInvariant_spec (fun x => (x.val : ℤ)) core.Usize.Insts.CoreIterRangeStep
    body init s e inv h_le ?_ ?_ ?_ ?_ h_init h_step
  · -- injectivity
    intro x y hxy; simp only [] at hxy; apply UScalar.eq_of_val_eq; exact_mod_cast hxy
  · -- clone
    intro i; rfl
  · -- partial_cmp
    intro x y
    show core.mkUPartialOrd.partial_cmp x y = _
    have e1 : ((x.val : ℤ) < (y.val : ℤ)) = (x.val < y.val) := by simp
    have e2 : ((x.val : ℤ) = (y.val : ℤ)) = (x.val = y.val) := by simp
    simp only [core.mkUPartialOrd, compare, compareOfLessAndEq, e1, e2]
    split_ifs <;> rfl
  · -- forward_checked by 1: `checked_add`, no overflow since `i < e ≤ max`
    intro i _ hie
    simp only []
    have hbnd : i.val + (1#usize).val ≤ Usize.max := by have := e.hBounds; scalar_tac
    have hno := UScalar.overflowing_add_eq i 1#usize
    have hle1 : ¬ (i.val + (1#usize).val > UScalar.max .Usize) := by scalar_tac
    simp only [hle1, if_false] at hno
    obtain ⟨hsv, hovf⟩ := hno
    simp only [core.Usize.Insts.CoreIterRangeStep.forward_checked,
      core.convert.TryFromUTInfallible.Blanket.try_from, core.convert.From.Blanket.from,
      core.num.Usize.checked_add, core.num.Usize.overflowing_add,
      rust_primitives.arithmetic.overflowing_add_usize, bind_tc_ok]
    generalize hov : UScalar.overflowing_add i 1#usize = ov at *
    obtain ⟨res, overflowed⟩ := ov
    subst hovf
    exact ⟨_, rfl, by exact_mod_cast hsv⟩

end Spec

/-! ## Body-extraction helpers (shared between the conv and regular tactics) -/

/-- Substitute every occurrence of `x.2` in `e` by `aFvar`, recognizing both
`Expr.proj Prod 1 x` and `Prod.snd _ _ x` (application) forms. -/
private def substXSnd (e : Expr) (x aFvar : Expr) : Expr :=
  e.replace fun e' =>
    match e' with
    | .proj ``Prod 1 inner => if inner == x then some aFvar else none
    | _ =>
      if e'.isAppOfArity ``Prod.snd 3 && e'.appArg! == x then some aFvar
      else none

/-- Extract the user-level step body from a loop body in the precise shape
produced by Aeneas extraction (after `simp only [← Aeneas.Std.bind_assoc_eq]`)
for a `for i in s..e` Rust loop:
```
Bind.bind (next StepUsize x.1) <|
  Function.uncurry fun o iter1 =>
    <match>.match_1 _motive o
      (fun _ : Unit => Result.ok (ControlFlow.done x.2))
      fun i => Bind.bind userBody fun acc' =>
        Result.ok (ControlFlow.cont (iter1, acc'))
```
Returns `userBody` with the match-bound index substituted by `jFvar`. -/
private def extractStepBody (jFvar : Expr) (loopBodyInner : Expr) :
    MetaM (Option Expr) := do
  let inner ← whnfR loopBodyInner
  unless inner.isAppOfArity ``Bind.bind 6 do return none
  let cont ← whnfR (inner.getArg! 5)
  unless cont.isAppOfArity ``Aeneas.Std.uncurry 4 do return none
  let uncurryFn ← whnfR (cont.getArg! 3)
  unless uncurryFn.isLambda do return none
  lambdaTelescope uncurryFn fun ys matchExpr => do
    unless ys.size == 2 do return none
    let matchExpr ← whnfR matchExpr
    -- The match-aux application has shape `match_aux motive discr noneCase someCase`
    -- (4+ args). The `someCase` is the last argument and is a `fun i => ...` lambda.
    let matchArgs := matchExpr.getAppArgs
    unless matchArgs.size ≥ 4 do return none
    let someBranch ← whnfR matchArgs.back!
    unless someBranch.isLambda do return none
    lambdaTelescope someBranch fun is bodyInSome => do
      unless is.size == 1 do return none
      let i := is[0]!
      -- bodyInSome = Bind.bind _ _ _ _ userBody (fun acc' => ok (cont (iter1, acc')))
      let bodyInSome ← whnfR bodyInSome
      unless bodyInSome.isAppOfArity ``Bind.bind 6 do return none
      let userBody := bodyInSome.getArg! 4
      let result := userBody.replace fun e' =>
        if e' == i then some jFvar else none
      return some result

/-- Given a `loop B (Prod.mk _ _ iter init)` expression and an already-elaborated
invariant `inv`, build `Hax.forLoopWithInvariant inv body iter init` by extracting
`body`. Returns the new expression. Throws if the loop body doesn't have the
expected iterator/`ControlFlow.cont` shape. -/
private def buildForLoopWithInvariant
    (loopExpr inv : Expr) : MetaM Expr := do
  unless loopExpr.isAppOfArity ``Aeneas.Std.loop 4 do
    throwError "for_loop_with_invariant: expected a `loop _ _` expression"
  let initialPair := loopExpr.getArg! 3
  unless initialPair.isAppOfArity ``Prod.mk 4 do
    throwError "for_loop_with_invariant: loop's initial argument is not \
      a literal pair `(iter, init)`"
  let iter := initialPair.getArg! 2
  let init := initialPair.getArg! 3
  let elemTy ← inferType init
  -- The loop index type `ι` is the type parameter of `iter : Range ι`.
  let idxTy := (← whnfR (← inferType iter)).getArg! 0
  let loopBody := loopExpr.getArg! 2
  -- Extract the `Step ι` instance from the loop body's `next StepInst x.1`.
  let stepInst ← do
    let loopBody ← whnfR loopBody
    unless loopBody.isLambda do
      throwError "for_loop_with_invariant: loop body is not a lambda"
    lambdaTelescope loopBody fun _ inner => do
      let inner ← whnfR inner
      unless inner.isAppOfArity ``Bind.bind 6 do
        throwError "for_loop_with_invariant: loop body is not a `next >>= …` bind"
      let nextApp := inner.getArg! 4
      let args := nextApp.getAppArgs
      unless args.size ≥ 2 do
        throwError "for_loop_with_invariant: could not extract the `Step` instance"
      -- `next {A} StepInst range` → the `Step` instance is the arg before `range`.
      pure args[args.size - 2]!
  let stepLambda ← withLocalDeclD `j idxTy fun j =>
    withLocalDeclD `a elemTy fun a => do
      let loopBody ← whnfR loopBody
      unless loopBody.isLambda do
        throwError "for_loop_with_invariant: loop body is not a lambda"
      lambdaTelescope loopBody fun xs inner => do
        unless xs.size == 1 do
          throwError "for_loop_with_invariant: loop body has unexpected arity"
        let x := xs[0]!
        let inner := substXSnd inner x a
        let some body ← extractStepBody j inner
          | throwError "for_loop_with_invariant: could not extract the loop \
              step body (expected shape \
              `Bind.bind userBody (fun acc' => ok (cont (_, acc')))`)"
        mkLambdaFVars #[j, a] body
  mkAppM ``Hax.forLoopWithInvariant #[stepInst, inv, stepLambda, iter, init]

/-- Elaborate the user-supplied invariant against the expected type
`ι → β → Result Prop`, where `ι` is the loop index type and `β` is the element
type taken from `init`. -/
private def elabInvariant (idxTy init : Expr) (invStx : Term) : TacticM Expr := do
  let elemTy ← inferType init
  let resultProp ← mkAppM ``Aeneas.Std.Result #[mkSort .zero]
  let invType :=
    Expr.forallE `i idxTy (Expr.forallE `r elemTy resultProp .default) .default
  let inv ← Term.elabTermEnsuringType invStx invType
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars inv

/-! ## Conv tactic

`conv ... => for_loop_with_invariant inv` expects the conv focus to be a
`loop _ _` expression. It normalizes the focused term with
`simp only [← Aeneas.Std.bind_assoc_eq]`, extracts the user-level step body
automatically, and rewrites the focus to
`Hax.forLoopWithInvariant inv body iter init`. -/

syntax (name := for_loop_with_invariant_conv) "for_loop_with_invariant " term : conv

@[tactic for_loop_with_invariant_conv]
def elabForLoopWithInvariantConv : Tactic := fun stx => do
  let invStx : Term := ⟨stx[1]⟩
  -- The focus is the `loop _ _` expression itself; this simp is naturally
  -- scoped to it.
  evalTactic (← `(conv| (try simp only [← Aeneas.Std.bind_assoc_eq])))
  withMainContext do
    let lhs ← instantiateMVars (← Conv.getLhs)
    let initialPair := lhs.getArg! 3
    unless initialPair.isAppOfArity ``Prod.mk 4 do
      throwError "for_loop_with_invariant: loop's initial argument is not \
        a literal pair `(iter, init)`"
    let iter := initialPair.getArg! 2
    let init := initialPair.getArg! 3
    let idxTy := (← whnfR (← inferType iter)).getArg! 0
    let inv ← elabInvariant idxTy init invStx
    let newExpr ← buildForLoopWithInvariant lhs inv
    Conv.changeLhs newExpr

/-! ## Regular tactic

`for_loop_with_invariant inv` locates the first `loop _ _` subterm in the goal
and rewrites it to `Hax.forLoopWithInvariant inv body iter init`. It is a thin
wrapper around the conv tactic: `conv in (loop _ _) => for_loop_with_invariant inv`. -/

syntax (name := for_loop_with_invariant) "for_loop_with_invariant " term : tactic

@[tactic for_loop_with_invariant]
def elabForLoopWithInvariant : Tactic := fun stx => do
  let invStx : Term := ⟨stx[1]⟩
  evalTactic (← `(tactic|
    conv in (Aeneas.Std.loop _ _) => for_loop_with_invariant $invStx))

end Hax
