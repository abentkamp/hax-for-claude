/-
Minimal example demonstrating that `grind` fails to simplify
`Vector.getElem_set_ne` in a hypothesis when the context contains
`decide (j < r_12) = true` with USize64 variables and indirect equality chains.

**Root cause**: `grind` applies `Vector.getElem_set` (the general if-then-else lemma)
which produces `if i = j then x else v[j]`. This triggers case splits.
With the `decide (j < r_12) = true` hypothesis present, grind's internal
reasoning about USize64 ordering generates additional case splits that exhaust
grind's exploration budget. As a result, grind never finishes simplifying
the nested `Vector.set` terms in the hypothesis.

Crucially, in the failing state grind has *already derived* the necessary
inequalities (`r_1 ≠ j` and `r_6 ≠ j`) but the hypothesis `h_19` containing
`((v.set r_1 ...).set r_6 ...)[j]` remains unsimplified. This suggests
grind derives the inequalities via its congruence closure / arithmetic
reasoning but fails to *use* them to trigger the `Vector.getElem_set_ne` rewrite
on the hypothesis before the case-split budget is exhausted.

**Workaround**: Manually `rw [Vector.getElem_set_ne] at h_19` before calling `grind`.
-/

import Hax

-- This SUCCEEDS: without `decide (j < r_12) = true`, grind handles it fine
example (n : Nat) (v : Vector UInt64 n) (x y : UInt64)
    (i r_1 r_5 r_6 r_11 r_12 j : usize)
    (h_4 : r_1.toNat = USize64.toNat 2 * i.toNat)
    (h_9 : r_5.toNat = USize64.toNat 2 * i.toNat)
    (h_10 : r_6.toNat = r_5.toNat + USize64.toNat 1)
    (h_16 : r_11.toNat = i.toNat + USize64.toNat 1)
    (h_17 : r_12.toNat = USize64.toNat 2 * r_11.toNat)
    (h_8 : r_1.toNat < v.size)
    (h_15 : r_6.toNat < (v.set r_1.toNat x h_8).size)
    (hj : j.toNat < n)
    -- NOTE: no `decide (j < r_12) = true` here
    (hlt : j.toNat < 2 * i.toNat)
    (r_13 r_18 : UInt64)
    (h_19 : r_13 = ((v.set r_1.toNat x h_8).set r_6.toNat y h_15)[j.toNat]'(by omega))
    (h_25 : r_18 = v[j.toNat]) :
    r_13 = r_18 := by
  grind

-- This FAILS: adding `decide (j < r_12) = true` causes grind to fail
set_option maxHeartbeats 4000000 in
example (n : Nat) (v : Vector UInt64 n) (x y : UInt64)
    (i r_1 r_5 r_6 r_11 r_12 j : usize)
    (h_4 : r_1.toNat = USize64.toNat 2 * i.toNat)
    (h_9 : r_5.toNat = USize64.toNat 2 * i.toNat)
    (h_10 : r_6.toNat = r_5.toNat + USize64.toNat 1)
    (h_16 : r_11.toNat = i.toNat + USize64.toNat 1)
    (h_17 : r_12.toNat = USize64.toNat 2 * r_11.toNat)
    (h_8 : r_1.toNat < v.size)
    (h_15 : r_6.toNat < (v.set r_1.toNat x h_8).size)
    (hj : j.toNat < n)
    (h_18 : decide (j < r_12) = true)  -- THIS is the critical hypothesis
    (hlt : j.toNat < 2 * i.toNat)
    (r_13 r_18 : UInt64)
    (h_19 : r_13 = ((v.set r_1.toNat x h_8).set r_6.toNat y h_15)[j.toNat]'(by omega))
    (h_25 : r_18 = v[j.toNat]) :
    r_13 = r_18 := by
  grind  -- FAILS even with 4M heartbeats

-- This SUCCEEDS: manual rewrite first, then grind
example (n : Nat) (v : Vector UInt64 n) (x y : UInt64)
    (i r_1 r_5 r_6 r_11 r_12 j : usize)
    (h_4 : r_1.toNat = USize64.toNat 2 * i.toNat)
    (h_9 : r_5.toNat = USize64.toNat 2 * i.toNat)
    (h_10 : r_6.toNat = r_5.toNat + USize64.toNat 1)
    (h_16 : r_11.toNat = i.toNat + USize64.toNat 1)
    (h_17 : r_12.toNat = USize64.toNat 2 * r_11.toNat)
    (h_8 : r_1.toNat < v.size)
    (h_15 : r_6.toNat < (v.set r_1.toNat x h_8).size)
    (hj : j.toNat < n)
    (h_18 : decide (j < r_12) = true)
    (hlt : j.toNat < 2 * i.toNat)
    (r_13 r_18 : UInt64)
    (h_19 : r_13 = ((v.set r_1.toNat x h_8).set r_6.toNat y h_15)[j.toNat]'(by omega))
    (h_25 : r_18 = v[j.toNat]) :
    r_13 = r_18 := by
  rw [Vector.getElem_set_ne] at h_19
  rw [Vector.getElem_set_ne] at h_19
  · grind         -- main goal: now h_19 is simplified
  · grind         -- side goal: r_1.toNat ≠ j.toNat
  · grind         -- side goal: r_6.toNat ≠ j.toNat

-- With plain Nat (no USize64), grind handles it even with the extra hypothesis
example (n : Nat) (v : Vector UInt64 n) (x y : UInt64)
    (i r_1 r_5 r_6 r_11 r_12 j : Nat)
    (h_4 : r_1 = 2 * i)
    (h_9 : r_5 = 2 * i)
    (h_10 : r_6 = r_5 + 1)
    (h_16 : r_11 = i + 1)
    (h_17 : r_12 = 2 * r_11)
    (h_8 : r_1 < v.size)
    (h_15 : r_6 < (v.set r_1 x h_8).size)
    (hj : j < n)
    (h_18 : j < r_12)
    (hlt : j < 2 * i)
    (r_13 r_18 : UInt64)
    (h_19 : r_13 = ((v.set r_1 x h_8).set r_6 y h_15)[j]'(by omega))
    (h_25 : r_18 = v[j]) :
    r_13 = r_18 := by
  grind
