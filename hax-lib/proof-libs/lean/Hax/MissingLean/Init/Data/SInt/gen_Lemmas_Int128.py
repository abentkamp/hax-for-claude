#!/usr/bin/env python3
"""
Generate Int128 Lean files from Lean4's Init/Data/SInt source files.

Supports six modes:
  --mode lemmas   (default) Generate Lemmas_Int128.lean from Init/Data/SInt/Lemmas.lean
  --mode basic              Generate Basic_Int128.lean  from Init/Data/SInt/Basic.lean
  --mode toexpr             Generate Lean/ToExpr.lean   from Lean/ToExpr.lean
  --mode sint               Generate BuiltinSimpProcs/SInt.lean from Lean/Meta/Tactic/Simp/BuiltinSimprocs/SInt.lean
  --mode toint              Generate Init/GrindInstances/ToInt.lean from Init/GrindInstances/ToInt.lean
  --mode ringsint           Generate Init/GrindInstances/Ring/SInt.lean from Init/GrindInstances/Ring/SInt.lean
  --mode prelude            Generate Init/Prelude.lean from Init/Prelude.lean

Strategy:
  1. Split the source file into items, each starting at an unindented line.
  2. Keep every item that:
       a. mentions "Int64" or "UInt64" (is Int64-specific), and
       b. is a Lean declaration (not a doc comment or bare text), and
       c. does not involve an ISize↔Int64 conversion, and
       d. does not reference typeclasses unavailable for Int128.
  3. Apply text substitutions to rename everything to 128-bit variants.
  4. Prepend the hard-coded header for the chosen mode.

Usage:
    python3 gen_Lemmas_Int128.py [--mode {lemmas,basic,toexpr,sint,toint,ringsint,prelude}] <input.lean> [output.lean]

If no output path is given the result is printed to stdout.
"""

# ---------------------------------------------------------------------------
# Known shortcomings and residual issues requiring manual post-processing
# ---------------------------------------------------------------------------
#
# --mode basic (Init/Data/SInt/Basic.lean → Basic_Int128.lean)
# ─────────────────────────────────────────────────────────────
# 1. Wrong maxValue / minValue literals.
#    Source contains Int64's evaluated bounds (9223372036854775807 and
#    -9223372036854775808); these numeric literals are not matched by any
#    substitution rule.
#    Fix: replace with the correct Int128 bounds
#         (170141183460469231731687303715884105727 and
#          -170141183460469231731687303715884105728).
#
# 2. Hashable Int128: wrong hash return type.
#    Source: hash i := i.toUInt64   →   generated: hash i := i.toUInt128
#    Hashable.hash must return UInt64, not UInt128.
#    Fix: hash i := UInt64.ofInt i.toInt
#
# 3. Spurious Hashable Int8/Int16/Int32/ISize instances.
#    These instances in the source implement Hashable by calling .toUInt64,
#    so they contain "UInt64" and pass should_keep.  After renaming they
#    reference .toUInt128 (wrong return type) and are not about Int128 at all.
#    Fix: delete all four instances.
#
# 4. Missing Int128.toInt64 and Int64.toInt128 conversions.
#    No integer type larger than Int64 appears in Basic.lean, so there is
#    nothing to rename into these functions.
#    Fix: add both definitions manually.
#
# 5. Structure field doc comment not updated.
#    The toUInt128 field inside "structure Int128 where" has an indented
#    doc comment that still refers to "64-bit".  The comment text is
#    harmless but misleading.
#
# --mode lemmas (Init/Data/SInt/Lemmas.lean → Lemmas_Int128.lean)
# ────────────────────────────────────────────────────────────────
# 1. ISize.toInt_le_int128MaxValue: proof broken after rename.
#    The original proof uses le_of_lt_add_one x.toInt_lt, which establishes
#    x.toInt ≤ 2^(Platform.numBits/2) - 1.  After rename the goal becomes
#    x.toInt ≤ 2^127 - 1, which that lemma cannot prove (ISize ≠ Int128).
#    Fix: manual proof using Int.le_trans and Platform.numBits_eq.
#
# 2. UInt128.toInt128_ofNatLT: references BitVec.ofNatLT_eq_ofNat which does
#    not exist at Lean v4.29.0-rc1.
#    Fix: find or prove an equivalent simp lemma for this version.
#
# --mode toexpr  (Lean/ToExpr.lean → Lean/ToExpr.lean)
# ──────────────────────────────────────────────────────
# The generated file uses "open Lean" globally (in the header) instead of
# the per-instance "open Lean in" style used in the existing file.
# This is functionally equivalent.
#
# --mode sint  (Lean/Meta/Tactic/Simp/BuiltinSimprocs/SInt.lean → BuiltinSimpProcs/SInt.lean)
# ─────────────────────────────────────────────────────────────────────────────────────────────
# No known shortcomings.  The macro approach produces a clean, maintainable
# file; updating to a new Lean version is a matter of re-running the script.
#
# --mode toint  (Init/GrindInstances/ToInt.lean → Init/GrindInstances/ToInt.lean)
# ────────────────────────────────────────────────────────────────────────────────
# 1. Comments about ToInt.Pow are dropped from the output.  Two comment blocks:
#      -- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.UInt`, ...
#      -- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.SInt`, ...
#    Neither references Int64 or UInt64, so they are filtered by should_keep.
#    Fix: manually re-add both comment lines.
#
# --mode ringsint  (Init/GrindInstances/Ring/SInt.lean → Init/GrindInstances/Ring/SInt.lean)
# ──────────────────────────────────────────────────────────────────────────────────────────
# 1. Verification comment dropped.
#    The inline comment "-- Verify we can derive the instances showing how
#    `toInt` interacts with operations:" does not contain "Int64" or "UInt64",
#    so it is filtered by should_keep.
#    Fix: manually re-add the comment line before the three `example` lines.
#
# --mode prelude  (Init/Prelude.lean → Init/Prelude.lean)
# ─────────────────────────────────────────────────────────
# 1. Structure field doc comments are preserved from upstream. The existing
#    hax file omits them. The generated file is more informative; update the
#    hax file to keep the docs, or delete them manually if preferred.

import argparse
import re

# ---------------------------------------------------------------------------
# Fixed headers for the generated files
# ---------------------------------------------------------------------------

LEMMAS_HEADER = """\
import Hax.MissingLean.Init.Data.SInt.Basic_Int128
import Hax.MissingLean.Init.Data.UInt.Lemmas_UInt128
import Hax.MissingLean.Lean.Tactic.Simp.BuiltinSimpProcs.SInt
import Hax.MissingLean.Lean.Tactic.Simp.BuiltinSimpProcs.UInt

-- Adapted from Init/Data/SInt/Lemmas.lean from the Lean v4.29.0-rc1 source code

-- Proofs that use (rfl) on 128-bit arithmetic require more kernel unfolding
-- steps than the default limit allows (Int128 routes through UInt128, adding
-- an extra indirection layer compared to the 64-bit built-in types).
set_option maxRecDepth 4000

declare_int_theorems Int128 128"""

BASIC_HEADER = """\
import Hax.MissingLean.Init.Prelude
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.SInt

set_option autoImplicit true

-- Adapted from Init/Data/SInt/Basic.lean from the Lean v4.29.0-rc1 source code"""

TOEXPR_HEADER = """\
import Lean
import Hax.MissingLean.Init.Data.UInt.Basic
import Hax.MissingLean.Init.Data.SInt.Basic_Int128

-- Adapted from Lean/ToExpr.lean from the Lean v4.29.0-rc1 source code

open Lean"""

SINT_HEADER = """\
import Lean
import Hax.MissingLean.Lean.ToExpr

-- Adapted from Lean/Meta/Tactic/Simp/BuiltinSimprocs/SInt.lean from the Lean v4.29.0-rc1 source code

open Lean Meta Simp"""

TOINT_HEADER = """\
import Hax.MissingLean.Init.Data.SInt.Lemmas_Int128
import Hax.MissingLean.Init.Data.UInt.Lemmas_UInt128

-- Adapted from Init/GrindInstances/ToInt.lean from the Lean v4.29.0-rc1 source code

open Lean.Grind"""

RINGSINT_HEADER = """\
import Hax.MissingLean.Init.GrindInstances.ToInt

-- Adapted from Init/GrindInstances/Ring/SInt.lean from the Lean v4.29.0-rc1 source code

open Lean Grind"""

# Leading \n produces the blank first line present in the existing hax file.
PRELUDE_HEADER = "\n-- Adapted from Init/Prelude.lean from the Lean v4.29.0-rc1 source code"

# ---------------------------------------------------------------------------
# Sint mode: substitutions applied to the extracted macro body.
# The upstream macro uses builtin_dsimproc/builtin_simproc (for types built
# into the Lean kernel); Int128 is not built-in, so we use dsimproc/simproc.
# We also rename the macro to avoid clashing with the upstream definition.
# ---------------------------------------------------------------------------

SINT_SUBS = [
    ("builtin_dsimproc",        "dsimproc"),
    ("builtin_simproc",         "simproc"),
    ('"declare_sint_simprocs"', '"declare_sint_simprocs_ext"'),
]


def extract_sint_macro(lines: list[str]) -> list[str]:
    """
    Extract the declare_sint_simprocs macro definition from the upstream file,
    stopping just before the first invocation (declare_sint_simprocs Int8/16/…).
    """
    in_macro = False
    result = []
    for line in lines:
        if not in_macro:
            if line.startswith('macro "declare_sint_simprocs"'):
                in_macro = True
                result.append(line)
        else:
            if line.startswith("declare_sint_simprocs "):
                break  # first invocation — stop here
            result.append(line)
    return result

# ---------------------------------------------------------------------------
# Substitution rules
# Applied in order; UInt64 before Int64 to avoid a double-hit, and both
# PascalCase and snake_case forms must be renamed.
# ---------------------------------------------------------------------------

LITERAL_SUBS = [
    ("UInt64", "UInt128"),
    ("Int64",  "Int128"),
    # Lowercase snake_case occurrences in theorem names:
    #   e.g. ofBitVec_int64ToBitVec, int64MinValue_le_toInt, ofInt_int64ToInt
    # Must come after the PascalCase replacements (no overlap, but clearer).
    ("int64",  "int128"),
    # BitVec 64 is the underlying representation of Int64; Int128 wraps BitVec 128.
    # Must come before the standalone "64" patterns below.
    ("BitVec 64", "BitVec 128"),
    # Bit-width literals that appear explicitly in Int64 theorems:
    ("signExtend 64",  "signExtend 128"),
    ("smod 64",        "smod 128"),       # shiftLeft/shiftRight clamp the shift amount
    ("BitVec.ofInt 64", "BitVec.ofInt 128"),
    ("#64", "#128"),
    ("ofNat 64", "ofNat 128"),  # rare but possible
    # IntInterval shape arguments in ToInt instances:
    (".uint 64",  ".uint 128"),
    (".sint 64",  ".sint 128"),
    # UInt64.size / Int64.size appear as the evaluated literal 2^64 in the source.
    # We use the bare 2^128 literal so the substitution is valid even in contexts
    # where Int128.size is not yet defined (e.g. Init/Prelude.lean).
    ("18446744073709551616", "340282366920938463463374607431768211456"),
]

# Signed-range bounds: 2^63  →  2^127
# Arithmetic modulus:  2^64  →  2^128  (bmod for add/sub/neg/etc.)
REGEX_SUBS = [
    (re.compile(r"2 \^ 63\b"), "2 ^ 127"),
    (re.compile(r"2\^63\b"),   "2^127"),
    (re.compile(r"2 \^ 64\b"), "2 ^ 128"),
    (re.compile(r"2\^64\b"),   "2^128"),
]


def apply_substitutions(text: str) -> str:
    for old, new in LITERAL_SUBS:
        text = text.replace(old, new)
    for pattern, new in REGEX_SUBS:
        text = pattern.sub(new, text)
    return text


# ---------------------------------------------------------------------------
# Filtering
# ---------------------------------------------------------------------------

def should_keep(item: str) -> bool:
    """Keep an item if it is specific to Int64 or UInt64."""
    return "Int64" in item or "UInt64" in item


# Keywords that begin a Lean declaration.  Items whose first line does not
# start with one of these are bare text (doc comment content, copyright
# lines, macro invocations such as "declare_int_theorems Int64 64", etc.)
# and should be dropped.
LEAN_DECL_PREFIXES = (
    "def ", "abbrev ", "protected ", "private ", "@[",
    "theorem ", "lemma ", "instance ", "attribute ",
    "structure ", "class ", "set_option ", "example ",
)


def is_lean_declaration(item: str) -> bool:
    """Return True if the item starts with a Lean declaration keyword."""
    first_line = item.split("\n")[0]
    return any(first_line.startswith(p) for p in LEAN_DECL_PREFIXES)


# Patterns in the ORIGINAL (pre-substitution) source text that indicate an
# item involves an ISize↔Int64 *conversion* (not just a bound comparison).
# Int128.toISize and ISize.toInt128 don't exist, so these items can't be
# ported and must be dropped.
#
# Three disjoint cases cover all such items in practice:
#   1. "toISize"   – any call that produces an ISize from something else
#                    (Int64.toBitVec_toISize, ISize.ofBitVec_int64ToBitVec…)
#   2. "iSizeTo"   – any name whose ISize is the *source* being converted
#                    (Int64.ofBitVec_iSizeToBitVec, ofIntLE_iSizeToInt…)
#   3. ISize namespace + ".toInt64" call – conversions from ISize to Int64
#                    (ISize.toBitVec_toInt64, ISize.toInt_toInt64…)
#
# Items such as ISize.int64MinValue_le_toInt / ISize.toInt_le_int64MaxValue
# contain "ISize" but neither "toISize", "iSizeTo", nor ".toInt64", so they
# are kept and renamed correctly.
def is_isize_conversion(item: str) -> bool:
    if "toISize" in item:
        return True
    if "iSizeTo" in item:
        return True
    if "ISize" in item and ".toInt64" in item:
        return True
    return False


def uses_unavailable_typeclass(item: str) -> bool:
    """
    Drop items that reference type class identifiers that don't exist for
    Int128 (either absent from this Lean version or not provided for Int128).
    The 'maximum recursion depth' elaboration errors these cause cascade into
    unrelated theorems that follow.
    """
    return "IsLinearOrder" in item or "LawfulOrderLT" in item


def is_extern_attribute_decl(item: str) -> bool:
    """
    Return True for standalone `attribute [extern "..."] Foo.bar` declarations.
    These are extern C linkage annotations for built-in kernel types; they have
    no counterpart for UInt128/Int128 and must be dropped in prelude mode.
    Distinguishes them from `attribute [local instance] X in CMD` (which ends
    with " in") by checking that " in" is absent.
    """
    first = item.split("\n")[0]
    return first.startswith('attribute [extern "') and " in" not in first


def strip_extern_decorator(item: str) -> str:
    """
    If the first line of an item is `@[extern "..."]`, remove it.
    In prelude mode the upstream uses extern FFI decorators on `ofNatLT` and
    `decEq`; the hax versions are pure Lean definitions without extern linkage.
    """
    lines = item.split("\n")
    if lines and lines[0].startswith('@[extern "'):
        return "\n".join(lines[1:])
    return item


def is_uint64_primary_definition(item: str) -> bool:
    """
    For prelude mode: return True only for items that define UInt64 itself or
    provide a typeclass instance specifically for UInt64.  Rejects items that
    merely use UInt64 as a return/argument type (e.g. class Hashable, mixHash,
    String.hash).  Must be called after strip_extern_decorator so the first
    line is the actual declaration, not the @[extern "..."] decorator.
    """
    first = item.split("\n")[0]
    return (first.startswith("abbrev UInt64") or
            first.startswith("structure UInt64") or
            first.startswith("def UInt64.") or
            (first.startswith("instance : ") and "UInt64" in first))


def split_into_items(lines: list[str]) -> list[str]:
    """
    Split lines into top-level items.  Each item starts at an unindented
    (column-0) non-blank line and continues until the next such line or a
    blank line that precedes one.  This correctly handles:
      - multi-line proofs (indented continuation lines stay with their item)
      - adjacent theorems with no blank line between them
    """
    items: list[str] = []
    current: list[str] = []
    for line in lines:
        if line.strip() == "":
            # Blank line ends the current item (if any).
            if current:
                items.append("\n".join(current))
                current = []
        elif line[0] != " " and line[0] != "\t":
            # Unindented non-blank line: starts a new item, UNLESS it is:
            #   (a) a bare "where" — a continuation clause in Lean syntax, or
            #   (b) the command following a pending "attribute X in" — which
            #       in Lean4 must appear on the very next line.
            if line.rstrip() == "where" and current:
                current.append(line)
            elif (current and len(current) == 1
                  and current[0].startswith("attribute ")
                  and current[0].rstrip().endswith(" in")):
                # Pending "attribute X in" — attach next declaration to same item.
                current.append(line)
            elif (current and len(current) == 1
                  and current[0].startswith("@[")
                  and current[0].rstrip().endswith("]")):
                # Single @[...] attribute decorator — attach next declaration to same item.
                current.append(line)
            else:
                if current:
                    items.append("\n".join(current))
                current = [line]
        else:
            # Indented line: continuation of the current item.
            if current:
                current.append(line)
            # Indented lines before any item (shouldn't happen) are dropped.
    if current:
        items.append("\n".join(current))
    return items


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate Int128 Lean files from Lean4 Init/Data/SInt sources."
    )
    parser.add_argument("input", help="Path to the Lean4 source file")
    parser.add_argument("output", nargs="?", help="Output path (default: stdout)")
    parser.add_argument(
        "--mode",
        choices=["lemmas", "basic", "toexpr", "sint", "toint", "ringsint", "prelude"],
        default="lemmas",
        help=(
            "lemmas: generate Lemmas_Int128.lean (default); "
            "basic: generate Basic_Int128.lean; "
            "toexpr: generate Lean/ToExpr.lean; "
            "sint: generate BuiltinSimpProcs/SInt.lean; "
            "toint: generate Init/GrindInstances/ToInt.lean; "
            "ringsint: generate Init/GrindInstances/Ring/SInt.lean; "
            "prelude: generate Init/Prelude.lean"
        ),
    )
    args = parser.parse_args()

    with open(args.input, encoding="utf-8") as f:
        raw_lines = [line.rstrip("\n") for line in f]

    if args.mode == "sint":
        macro_lines = extract_sint_macro(raw_lines)
        macro_text = "\n".join(macro_lines)
        for old, new in SINT_SUBS:
            macro_text = macro_text.replace(old, new)
        output = SINT_HEADER + "\n\n" + macro_text.rstrip() + "\n\ndeclare_sint_simprocs_ext Int128\n"
    elif args.mode == "prelude":
        # Prelude mode: drop extern-only attribute declarations and strip
        # @[extern "..."] decorator lines from definitions.  Then keep only
        # items that define UInt64 itself (not items that merely use UInt64 as
        # a return/argument type such as class Hashable or opaque mixHash).
        # The standard isize-conversion and unavailable-typeclass filters are
        # not needed (no ISize or IsLinearOrder in Init/Prelude.lean).
        kept: list[str] = []
        for item in split_into_items(raw_lines):
            if (should_keep(item)
                    and is_lean_declaration(item)
                    and not is_extern_attribute_decl(item)):
                item = strip_extern_decorator(item)
                if is_uint64_primary_definition(item):
                    kept.append(apply_substitutions(item))
        output = PRELUDE_HEADER + "\n\n" + "\n\n".join(kept) + "\n"
    else:
        header = {
            "lemmas":   LEMMAS_HEADER,
            "basic":    BASIC_HEADER,
            "toexpr":   TOEXPR_HEADER,
            "toint":    TOINT_HEADER,
            "ringsint": RINGSINT_HEADER,
        }[args.mode]

        # Collect kept items
        kept: list[str] = []
        for item in split_into_items(raw_lines):
            if (should_keep(item)
                    and is_lean_declaration(item)
                    and not is_isize_conversion(item)
                    and not uses_unavailable_typeclass(item)):
                kept.append(apply_substitutions(item))

        # Assemble output: header, then one blank line between each kept block
        output = header + "\n\n" + "\n\n".join(kept) + "\n"

    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(output)
        import sys
        print(f"Written to {args.output}", file=sys.stderr)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
