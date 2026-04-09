#!/usr/bin/env python3
"""
Generate an approximation of Lemmas_Int128.lean from Lean4's
Init/Data/SInt/Lemmas.lean.

Strategy:
  1. Skip the preamble of the source file (copyright, imports, macro definition,
     and the declare_int_theorems invocations for the built-in types).
  2. Split the remaining content into items, each starting at an unindented line.
  3. Keep every item that mentions "Int64" or "UInt64" – these are the
     explicitly written Int64-specific theorems.
  4. Drop items that involve ISize↔Int64 *conversions* (not just bound
     comparisons), because Int128.toISize and ISize.toInt128 don't exist.
  5. Apply text substitutions to rename everything to 128-bit variants.
  5. Prepend the hard-coded header (imports + declare_int_theorems Int128 128).

Usage:
    python3 gen_Lemmas_Int128.py <path/to/Init/Data/SInt/Lemmas.lean> [output]

If no output path is given the result is printed to stdout.
"""

import re
import sys

# ---------------------------------------------------------------------------
# Fixed header for the generated file
# ---------------------------------------------------------------------------

HEADER = """\
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
    ("BitVec.ofInt 64", "BitVec.ofInt 128"),
    ("#64", "#128"),
    ("ofNat 64", "ofNat 128"),  # rare but possible
    # Int64.size appears as the evaluated literal 2^64 in the source:
    ("18446744073709551616", "Int128.size"),
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


def find_body_start(lines: list[str]) -> int:
    """
    Return the index of the first line after the last declare_int_theorems
    invocation in the file.  Everything before that index belongs to the
    preamble (copyright, imports, macro definition, and the invocations for
    the built-in Int8/Int16/Int32/Int64/ISize types).
    """
    last_idx = 0
    for i, line in enumerate(lines):
        if line.strip().startswith("declare_int_theorems"):
            last_idx = i
    return last_idx + 1


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
            # Unindented non-blank line: starts a new item.
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
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <Lemmas.lean> [output]", file=sys.stderr)
        sys.exit(1)

    input_path = sys.argv[1]
    output_path = sys.argv[2] if len(sys.argv) > 2 else None

    with open(input_path, encoding="utf-8") as f:
        raw_lines = [line.rstrip("\n") for line in f]

    # Skip preamble; only process the theorem definitions
    body_start = find_body_start(raw_lines)
    body_lines = raw_lines[body_start:]

    # Collect kept items
    kept: list[str] = []
    for item in split_into_items(body_lines):
        if should_keep(item) and not is_isize_conversion(item) and not uses_unavailable_typeclass(item):
            kept.append(apply_substitutions(item))

    # Assemble output: header, then one blank line between each kept block
    output = HEADER + "\n\n" + "\n\n".join(kept) + "\n"

    if output_path:
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(output)
        print(f"Written to {output_path}", file=sys.stderr)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
