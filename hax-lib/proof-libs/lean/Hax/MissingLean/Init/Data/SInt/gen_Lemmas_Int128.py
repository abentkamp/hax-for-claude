#!/usr/bin/env python3
"""
Generate an approximation of Lemmas_Int128.lean from Lean4's
Init/Data/SInt/Lemmas.lean.

Strategy:
  1. Skip the preamble of the source file (copyright, imports, macro definition,
     and the declare_int_theorems invocations for the built-in types).
  2. Split the remaining content into blocks (groups of consecutive non-blank lines).
  3. Keep every block that mentions "Int64" or "UInt64" – these are the
     explicitly written Int64-specific theorems.
  4. Apply text substitutions to rename everything to 128-bit variants.
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

declare_int_theorems Int128 128"""

# ---------------------------------------------------------------------------
# Substitution rules
# Applied in order; UInt64 must come before Int64 to avoid a double-hit.
# ---------------------------------------------------------------------------

LITERAL_SUBS = [
    ("UInt64", "UInt128"),
    ("Int64",  "Int128"),
    # Bit-width literals that appear explicitly in Int64 theorems:
    ("signExtend 64",  "signExtend 128"),
    ("BitVec.ofInt 64", "BitVec.ofInt 128"),
    ("#64", "#128"),
    ("ofNat 64", "ofNat 128"),  # rare but possible
]

# Signed-range bounds: 2^63  →  2^127
REGEX_SUBS = [
    (re.compile(r"2 \^ 63\b"), "2 ^ 127"),
    (re.compile(r"2\^63\b"),   "2^127"),
]


def apply_substitutions(text: str) -> str:
    for old, new in LITERAL_SUBS:
        text = text.replace(old, new)
    for pattern, new in REGEX_SUBS:
        text = pattern.sub(new, text)
    return text


def should_keep(block: str) -> bool:
    """Keep a block if it is specific to Int64 or UInt64."""
    return "Int64" in block or "UInt64" in block


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


def split_into_blocks(lines: list[str]) -> list[str | None]:
    """
    Split lines into a list where:
      - str entries are non-empty blocks (consecutive non-blank lines joined)
      - None entries represent blank-line separators
    """
    blocks: list[str | None] = []
    current: list[str] = []
    for line in lines:
        if line.strip() == "":
            if current:
                blocks.append("\n".join(current))
                current = []
            blocks.append(None)
        else:
            current.append(line)
    if current:
        blocks.append("\n".join(current))
    return blocks


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

    # Collect kept blocks
    kept: list[str] = []
    for block in split_into_blocks(body_lines):
        if block is not None and should_keep(block):
            kept.append(apply_substitutions(block))

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
