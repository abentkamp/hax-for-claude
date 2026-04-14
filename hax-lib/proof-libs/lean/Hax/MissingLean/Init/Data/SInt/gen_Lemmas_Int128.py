#!/usr/bin/env python3
"""
Generate Int128/UInt128 Lean declarations from Lean4 upstream source files.

Automatically locates the Lean4 source tree via the nearest lean-toolchain file
(searched upward from this script), reads each upstream source file, applies all
transformation pipelines, and writes the combined output to a single Lean file.

The output contains no import statements; each section is prefixed with a comment
header identifying the upstream source and the target hax file.

Usage:
    python3 gen_Lemmas_Int128.py [output.lean]

If no output path is given the result is printed to stdout.
"""


# ---------------------------------------------------------------------------
# Manual edits required in the combined Generated.lean file (Lean v4.29.0-rc1)
# ---------------------------------------------------------------------------
# Run this script then apply the following edits to make the combined file compile.
#
# [uintbasic] instance UInt128.instOfNat / Int128.instOfNat — explicit (n : Nat)
#   The bare-n form `instance UInt128.instOfNat : OfNat UInt128 n` fails because
#   `n` is not auto-bound as `Nat` in this context.  Add `(n : Nat)` explicitly.
#
# [uintbasic] HMod UInt128 Nat UInt128 — suppress deprecation warning
#   Wrap the instance with `set_option linter.deprecated false in` (the upstream
#   uses this wrapper, but it is dropped by should_keep since it contains no
#   "UInt64").
#
# [uintbasic] Hashable Int8/Int16/Int32/ISize — remove wrong instances
#   The generator keeps the Hashable instances for Int8/16/32/ISize from
#   Basic.lean (they reference .toUInt64, hence pass should_keep).  After
#   renaming they reference .toUInt128 (wrong return type for hash, which must
#   be UInt64).  Remove these four instances (they are already defined upstream
#   via .toUInt64).
#
# [uintbasic] Hashable Int128 — fix hash return type
#   The generated `hash i := i.toUInt128` returns UInt128, not UInt64.
#   Replace with `hash i := hash i.toInt`.
#
# [uintbasic] Hashable ISize — remove wrong instance
#   The generated instance uses `i.toUSize.toUInt128` (USize.toUInt128 absent at
#   generation time).  Remove it; ISize's Hashable is already defined upstream.
#
# [basicaux] USize.toUInt128 — add manually after UInt32.toUInt128
#   The generator drops `def USize.toUInt64` because its body `⟨a.val⟩` is wrong
#   for UInt128 (UInt128 uses BitVec internally, not Fin).  Add manually:
#     def USize.toUInt128 (a : USize) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩
#   This mirrors the existing UInt8/16/32.toUInt128 definitions.
#
# [uintlemmas] Add UInt128.toUSize before declare_uint_theorems
#   The uintbasic section intentionally skips UInt64.toUSize → UInt128.toUSize
#   (drop logic: lines 633–635 of the script).  But declare_uint_theorems (macro
#   in the uintlemmas section) calls UInt128.toUSize.  Add manually:
#     def UInt128.toUSize (a : UInt128) : USize := a.toNat.toUSize
#
# [uintlemmas] UIntN.toNat_toUInt128 simp lemmas — add after UInt128.toUSize
#   `declare_uint_theorems` only generates `toNat_toUInt64` for types with nbits ≤ 32;
#   there is no `toNat_toUInt128` branch.  Add four simp lemmas manually:
#     @[simp] theorem UInt8.toNat_toUInt128 (n : UInt8) : n.toUInt128.toNat = n.toNat :=
#       Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
#     @[simp] theorem UInt16.toNat_toUInt128 (n : UInt16) : n.toUInt128.toNat = n.toNat :=
#       Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
#     @[simp] theorem UInt32.toNat_toUInt128 (n : UInt32) : n.toUInt128.toNat = n.toNat :=
#       Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
#     @[simp] theorem USize.toNat_toUInt128 (n : USize) : n.toUInt128.toNat = n.toNat :=
#       Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le n.toNat_lt USize.size_le_uint128Size)
#   Proof: n.toUInt128.toNat = n.toNat % 2^128 by def; Nat.mod_eq_of_lt closes it
#   since n.toNat < UIntN.size ≤ 2^128.  For USize, `by decide` fails because
#   USize.size is platform-dependent (2^32 or 2^64); use the already-proved
#   USize.size_le_uint128Size lemma instead.
#   These two manual additions (USize.toUInt128 + toNat_toUInt128 simp lemmas) unlock
#   ~100 theorems that were otherwise unprovable.
#
# [uintlemmas] USize.toNat_mod_uInt128Size — wrong bound in proof
#   Generated proof uses `Nat.mod_eq_of_lt n.toNat_lt` (USize bound ≤ 2^64).
#   UInt128.size is 2^128, so the correct proof is:
#     Nat.mod_eq_of_lt (Nat.lt_trans n.toNat_lt (by decide))
#
# [uintlemmas] UInt128.toUSize_ofNatTruncate_of_le — proof needs native_decide
#   The generated `USize.toNat.inj (by simp [...])` leaves goal
#   `(2^128 - 1) % 2^System.Platform.numBits = USize.size - 1`
#   which simp cannot close (System.Platform.numBits is opaque).
#   Fix: append `; native_decide` after the simp.
#
# [uintlemmas] UInt128.neg_one_eq and UInt128.sub_eq_add_mul — wrong literal
#   LITERAL_SUBS replaces "64" → "128" but misses the concrete value
#   18446744073709551615 (= 2^64 - 1).  The Int128 equivalent is
#   340282366920938463463374607431768211455 (= 2^128 - 1).
#   Replace both occurrences of 18446744073709551615 with that value.
#
# [uintlemmas] UInt32.neg_inj / neg_ne_zero / not_lt_zero / zero_le — duplicate decls
#   The generator pairs each new UInt128 theorem with its UInt32 source verbatim.
#   For `neg_inj`, `neg_ne_zero`, `not_lt_zero`, `zero_le` these UInt32 theorems
#   already exist in Lean core → "already declared" error.  Remove the four UInt32
#   declarations, keeping only the UInt128 versions.
#
# [uintlemmas] Many UIntN.toUInt128 widening theorems — proof fixes required
#   The generator produces theorems like UInt8.toUInt8_toUInt128, toFin_toUInt128,
#   toBitVec_toUInt128, and arithmetic conversions (add, mul, lt, le, eq, neg, sub)
#   that need manual proof adjustments:
#   (a) `rfl` fails for cross-struct UInt-to-UInt128 conversions: UInt128 uses BitVec
#       internally while UIntN uses Fin, so cross-type constructors like ofNatLT and
#       toUInt128 are not definitionally equal even for the same value.  Fix:
#       replace `rfl` with `UInt128.toNat.inj (by simp)` (compares Nat values instead).
#   (b) For toFin theorems use `Fin.ext (by simp [...])` instead of `rfl`.
#   (c) For toBitVec theorems use `BitVec.eq_of_toNat_eq (by simp [...])` instead.
#   (d) setWidth substitution: LITERAL_SUBS replaces "BitVec 64" → "BitVec 128" but
#       misses "setWidth 64" → "setWidth 128" in some proofs; fix manually.
#   After adding USize.toUInt128 and the UIntN.toNat_toUInt128 simp lemmas (see above),
#   essentially all these theorems become provable.  A few theorems remain commented out:
#   - UInt128.toUSize_neg: simp cannot prove BitVec.setWidth(-x) = -BitVec.setWidth(x)
#   - UInt128.toUSize_sub: depends on UInt128.toUSize_neg
#   - USize.ofNat_uInt128Size_sub_one: needs `cases USize.size_eq`; not in reference
#   These three are not present in the reference Lemmas_UInt128.lean and stay omitted.
#
# [uintsimproc / sint] declare_uint/sint_simprocs_ext macro call — auto-generated
#   dsimproc/simproc declarations inside a macro quotation `(...)` produce
#   "Unknown attribute" errors in Lean v4.29.0-rc1.  The script therefore expands
#   the macro body inline (see expand_simproc_macro_body) instead of calling it.

from pathlib import Path
import re
import sys

# ---------------------------------------------------------------------------
# Import-free preambles for each section of the combined output.
# (Imports are already excluded by the should_keep / is_lean_declaration
# pipeline filters and need not appear in a reference file.)
# ---------------------------------------------------------------------------

LEMMAS_PREAMBLE = """\
set_option maxRecDepth 4000

declare_int_theorems Int128 128"""

BASIC_PREAMBLE = "set_option autoImplicit true"

TOEXPR_PREAMBLE = "open Lean"

SINT_PREAMBLE = "open Lean Meta Simp"

UINTSIMPROC_PREAMBLE = "open Lean Meta Simp"

TOINT_PREAMBLE = "open Lean.Grind"

RINGSINT_PREAMBLE = "open Lean Grind"

RINGUINT_PREAMBLE = """\
open Lean Grind

set_option autoImplicit true"""

PRELUDE_PREAMBLE = ""

BASICAUX_PREAMBLE = ""

UINTBASIC_PREAMBLE = ""

UINTLEMMAS_PREAMBLE = """\
set_option autoImplicit true
open Std

declare_uint_theorems UInt128 128"""

# ---------------------------------------------------------------------------
# Ordered (mode, upstream_rel_path, hax_rel_path) for every section.
# ---------------------------------------------------------------------------

SECTIONS: list[tuple[str, str, str]] = [
    ("prelude",     "Init/Prelude.lean",                               "Init/Prelude.lean"),
    ("basicaux",    "Init/Data/UInt/BasicAux.lean",                    "Init/Data/UInt/BasicAux.lean"),
    ("uintbasic",   "Init/Data/UInt/Basic.lean",                       "Init/Data/UInt/Basic.lean"),
    ("basic",       "Init/Data/SInt/Basic.lean",                       "Init/Data/SInt/Basic_Int128.lean"),
    ("toexpr",      "Lean/ToExpr.lean",                                "Lean/ToExpr.lean"),
    ("uintsimproc", "Lean/Meta/Tactic/Simp/BuiltinSimprocs/UInt.lean", "Lean/Tactic/Simp/BuiltinSimpProcs/UInt.lean"),
    ("sint",        "Lean/Meta/Tactic/Simp/BuiltinSimprocs/SInt.lean", "Lean/Tactic/Simp/BuiltinSimpProcs/SInt.lean"),
    ("uintlemmas",  "Init/Data/UInt/Lemmas.lean",                      "Init/Data/UInt/Lemmas_UInt128.lean"),
    ("lemmas",      "Init/Data/SInt/Lemmas.lean",                      "Init/Data/SInt/Lemmas_Int128.lean"),
    ("toint",       "Init/GrindInstances/ToInt.lean",                  "Init/GrindInstances/ToInt.lean"),
    ("ringsint",    "Init/GrindInstances/Ring/SInt.lean",              "Init/GrindInstances/Ring/SInt.lean"),
    ("ringuint",    "Init/GrindInstances/Ring/UInt.lean",              "Init/GrindInstances/Ring/UInt.lean"),
]

# ---------------------------------------------------------------------------
# BasicAux mode: substitutions applied after the standard renaming.
# The upstream encodes small-to-large widening conversions using a Fin-based
# proof construction that is valid for UInt64 but causes `decide` to evaluate
# 2^128 (a 39-digit number) for UInt128.  Replace with BitVec.ofNat instead.
# ---------------------------------------------------------------------------

BASICAUX_SUBS = [
    ("⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩",
     "⟨BitVec.ofNat 128 a.toNat⟩"),
]

# ---------------------------------------------------------------------------
# UIntBasic mode: substitutions applied after the standard renaming.
# ---------------------------------------------------------------------------

UINTBASIC_SUBS = [
    # Shift modulus: 128-bit shifts are taken mod 128, not 64.
    ("UInt128.mod b 64)", "UInt128.mod b 128)"),
]

# ---------------------------------------------------------------------------
# Sint / UIntSimproc modes: substitutions applied to the extracted macro body.
# The upstream macro uses builtin_dsimproc/builtin_simproc (for types built
# into the Lean kernel); Int128 is not built-in, so we use dsimproc/simproc.
# We also rename the macro to avoid clashing with the upstream definition.
# SIMPROC_COMMON_SUBS holds the two replacements shared by both modes; each
# mode-specific list appends only its macro-rename entry.
# ---------------------------------------------------------------------------

SIMPROC_COMMON_SUBS = [
    ("builtin_dsimproc", "dsimproc"),
    ("builtin_simproc",  "simproc"),
]

SINT_SUBS        = SIMPROC_COMMON_SUBS + [('"declare_sint_simprocs"', '"declare_sint_simprocs_ext"')]
UINTSIMPROC_SUBS = SIMPROC_COMMON_SUBS + [('"declare_uint_simprocs"', '"declare_uint_simprocs_ext"')]


def extract_simproc_macro(lines: list[str], macro_name: str) -> list[str]:
    """
    Extract the named macro definition from the upstream file, stopping just
    before the first invocation (first line starting with '{macro_name} ').
    """
    in_macro = False
    result = []
    for line in lines:
        if not in_macro:
            if line.startswith(f'macro "{macro_name}"'):
                in_macro = True
                result.append(line)
        else:
            if line.startswith(f"{macro_name} "):
                break  # first invocation — stop here
            result.append(line)
    return result


def _uint_simproc_expand_subs(typename: str) -> list[tuple[str, str]]:
    """
    Substitution list to expand Lean metaprogramming syntax in the UInt simproc
    macro body (`( ... )`) to concrete Lean code for `typename`.
    Applied in order; more-specific patterns precede their shorter prefixes.
    """
    return [
        # Quoted Name literals
        ("$(quote typeName.getId)",          f"``{typename}"),
        ("$(quote ofNatLT.getId)",           f"``{typename}.ofNatLT"),
        ("$(quote toNat.getId)",             f"``{typename}.toNat"),
        ("$(quote ofNat)",                   f"``{typename}.ofNat"),
        # Named dsimproc/simproc identifiers wrapped in $(mkIdent ...):ident
        ("$(mkIdent `reduceAdd):ident",      "reduceAdd"),
        ("$(mkIdent `reduceMul):ident",      "reduceMul"),
        ("$(mkIdent `reduceSub):ident",      "reduceSub"),
        ("$(mkIdent `reduceDiv):ident",      "reduceDiv"),
        ("$(mkIdent `reduceMod):ident",      "reduceMod"),
        ("$(mkIdent `reduceLT):ident",       "reduceLT"),
        ("$(mkIdent `reduceLE):ident",       "reduceLE"),
        ("$(mkIdent `reduceGT):ident",       "reduceGT"),
        ("$(mkIdent `reduceGE):ident",       "reduceGE"),
        ("$(mkIdent `reduceOfNatLT):ident",  "reduceOfNatLT"),
        ("$(mkIdent `reduceOfNat):ident",    "reduceOfNat"),
        ("$(mkIdent `reduceToNat):ident",    "reduceToNat"),
        # Ident expressions
        ("$(mkIdent ofNatLT)",               "ofNatLT"),
        ("$(mkIdent ofNat)",                 "ofNat"),
        # Bare dollar-idents (used in simproc patterns / bodies)
        ("$ofNatLT",   "ofNatLT"),
        ("$toNat",     "toNat"),
        ("$fromExpr",  "fromExpr"),
        ("$typeName",  typename),
    ]


def _sint_simproc_expand_subs(typename: str) -> list[tuple[str, str]]:
    """
    Substitution list to expand Lean metaprogramming syntax in the SInt simproc
    macro body (`( ... )`) to concrete Lean code for `typename`.
    """
    return [
        # Quoted Name literals
        ("$(quote typeName.getId)",              f"``{typename}"),
        ("$(quote ofIntLE.getId)",               f"``{typename}.ofIntLE"),
        ("$(quote toInt.getId)",                 f"``{typename}.toInt"),
        ("$(quote toNatClampNeg.getId)",         f"``{typename}.toNatClampNeg"),
        ("$(quote ofNat)",                       f"``{typename}.ofNat"),
        ("$(quote ofInt)",                       f"``{typename}.ofInt"),
        # Named dsimproc/simproc identifiers wrapped in $(mkIdent ...):ident
        ("$(mkIdent `reduceAdd):ident",          "reduceAdd"),
        ("$(mkIdent `reduceMul):ident",          "reduceMul"),
        ("$(mkIdent `reduceSub):ident",          "reduceSub"),
        ("$(mkIdent `reduceDiv):ident",          "reduceDiv"),
        ("$(mkIdent `reduceMod):ident",          "reduceMod"),
        ("$(mkIdent `reduceLT):ident",           "reduceLT"),
        ("$(mkIdent `reduceLE):ident",           "reduceLE"),
        ("$(mkIdent `reduceGT):ident",           "reduceGT"),
        ("$(mkIdent `reduceGE):ident",           "reduceGE"),
        ("$(mkIdent `reduceOfIntLE):ident",      "reduceOfIntLE"),
        ("$(mkIdent `reduceOfNat):ident",        "reduceOfNat"),
        ("$(mkIdent `reduceOfInt):ident",        "reduceOfInt"),
        ("$(mkIdent `reduceToInt):ident",        "reduceToInt"),
        ("$(mkIdent `reduceToNatClampNeg):ident","reduceToNatClampNeg"),
        # Ident expressions
        ("$(mkIdent ofNat)",   "ofNat"),
        ("$(mkIdent ofInt)",   "ofInt"),
        # Bare dollar-idents
        ("$ofIntLE",        "ofIntLE"),
        ("$toInt",          "toInt"),
        ("$toNatClampNeg",  "toNatClampNeg"),
        ("$fromExpr",       "fromExpr"),
        ("$typeName",       typename),
    ]


def expand_simproc_macro_body(macro_text: str, typename: str, mode: str) -> str:
    """
    Extract the `( ... )` quotation body from the already-substituted macro
    definition text and expand Lean metaprogramming syntax to produce a
    concrete inline `namespace {typename} ... end {typename}` block.

    This replaces the broken `declare_{uint,sint}_simprocs_ext {typename}` call:
    dsimproc/simproc inside a macro quotation produce "Unknown attribute" errors.
    """
    marker = "`(\n"
    start = macro_text.index(marker) + len(marker)
    end = macro_text.rindex("\n)")
    body = macro_text[start:end]

    subs = (_uint_simproc_expand_subs(typename) if mode == "uintsimproc"
            else _sint_simproc_expand_subs(typename))
    for old, new in subs:
        body = body.replace(old, new)
    return body

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
    If the first line is `@[extern "..."]` or `@[extern "...", instance_reducible]`,
    remove the extern attribute.  The `instance_reducible` attribute, when present,
    is preserved as `@[instance_reducible]` on the same line; other co-located
    attributes (e.g. `tagged_return`) are FFI-specific and are dropped along with
    the extern.  If the decorator line contained only the extern entry, it is
    dropped entirely.
    """
    lines = item.split("\n")
    if not lines or not lines[0].startswith('@[extern "'):
        return item
    if "instance_reducible" in lines[0]:
        lines[0] = "@[instance_reducible]"
        return "\n".join(lines)
    return "\n".join(lines[1:])


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


def extract_namespace_block(lines: list[str], typename: str) -> list[str]:
    """
    Return all lines from 'namespace {typename}' to 'end {typename}' inclusive,
    stripping trailing blank lines.
    """
    start, end = None, None
    for i, line in enumerate(lines):
        if line == f"namespace {typename}":
            start = i
        elif start is not None and line == f"end {typename}":
            end = i
            break
    if start is None or end is None:
        return []
    result = list(lines[start:end + 1])
    while result and not result[-1].strip():
        result.pop()
    return result


def extract_grind_section(lines: list[str], typename: str, next_typename: str) -> list[str]:
    """
    Return lines for {typename} from the Lean.Grind namespace section.
    Starts at the 'attribute [local instance] {typename}.natCast {typename}.intCast'
    line and stops just before {next_typename}'s equivalent line or 'end Lean.Grind'.
    Trailing blank lines are stripped.
    """
    result = []
    in_section = False
    for line in lines:
        if not in_section:
            if f"{typename}.natCast {typename}.intCast" in line:
                in_section = True
        else:
            if (f"{next_typename}.natCast {next_typename}.intCast" in line
                    or line == "end Lean.Grind"):
                break
        if in_section:
            result.append(line)
    while result and not result[-1].strip():
        result.pop()
    return result


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


def find_lean_src() -> Path:
    """Return the Lean source root for the project's toolchain."""
    p = Path(__file__).resolve().parent
    while True:
        candidate = p / "lean-toolchain"
        if candidate.exists():
            version = candidate.read_text().strip()
            # e.g. "leanprover/lean4:v4.29.0-rc1" -> "leanprover--lean4---v4.29.0-rc1"
            toolchain_dir = version.replace("/", "--").replace(":", "---")
            return Path.home() / ".elan" / "toolchains" / toolchain_dir / "src" / "lean"
        if p.parent == p:
            raise FileNotFoundError("lean-toolchain not found in any parent directory")
        p = p.parent


def generate(mode: str, raw_lines: list[str]) -> str:
    """Run the transformation pipeline for *mode* and return the content string."""

    def _with_preamble(preamble: str, body: str) -> str:
        if preamble:
            return preamble + "\n\n" + body
        return body

    if mode == "sint":
        macro_lines = extract_simproc_macro(raw_lines, "declare_sint_simprocs")
        macro_text = "\n".join(macro_lines)
        for old, new in SINT_SUBS:
            macro_text = macro_text.replace(old, new)
        inline = expand_simproc_macro_body(macro_text, "Int128", mode)
        comment = ("-- declare_sint_simprocs_ext Int128"
                   " -- macro call replaced with direct inline")
        body = macro_text.rstrip() + "\n\n" + comment + "\n" + inline
        return _with_preamble(SINT_PREAMBLE, body)

    elif mode == "uintsimproc":
        macro_lines = extract_simproc_macro(raw_lines, "declare_uint_simprocs")
        macro_text = "\n".join(macro_lines)
        for old, new in UINTSIMPROC_SUBS:
            macro_text = macro_text.replace(old, new)
        inline = expand_simproc_macro_body(macro_text, "UInt128", mode)
        comment = ("-- declare_uint_simprocs_ext UInt128"
                   " -- macro call replaced with direct inline"
                   " (macros don't handle dsimproc correctly)")
        body = macro_text.rstrip() + "\n\n" + comment + "\n" + inline
        return _with_preamble(UINTSIMPROC_PREAMBLE, body)

    elif mode == "prelude":
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
        return _with_preamble(PRELUDE_PREAMBLE, "\n\n".join(kept))

    elif mode == "basicaux":
        # BasicAux mode: strip @[extern "..."] decorator lines (all UInt64
        # definitions in this file have extern implementations) and apply
        # BASICAUX_SUBS to fix the body of widening conversions.  No
        # is_uint64_primary_definition filter needed — every UInt64 item in
        # this file is a genuine UInt64 definition or conversion.
        kept: list[str] = []
        for item in split_into_items(raw_lines):
            if (should_keep(item)
                    and is_lean_declaration(item)
                    and not is_extern_attribute_decl(item)):
                item = strip_extern_decorator(item)
                item = apply_substitutions(item)
                for old, new in BASICAUX_SUBS:
                    item = item.replace(old, new)
                kept.append(item)
        return _with_preamble(BASICAUX_PREAMBLE, "\n\n".join(kept))

    elif mode == "ringuint":
        # RingUInt mode: extract the UInt64 namespace block and the UInt64 section
        # of the Lean.Grind namespace verbatim, then apply standard substitutions.
        # The item-based pipeline cannot be used here because the namespace wrapper
        # lines and the `attribute [local instance] natCast intCast` line lack
        # "UInt64" and would be dropped by should_keep.
        ns_lines = extract_namespace_block(raw_lines, "UInt64")
        grind_lines = extract_grind_section(raw_lines, "UInt64", "USize")
        ns_text = apply_substitutions("\n".join(ns_lines))
        grind_text = apply_substitutions("\n".join(grind_lines))
        return _with_preamble(RINGUINT_PREAMBLE, ns_text + "\n\n" + grind_text)

    elif mode == "uintbasic":
        # UIntBasic mode: strip @[extern "..."] decorators (preserving any
        # co-located attributes such as instance_reducible), drop the two
        # USize↔UInt64 cross-type conversions that are either already in
        # BasicAux or produce wrong bodies for UInt128, then apply UINTBASIC_SUBS
        # to fix shift moduli and qualify ofNat.
        kept: list[str] = []
        for item in split_into_items(raw_lines):
            if (should_keep(item)
                    and is_lean_declaration(item)
                    and not is_extern_attribute_decl(item)):
                item = strip_extern_decorator(item)
                # Drop USize↔UInt64 conversions (wrong body / belongs in BasicAux)
                first = item.split("\n")[0]
                if (first.startswith("def UInt64.toUSize")
                        or first.startswith("def USize.toUInt64")):
                    continue
                item = apply_substitutions(item)
                for old, new in UINTBASIC_SUBS:
                    item = item.replace(old, new)
                kept.append(item)
        return _with_preamble(UINTBASIC_PREAMBLE, "\n\n".join(kept))

    else:
        preamble = {
            "lemmas":     LEMMAS_PREAMBLE,
            "basic":      BASIC_PREAMBLE,
            "toexpr":     TOEXPR_PREAMBLE,
            "toint":      TOINT_PREAMBLE,
            "ringsint":   RINGSINT_PREAMBLE,
            "uintlemmas": UINTLEMMAS_PREAMBLE,
        }[mode]

        kept: list[str] = []
        for item in split_into_items(raw_lines):
            if (should_keep(item)
                    and is_lean_declaration(item)
                    and not is_extern_attribute_decl(item)):
                if mode == "basic":
                    # Int128 is not a built-in kernel type; strip @[extern "..."]
                    # decorators (only ISize conversion defs carry them here).
                    item = strip_extern_decorator(item)
                kept.append(apply_substitutions(item))

        return _with_preamble(preamble, "\n\n".join(kept))


def make_section(upstream_rel: str, hax_rel: str, content: str) -> str:
    bar = "-- " + "\u2500" * 70
    return (f"{bar}\n"
            f"-- Source: {upstream_rel}\n"
            f"-- Target: Hax/MissingLean/{hax_rel}\n"
            f"{bar}\n\n"
            f"{content}")


def main() -> None:
    output_path = sys.argv[1] if len(sys.argv) > 1 else None

    lean_src = find_lean_src()
    sections = []
    for mode, upstream_rel, hax_rel in SECTIONS:
        raw_lines = (lean_src / upstream_rel).read_text(encoding="utf-8").splitlines()
        content = generate(mode, raw_lines)
        sections.append(make_section(upstream_rel, hax_rel, content))

    output = "\n\n".join(sections) + "\n"
    if output_path:
        Path(output_path).write_text(output, encoding="utf-8")
        print(f"Written to {output_path}", file=sys.stderr)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
