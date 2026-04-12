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
#
# --mode basicaux  (Init/Data/UInt/BasicAux.lean → Init/Data/UInt/BasicAux.lean)
# ────────────────────────────────────────────────────────────────────────────────
# 1. Four conversions have no upstream counterpart (no UInt64.toUInt64,
#    USize.toUInt64, UInt64.toUSize, or USize.toUSize in the UInt64 block) and
#    must be added manually after generation:
#      def UInt128.toUInt64 (a : UInt128) : UInt64 := a.toNat.toUInt64
#      def UInt128.toUSize  (a : UInt128) : USize  := a.toNat.toUSize
#      def UInt64.toUInt128 (a : UInt64)  : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩
#      def USize.toUInt128  (a : USize)   : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩
#
# --mode uintbasic  (Init/Data/UInt/Basic.lean → Init/Data/UInt/Basic.lean)
# ─────────────────────────────────────────────────────────────────────────
# 1. The `additional_uint_decls` macro (overflow helpers toNat_add_of_lt etc.)
#    and its invocations have no upstream counterpart; must be added manually.
# 2. The `declare_missing_uint_conversions` macro and its invocation have no
#    upstream counterpart; must be added manually.
# 3. The generated output has `@[instance_reducible]\ndef UInt128.decLt/decLe`
#    (instance_reducible preserved from the stripped extern decorator) plus a
#    separate `attribute [instance] UInt128.decLt UInt128.decLe`.  The existing
#    hax file instead uses a combined
#    `attribute [instance_reducible, instance] UInt128.decLt UInt128.decLe`.
#    Both are functionally equivalent.
# 4. `UInt128.ofInt` uses bare `ofNat` (from upstream `UInt64.ofInt`):
#      def UInt128.ofInt (x : Int) : UInt128 := ofNat (x % 2 ^ 128).toNat
#    The hax file qualifies it as `UInt128.ofNat`.  Fix: replace manually or
#    add a UINTBASIC_SUBS entry `(": UInt128 := ofNat ", ": UInt128 := UInt128.ofNat ")`.
# 5. The `@[deprecated]` modn definition and the `HMod UInt128 Nat UInt128`
#    instance are generated without their upstream `set_option linter.*` wrappers
#    (those lines contain no "UInt64" and are dropped by should_keep).
#    The generated file may trigger linter warnings at use sites.
#
# --mode ringuint  (Init/GrindInstances/Ring/UInt.lean → Init/GrindInstances/Ring/UInt.lean)
# ─────────────────────────────────────────────────────────────────────────────────────────────
# 1. The `-- A better proof would be welcome!` comment inside `intCast_ofNat` is
#    preserved in the generated output (verbatim from upstream). The existing hax
#    file also keeps this comment, so no manual fix is needed.
#
# --mode uintlemmas  (Init/Data/UInt/Lemmas.lean → Init/Data/UInt/Lemmas_UInt128.lean)
# ─────────────────────────────────────────────────────────────────────────────────────
# 1. `UInt128.toNat_toUInt64` has no upstream counterpart (the macro only
#    generates `toNat_toUInt64` for types with fewer than 64 bits, where the
#    result is lossless).  Must be added manually:
#      @[simp] theorem UInt128.toNat_toUInt64 (x : UInt128) :
#          x.toUInt64.toNat = x.toNat % 2 ^ 64 := (rfl)
# 2. Widening theorems (`X.toUInt128`-based items, e.g. `USize.toNat_toUInt128`,
#    `UInt8.toFin_toUInt128`, `UInt8.toBitVec_toUInt128`, `UInt64.ofFin_uXToFin`,
#    `UInt128.ofBitVec_uXToBitVec` widening, etc.) are generated as active
#    theorems, but the hax file comments them out.  The `(rfl)` proofs for
#    the widening direction may also be wrong because `X.toUInt128` uses
#    `BitVec.ofNat 128 x.toNat` whose `toNat` only reduces modulo 2^128
#    propositionally, not definitionally.
# 3. Hax-specific theorems not in the upstream UInt64 block (e.g.
#    `UInt128.toNat_ofNatTruncate_of_lt/le`, `UInt128.toFin_ofNatTruncate_of_lt/le`,
#    `UInt128.toBitVec_ofNatTruncate_of_lt/le`, `USize.size_dvd_uInt128Size`,
#    and many cross-type `toUX_ofNatTruncate_of_le` lemmas) are not generated
#    and must be added manually.
#
# --mode uintsimproc  (Lean/Meta/Tactic/Simp/BuiltinSimprocs/UInt.lean → BuiltinSimpProcs/UInt.lean)
# ────────────────────────────────────────────────────────────────────────────────────────────────────
# 1. The generated file uses the macro approach (declare_uint_simprocs_ext UInt128)
#    whereas the existing hax file has the declarations written out directly inside
#    `namespace UInt128`.  Both are functionally equivalent.
# 2. The USize special block (lines 92–110 of the upstream, with platform-dependent
#    `numBits` math) is not generated; it handles platform-dependent bit widths
#    irrelevant to UInt128.

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
    ("uintsimproc", "Lean/Meta/Tactic/Simp/BuiltinSimprocs/UInt.lean", "Lean/Tactic/Simp/BuiltinSimpProcs/UInt.lean"),
    ("uintlemmas",  "Init/Data/UInt/Lemmas.lean",                      "Init/Data/UInt/Lemmas_UInt128.lean"),
    ("basic",       "Init/Data/SInt/Basic.lean",                       "Init/Data/SInt/Basic_Int128.lean"),
    ("sint",        "Lean/Meta/Tactic/Simp/BuiltinSimprocs/SInt.lean", "Lean/Tactic/Simp/BuiltinSimpProcs/SInt.lean"),
    ("toexpr",      "Lean/ToExpr.lean",                                "Lean/ToExpr.lean"),
    ("toint",       "Init/GrindInstances/ToInt.lean",                  "Init/GrindInstances/ToInt.lean"),
    ("ringsint",    "Init/GrindInstances/Ring/SInt.lean",              "Init/GrindInstances/Ring/SInt.lean"),
    ("ringuint",    "Init/GrindInstances/Ring/UInt.lean",              "Init/GrindInstances/Ring/UInt.lean"),
    ("lemmas",      "Init/Data/SInt/Lemmas.lean",                      "Init/Data/SInt/Lemmas_Int128.lean"),
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

UINTSIMPROC_SUBS = [
    ("builtin_dsimproc",        "dsimproc"),
    ("builtin_simproc",         "simproc"),
    ('"declare_uint_simprocs"', '"declare_uint_simprocs_ext"'),
]


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
        body = macro_text.rstrip() + "\n\ndeclare_sint_simprocs_ext Int128"
        return _with_preamble(SINT_PREAMBLE, body)

    elif mode == "uintsimproc":
        macro_lines = extract_simproc_macro(raw_lines, "declare_uint_simprocs")
        macro_text = "\n".join(macro_lines)
        for old, new in UINTSIMPROC_SUBS:
            macro_text = macro_text.replace(old, new)
        body = macro_text.rstrip() + "\n\ndeclare_uint_simprocs_ext UInt128"
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
                    and not is_isize_conversion(item)
                    and not uses_unavailable_typeclass(item)):
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
