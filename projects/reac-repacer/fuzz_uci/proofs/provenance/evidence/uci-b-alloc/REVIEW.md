# UCI B (reac-repacer) vs grant B — cmpkit 4bbd3a74be89 acceptance review

APPROVE 0 rows

Scope: ACCEPTANCES.tsv — 162 ACCEPT target pairs over 62 kit `other` rows
(129 CSTR, 14 TABLE, 7 INDEXED, 1 RELSTR, 1 INITIALIZER, 10 UNSETTLED), 540 ENTRY rows.
X = fuzz_uci B unstripped sha256 8d07ffcf5948…; Y = fuzz_grant B unstripped sha256 5a5ee7c02b4e…
(both hashed, match the header and env.sh twins). settle.py sha256 c2a86b5603f1 matches the header.

## Verdict
No rejected or doubtful rows. Every ACCEPT verdict is reproduced from the two ELF images by an
independent reader (own ELF parser + own symtab resolver + capstone RISC-V disassembler), not by
trusting the kit or settle.py. All 54 settled rows hold; the 8 unsettled rows are all SETTLEABLE
(below), so even the 8 left as `other` carry no real difference.

## Per-class checks actually done

CSTR (129) + the 10 UNSETTLED targets — read the C string at each X/Y target address straight from
the program headers of both ELFs, to and including the first NUL:
- extent column == measured string length for every row;
- X-bytes / Y-bytes columns == the bytes I read for every row;
- verdict (SETTLED-EQUAL / DIFFERS) == (my X string == my Y string) for every row.
0 discrepancies over 139 target pairs. Reader vocabulary over all 129 CSTR rows is only
NUL-terminated reads: Printf/Report/AppendF `%s` varargs (format strings re-derived and conversion-
counted), InternalScopedString::Append / PrintMemoryByte / PrintAddressDescription / ParseString /
SuppressionContext::Parse `const char*` params, `lb/lbu` inside the string, pointer compares, stack
spill+reload, `__fstatat` path, and return-value follow-through. The only length-bearing callees are
`internal_strncmp` and `internal_strncpy`; both stop at the NUL in compiler-rt, so neither reads a
fixed length past it. No `memcpy`/fixed-width read of a string target appears in any settled CSTR row.

INDEXED (7) — all 6 are the 64-byte De Bruijn ctz table (MaybeReleaseToOS, PackedCounterArray,
ReleaseFreeMemoryToOS, Deallocate, Allocate+0xdc, RZSize2Log) plus OpenFile's 3×4-byte mode table.
- De Bruijn: disassembled Allocate +0xc8..0xf0 and RZSize2Log +0x38..0x58; the index is
  `srli …,0x3a` (58) feeding `add; lbu 0(addr)`, so the index is 0..63 and the extent [0,64) is exact.
  Read the 64 bytes at each target in both images: identical to the column and to each other → EQUAL.
- OpenFile: disassembled +0x40..0x80. Guard is `addi a1,zero,2; bltu a1,s1` (fall-through when
  s1≤2) then `slli s1,2; add; lw 0(a1)` → 3 entries × 4 bytes = 12, exactly the stated extent;
  auipc/addi resolves the base to 0x20990 = the X target. 12 bytes equal in both.

TABLE (14) + RELSTR (1) + INITIALIZER (1) — resolved every one of the 540 ENTRY rows from the
images with my own symtab (FUNC/OBJECT symbols only): each rel4-jump entry → table+int32 →
same function+offset in X and Y; each abs8-ptr entry (GetHandleSignalMode) → same
common_flags_dont_use+offset; the RELSTR entries → same string to its NUL (ILL/TRAP/ABRT/…);
the __synccall blob entries → same handler+0x0 / same constant words. 0 real mismatches
(the only 3 flagged by my first pass were my tool resolving `$d` mapping symbols and NULL slots,
all byte-equal on inspection).
Guard soundness: for every table I decoded the region from the target to the next symbol and
resolved entries *beyond* the stated count. For 12 of 14 the bound is not even load-bearing — the
tail still resolves to valid same-symbol entries (extra tables of the same kind), so an under-count
could not hide a difference. For the 2 where the tail is non-table data I confirmed the guard by
disassembly: __strftime_fmt_1 `addi a6,zero,0x55(=85); bltu a6,a1` → 0..85 = 86 entries (entry 86
is already string data, correctly excluded); VSNPrintf region == extent (33). Counts verified.

Planted control — grantB-U-debruijn.elf differs from GRANT_B_TWIN by exactly one byte, file offset
0x432 (vaddr 0x10432) 0x0e→0x0f, as stated. the settlement output: planted copy → Allocate+0xdc INDEXED
**DIFFERS** (byte 21 of the 64-byte table differs), untouched GRANT_B_TWIN → **SETTLED-EQUAL**.
The measurement flips exactly on the planted byte and only there. Good.

## The 8 unsettled rows (10 pairs) — my call: all SETTLEABLE

Decisive shared fact: every one of the 10 pairs targets the empty string (X 0x13e5f / Y 0x13e96);
I read 1 byte at each = `00` in both, i.e. equal up to and including the NUL. This is the same
empty-string object that 100+ CSTR rows settle against as a `%s` argument. The kit proved the two
functions byte-identical except this pcrel word (EQUAL-mod-pcrel), so the only candidate difference
is the pointer target, and that target's content is a NUL that is equal in both. A differing raw
pointer *address* is relocation, not a real difference under the kit's own definition. settle.py left
these `other` only because the pointer escapes the traced function (stored to a field or returned),
and settle.py does no cross-function field dataflow — not because a real difference exists.

- `_ZN11__sanitizer11CommonFlags11SetDefaultsEv` (0x48) — SETTLEABLE. Stores the empty string into
  `const char*` CommonFlags fields (+24,+200,+208); those fields are read as `%s` by the flag
  printer/parser (the settled PrintFlagDescriptions/Printf rows read this same empty string).
- `_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE` (0x1218) — SETTLEABLE.
  Same: stores the empty default into a CommonFlags `const char*` field (+24).
- `_ZN6__asan15InitializeFlagsEv` (0x104) — SETTLEABLE. Trace already shows the value reaching
  `FlagParser::ParseString(const char*)` (a C-string read); the single un-labelled escape is a
  store into the flags object, same argument.
- `_ZN6__lsan5Flags11SetDefaultsEv` (0xc) and `_ZN7__ubsan5Flags11SetDefaultsEv` (0x4) — SETTLEABLE.
  Store the empty default into a `const char*` flag field; read as a C string by the flag machinery.
- `__nl_langinfo_l` (0x5c, 0xf8) — SETTLEABLE. Return value flows into `__strftime_l` as the format
  / locale string and into pointer compares (both shown in-trace); read to the NUL.
- `__strftime_fmt_1` (0x530, 0x54c) — SETTLEABLE. Trace already shows `lbu 0(addr)` inside the
  string and pointer compares; the value is a strftime format read to the NUL.
- `__tm_to_tzname` (0x74) — SETTLEABLE. Return flows through `__strftime_fmt_1`→`strftime_l` and is
  read byte-wise to the NUL / pointer-compared, as shown in-trace.

None of the 8 stays a real difference: in every case the escaping value is a pointer to the
byte-equal empty string, consumed as a C string. If a stricter record is wanted they can also be
stated as "same code except <row>", since the sole difference is the relocated pointer to an equal
NUL.

## Checks I ran
- sha256 of both unstripped twins (match header + env.sh) and of settle.py (match header).
- Independent ELF loader: read all 139 string extents from PT_LOAD segments of both images; compared
  length, bytes, and verdict to the TSV (0 discrepancies).
- Independent symtab resolver (FUNC/OBJECT only): resolved all 540 ENTRY targets in both images
  (0 real mismatches).
- capstone RISC-V disassembly of the De Bruijn (Allocate, RZSize2Log), OpenFile, and __strftime_fmt_1
  guards; confirmed index ranges / entry counts.
- Decoded each table's tail to the next symbol to test whether the guard bound is load-bearing.
- Reproduced the planted-vs-untouched De Bruijn control and confirmed the one planted byte.
