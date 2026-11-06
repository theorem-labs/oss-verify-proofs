# Review of the empty-string acceptance at RegisterCommonFlags +0x1218

VERDICT: ACCEPT

The acceptance is correct. Its conclusion holds: both places are the C string "" (one NUL byte). The only code that reads the address is FlagHandlerInclude::Format, which passes it as the argument of a "%s" conversion with no precision, and that conversion reads up to the NUL. The record has three wording errors (check 5). None of them changes the verdict.

Method
- I re-derived every fact with my own reads. I did not reuse code from gates/settle-sm1.py. Tools: pyelftools 0.33 and capstone 5.0.7 (RISCV64 | RVC). I decoded every STT_FUNC symbol of both images by its symbol range: 1428 functions in the donor and 1402 in the target, every one decoded completely.
- Images: <donor twin> fuzz_grant.asan (sha256 prefix 57c26f993615) and <target twin> fuzz_uci.asan (sha256 prefix 56822e263d76). Both prefixes match the values I computed.
- Both images are ET_EXEC, EM_RISCV and statically linked. They have no SHT_RELA, SHT_REL or SHT_DYNAMIC section and no PT_DYNAMIC or PT_INTERP segment. Thus the file bytes of code, .rodata and .data.rel.ro are the bytes at run time; no relocation changes them.

Check 1: the place is the same C string "" on both sides, from file bytes. Result: PASS.
- Donor place 0x13f5f is in .rodata (SHT_PROGBITS, 0x102e0 + 0x1296c). It is in the first PT_LOAD (vaddr 0x10000, offset 0, filesz = memsz = 0x1f7dc, flags R only), so it is in the file part, not zero fill. The byte at file offset 0x3f5f is 0x00. Bytes 0x13f57..0x13f66 are 69 6f 6e 2e 63 70 70 00 | 00 | 27 00 48 49 4e 54 3a, which is the end of "...ion.cpp", then the place, then "'" and "HINT:...".
- Target place 0x13e5f is in .rodata (SHT_PROGBITS, 0x102e0 + 0x122e4). It is in the first PT_LOAD (vaddr 0x10000, offset 0, filesz = memsz = 0x1ebf0, flags R only). The byte at file offset 0x3e5f is 0x00. The 16 bytes around it are the same as in the donor.
- On both sides, the byte before the place is 0x00. The place is therefore a separate 1-byte string, not the tail of a longer string. The segment is read-only, so the byte cannot change at run time.
- The C string at each place, with its NUL, is b'\x00' (1 byte). The two are equal. The kit's difference at region offset 4241 is past this NUL.

Check 2: the address and every use of it in RegisterCommonFlags. Result: PASS.
- The function is _ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE: donor 0x61974, target 0x605ac, size 0x12a4 on both sides.
- Donor: +0x1210 `9715fbff auipc a1, 0xfffb1` gives a1 = 0x62b84 - 0x4f000 = 0x13b84. Then +0x1218 `1389b53d addi s2, a1, 0x3db` gives s2 = 0x13f5f.
- Target: +0x1210 `9725fbff auipc a1, 0xfffb2` gives a1 = 0x137bc. Then +0x1218 `1389356a addi s2, a1, 0x6a3` gives s2 = 0x13e5f.
- The vtable register: +0x120c auipc a0 and +0x1214 addi s1, a0 give s1 = 0x9c270 (donor) and 0x96b90 (target). These equal _ZTVN11__sanitizer18FlagHandlerIncludeE (donor 0x9c260, target 0x96b80) + 0x10.
- The objects:
  - +0x11fc calls GetGlobalLowLevelAllocator, +0x1200 sets a1 = 0x20, +0x1204 calls LowLevelAllocator::Allocate, and +0x1208 does `mv a2, a0`. Thus a2 is a fresh 0x20-byte block from the runtime's internal LowLevelAllocator, not a malloc heap block.
  - +0x1244, +0x1248, +0x124c and +0x1250 make the second block the same way.
  - s0 is the FlagParser* argument: +0x28 does `mv s0, a0`, and the only other write of s0 is the restore at +0x1280.
- Register def-use, scanned from +0x1218 to the function end at +0x12a0, on both sides:
  - s2 is read only at +0x1228 and +0x1274, both `233c2601 sd s2, 0x18(a2)`. Its next write is +0x1288 `ld s2, 0x20(sp)`, the epilogue restore.
  - At each store, field +0 of the same a2 receives s1: +0x121c and +0x1268 `sd s1, 0(a2)`. Field +8 receives s0 (+0x1220 and +0x126c). Field +0x10 receives the byte 0 (+0x1224) or 1 (+0x1270). a2 does not change between each store of field +0 and the store of field +0x18. s1 is read only at those two stores and is written next at +0x1284.
  - a1, the auipc high part, is not read again before +0x1234 overwrites it.
  - This layout agrees with FlagHandlerInclude: vptr, parser_, ignore_missing_, original_path_.
- Control flow:
  - From +0x1218 to the end, the only control transfers are 3 calls (`jal` with rd = ra) and the final tail jump. The calls are +0x1240 FlagParser::RegisterHandler (a2 = first object, a1 = "include"), +0x1244 GetGlobalLowLevelAllocator and +0x124c LowLevelAllocator::Allocate. The tail jump is +0x12a0 `j` to RegisterHandler (a0 = s0, a1 = "include_if_exists", a2 = second object), after s2 is restored.
  - The function has no indirect jump anywhere.
  - No direct branch or jal anywhere in either image goes to an address in (+0x1218, +0x12a4).
- Callees and s2:
  - RegisterHandler and GetGlobalLowLevelAllocator do not touch s2.
  - Allocate stores s2 only in its prologue (+0x10 `sd s2, 0(sp)`) and writes s2 at +0x40 before any read. The only branch before +0x40 is +0x24 to the CHECK-failure path at +0x11c, which does not read s2. Allocate restores s2 at +0xdc.
  - Thus no callee consumes the address.
- Conclusion: the only consumer of the address in this function is the two stores into field +0x18 of the two new FlagHandlerInclude objects ("include" and "include_if_exists"). The objects are then given to RegisterHandler.

Check 3: who reads field +0x18 of a FlagHandlerInclude. Result: PASS. The only reader is Format, as a "%s" argument read up to the NUL.
- The vtable: _ZTVN11__sanitizer18FlagHandlerIncludeE has size 32, in .data.rel.ro and in the file part of its PT_LOAD.
  - Donor words: 0, 0, 0x62c3c (FlagHandlerInclude::Parse), 0x62cf8 (FlagHandlerInclude::Format).
  - Target words: 0, 0, 0x61874 (Parse), 0x61930 (Format).
  - There are only two virtual slots (+0x10 Parse, +0x18 Format) and no destructor slot. The RTTI word is 0. The images have no symbol for a FlagHandlerBase vtable or for FlagHandlerBase method bodies, so no base-class method can run on these objects.
- Which addresses reach the class:
  - The Format address is present only as the data word at vtable+0x18 (donor 0x9c278, target 0x96b98). No code forms it and no direct call or jump goes to it. The Parse address is present only at vtable+0x10.
  - No code forms an address in [vtable, vtable+0x20) other than vtable+0x10, and only in two functions: RegisterCommonFlags +0x1214 and the separate copy of RegisterIncludeFlags. No data word holds an address in the vtable.
  - Thus Format runs only by a slot-+8 load through the vptr of a FlagHandlerInclude object.
- Parse, all 47 instructions read:
  - The object is in a0 until +0x24 and in s0 from +0x18 until +0x68 (`mv s0, a0` takes the ParseFile result). a1 and s1 hold the value argument, and s2 holds the MmapOrDie buffer.
  - The only access to +0x18 is +0x1c `233cb500 sd a1, 0x18(a0)`, a write (original_path_ = value). The other object accesses are `ld a0, 8(s0)` and `lbu a2, 0x10(s0)` (+0x58/+0x5c and +0x98/+0x9c).
  - No callee receives the object pointer: strchr, MmapOrDie and SubstituteForFlagValue get the value or the buffer, and ParseFile gets parser_.
- Format, all 15 instructions read:
  - +0x10 `83368501 ld a3, 0x18(a0)`, then +0x14 `mv a0, a1` (buffer), then +0x18/+0x1c auipc/addi a2. a2 is 0x170a1 in the donor and 0x16f60 in the target, and the bytes there are "%s\0" on both sides. Then +0x20 `mv a1, s0` (size), then +0x24 `jal` internal_snprintf (donor 0x66ffc, target 0x65c34), then `sltu a0, a0, s0`.
  - The field is the first and only variadic argument (a3) of format "%s", which has no width and no precision. The object pointer does not go to the callee.
- internal_snprintf "%s" in the binary:
  - internal_snprintf only stores a3..a7 to the stack and calls VSNPrintf (donor 0x66940, target 0x65578).
  - In VSNPrintf, precision starts as -1 (+0x10c `addi a2, zero, -1`) and is set only by the ".*" form (+0x110..+0x128). The conversion jump table entry for 's' is at the table formed at +0x1bc/+0x1c0 (donor 0x20b9c, target 0x209bc), and it goes to +0x1fc on both sides.
  - The 's' path loads the pointer from va_arg (+0x230). If the pointer is NULL it uses "<null>" (+0x218); the place is not NULL on either side. The path then reads bytes with `lbu` and stops at the first zero byte (+0x238 `beqz`). If the output buffer becomes full, it keeps reading up to the NUL to count (+0x2b8..+0x2c8).
  - For "", it reads the NUL byte only and writes nothing.
- The handler pointer's escape:
  - In RegisterCommonFlags, the object pointer goes only to RegisterHandler. RegisterHandler (donor 0x637cc, target 0x62404) stores it only at flags_[n].handler: +0x10 `ld a5, 0(a0)`, then +0x30 `23b8c700 sd a2, 0x10(a5)`. Its CHECK path overwrites a2 before calling CheckFailed.
  - Of the FlagParser members, only two read flags_ entries at +0x10:
    - parse_flag (+0x25c..+0x274: `ld a0, 0(s0)`; `add`; `ld a0, 0x10(a0)`; `ld a1, 0(a0)`; `ld a2, 0(a1)`; `jalr a2`) makes a slot-0 call, which is Parse.
    - PrintFlagDescriptions (+0xa8..+0xc4: `ld a0, 0(s0)`; `add`; `ld a0, 0x10(a0)`; `ld a1, 0(a0)`; `ld a3, 8(a1)`; a1 = sp+8; a2 = 0x80; `jalr a3`) makes a slot-+8 call, which is Format, with a 128-byte stack buffer. The buffer is filled with 0xaa at +0x48..+0x54. The result goes to Printf "\t%s\n\t\t- %s (Current Value%s: %s)\n" as a4 = sp+8, so the printed value is the copy in the buffer, not the place.
    - ParseString, ParseStringFromEnv and ParseFile read only buf_ (+0x10) and pos_ (+0x18) of the FlagParser itself, with no load of flags_ (+0). The constructor only writes flags_.
    - ReportUnrecognizedFlags does not use flags_.
  - I listed every indirect call in each image whose target comes from `ld rX, 8(rY)`: 16 in the donor and 16 in the target. The only one whose receiver is loaded from +0x10 of a flags_ entry is PrintFlagDescriptions +0xc4. For the others, I traced the receiver or function table back with straight-line def chains. Each chain starts at a global (an auipc-formed address), at the function's own this or argument register, or at a field of another object, never at a flags_ entry. These call sites are in ScopedInErrorReport::~ScopedInErrorReport, RunFreeHooks, MemoryMappingLayout::Next, StackTrace::PrintTo, Symbolizer::SymbolizeData, SymbolizerProcess::SendCommand, MarkupStackTracePrinter::RenderFrame, BufferedStackTrace::UnwindSlow, the LSan CheckForLeaksCallback (5 sites), __funcs_on_exit and handler.
  - The conclusion does not depend on which caller reaches Format: every path into Format reads field +0x18 only as the "%s" argument, and every path into Parse only writes it.
- Is anything else reading the field? I found no other code that reads field +0x18 of these objects (see the limits below). The pointer value itself is compared only with NULL (in VSNPrintf), and it is non-NULL on both sides.
- Source cross-check, used only as a cross-check: the current upstream llvm-project files compiler-rt/lib/sanitizer_common/sanitizer_flags.cpp, sanitizer_flag_parser.cpp and sanitizer_flag_parser.h. They define FlagHandlerInclude(parser, ignore_missing) with original_path_(""), a Parse that assigns original_path_ = value first, and a Format that returns FormatString(buffer, size, original_path_). FormatString (in sanitizer_flag_parser.h) is internal_snprintf(buffer, size, "%s", str_to_use) < size. PrintFlagDescriptions calls flags_[i].handler->Format(buffer, 128). RegisterIncludeFlags is inlined at the end of RegisterCommonFlags. I did not identify the LLVM version of the images, but the binary structure agrees with this source.

Check 4: the two images run the same code on this path. Result: PASS.
- I compared these functions instruction by instruction: RegisterCommonFlags (1193 instructions), RegisterIncludeFlags, FlagParser::RegisterHandler, parse_flag, PrintFlagDescriptions, FlagHandlerInclude::Parse and Format, internal_snprintf and VSNPrintf (366).
- auipc-formed addresses are normalized, and direct call targets are compared by symbol name. There are 0 differences in each function.
- The strings formed beside the place are the same on both sides: "include", "read more options from the given file", "include_if_exists", "read more options from the given file (if it exists)" and "%s".

Check 5: the wording of records/settle-sm1.out. Result: the conclusion is accurate, with three wording errors.
- Accurate: the place lines (addresses, .rodata, b'\x00', 1 byte, read from PT_LOAD file bytes, because the script's rd() reads only within p_filesz), the vtable register lines, the two "READ of s2: stored to field 0x18" lines, the vtable entries, the Parse "WRITE of field +0x18" line, the Format line (field in a3, format b'%s\x00'), and the final "the same C string" and VERDICT lines.
- Error 1: the line "RegisterCommonFlags from +0x121c to its end:" is wrong. The listing (and the script's branch check) stops at +0x1288, where s2 is restored. The function continues to +0x12a0: restores of s3..s6, `addi sp, sp, 0x40`, and the tail jump to RegisterHandler that registers the second object. I checked +0x128c..+0x12a0: it has no use of s2 and no branch other than that tail jump.
- Error 2: for Parse, the line "(registers holding the object pointer somewhere in the method: ['a0', 'a1', 's0', 's1', 's2'])" is wrong as worded. It is a flow-insensitive over-approximation: only a0 and s0 hold the object, and a1/s1 (value) and s2 (buffer) do not. The over-approximation is conservative for finding accesses to +0x18, so the result does not change.
- Error 3: the VERDICT phrase "the one consumer reads it only as the "%s" argument of internal_snprintf" is true, but the record alone does not show it. The record does not show:
  - who calls Format (only PrintFlagDescriptions, through vtable slot +8);
  - that nothing outside Parse and Format reads field +0x18 (the handler pointer escapes only into the flags_ table);
  - that the binary's VSNPrintf "%s" path reads up to the NUL with no precision.
  This review supplies those facts (check 3).
- The script and the record reproduce: I ran `python3 gates/settle-sm1.py <donor twin> <target twin>` and got exit status 0, and its output plus "rc=0" is byte-identical to records/settle-sm1.out (8105 bytes).

Things I could not check, or did not check
- I did not re-run the comparison kit (strictcmp2 4bbd3a74be89). I took its finding (one data-differs at +0x1218, regions 51389 / 51165 bytes, first difference at offset 4241) from records/cmpkit-4bbd3a74be89-region.out and the RegisterCommonFlags row of records/cmpkit-4bbd3a74be89-pairs.out.
- The escape analysis in check 3 is a reading of the disassembly, not a machine points-to proof. I did not prove that no code outside the FlagParser members reads FlagParser+0 (flags_). The verdict would change only if such code loaded a handler from flags_ and then read +0x18 of that handler directly, outside Parse and Format. In the source, flags_ is private to FlagParser and original_path_ is private to FlagHandlerInclude. I found no such load among the FlagParser members. Any call through the vtable reaches only Parse (which only writes the field) or Format (which reads it only as "%s").
- Code that reads memory words as integers, for example a leak checker that scans root regions for heap pointers, can see the stored pointer value (0x13f5f / 0x13e5f). That is a read of the address value, not of the string. I did not analyze it further. Neither value points into a heap chunk.
