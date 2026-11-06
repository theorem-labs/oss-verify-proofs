# Donor compare of five runtime functions: fuzz_grant.asan vs fuzz_transport.asan (new pin e89be137db17)

Kit of record: cmpkit 86da41d3ef68 (the tool registry's tools/cmpkit/86da41d3ef68/, SHA256SUMS checked OK).
A = fuzz_grant.asan unstripped twin, sha256 57c26f993615 (its pin c2c7559b29bd). B = fuzz_transport.asan unstripped
twin, sha256 86efc3a80314 (its pin e89be137db17; the twin's PT_LOAD bytes equal the pin's except the ELF header and the
build-id note at 0x10028-0x102cb, the same difference the old pin pair 29ec57e03c5d has).

Commands (from a fresh copy of the kit directory):

    python3 strictcmp3.py cmp <F> A=<grant twin> B=<transport twin> A:B   > strictcmp3-five.txt
    python3 jtcheck.py <grant twin> <transport twin> <F>                   > jtcheck-five.txt

F = MaybeReleaseToOS (`_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16MaybeReleaseToOSEPNS_12MemoryMapperIS5_EEmb`),
`_ZN11__sanitizer9VSNPrintfEPciPKcPv`, `_ZN6__asan9Decorator10ShadowByteEh`,
`_ZNK11__sanitizer13SignalContext8DescribeEv`, `__strftime_fmt_1`.

| function | A | B | size | strictcmp3 | jtcheck | open rows and their hand argument |
|---|---|---|---|---|---|---|
| MaybeReleaseToOS | 0x34850 | 0x35144 | 492 = 492 | DIFFERENT-target (13 pcrel, 0 real) | one table-free function: 1 `lui-in-section`, 1 unmeasured `.rodata` region | +0xd8/+0xdc `lui a3,0xf4; addiw a3,a3,0x240` = 1000000 in both; its only use is `mul a1,a1,a3` at +0xe0 (interval in ms times 10^6, to ns), so it is a number, not an address (same bytes, same dataflow in A and B) |
| VSNPrintf | 0x66940 | 0x674f4 | 1464 = 1464 | DIFFERENT-target (35 pcrel; 18 C-string acceptances) | the table at +0x1c0 is `unmeasured` (extent unknown to jtcheck) | MEASURED by hand: `auipc t4 / addi t4` at +0x1bc/+0x1c0 gives the table base (A 0x20b9c, B 0x20ce0); `lw t3,0(t3); add t3,t3,t4; jr t3` makes each 4-byte entry relative to that base (rel4-jump); the first 33 entries resolve to the SAME function offsets in A and B (0x1d4, 0x594 x10, 0x330, ...), entry 34 leaves the function in both |
| Decorator::ShadowByte | 0x55190 | 0x55d44 | 160 = 160 | DIFFERENT-target | ACCEPT table +0x14 rel4-jump 83 entries | none |
| SignalContext::Describe | 0x666f8 | 0x672ac | 60 = 60 | DIFFERENT-target | ACCEPT table +0x1c rel4-str 8 entries | none |
| __strftime_fmt_1 | 0x9a400 | 0xa1be4 | 1572 = 1572 | DIFFERENT-target (49 pcrel; 16 C-string acceptances) | ACCEPT table +0x44 rel4-jump 86 entries; 7 `lui-in-section`; 2 unmeasured `.rodata` regions | The 7 rows build 0x20000 + k with `lui rX,0x20` + `addi(w)` (equal in A and B). Followed by hand (RISC-V `j` / `jal` offsets are pc-relative): +0x148 (k = 0x2a) and +0x254 (k = 0x2b) jump to +0x470, where `mv a0,a1; ... jal nl_langinfo_l` (A 0x98864, B 0xa0048) passes the value as the item; +0xf0 and +0x4e8 / +0x4fc add it to a tm field (`add` / `addw`, which kit dataflow does not follow) and the sum reaches `jal nl_langinfo_l` at +0x480 / +0x508 as a0. These are musl's LC_TIME item codes (`2 << 16 \| n`: DAY_1 = 0x20007, D_T_FMT = 0x20028, T_FMT = 0x2002a, T_FMT_AMPM = 0x2002b), numbers. +0x60 (k = 0x28 = D_T_FMT) sets a1 just before the `jr t2` dispatch: `strftime_a1_trace.py` follows a1 from each of the 86 table entries (37 distinct targets) through both arms of every branch: 30 cases write a1 before any read, 52 reach `ret` with a1 unread, 3 reach a call whose callee takes one argument (week_num, __tm_to_tzname, __tm_to_secs), and the one read is +0x470 `mv a0,a1` before `jal nl_langinfo_l` (the item argument); a1 is never used as a memory address. The bytes +0x5c..+0x68 are equal in A and B (`lui t1,0x20; add t2,a1,t0; addiw a1,t1,40; jr t2`). +0x530 / +0x54c: `auipc a0 / addi a0` give A 0x13f5f, B 0x13f18; both hold the empty string (one NUL byte), read by pyelftools from the two images, so they are C-string pointers to equal strings |

Result: the five functions are the same code up to pc-relative displacements and their switch tables; every differing
table is a jump or string table whose entries jtcheck pairs (ACCEPT) or whose words differ only by the code shift; every
`lui-in-section` row is a number by its dataflow (above). MemToShadow is not among the five, so no by-name shadow compare
is used.


Closed 2026-10-30 (the image-A core's writer): the two OPEN rows of __strftime_fmt_1 above. Script: `python3 strftime_a1_trace.py strftime-neutral-oldpin.s <fuzz_transport.asan image>`; the excerpt is neutral_dis.py's output for __strftime_fmt_1 from the old-pin listing (29ec57e03c5d): same address 0xa1be4 and the same instruction words as the new pin e89be137db17 except 7 halfwords (+0x1aa, +0x2c6, +0x4c2, +0x516, +0x5c6, +0x5de, +0x5ea: pc-relative string and call offsets); the 86-entry table at 0x229f4 is byte-equal in the two pins.
