# Independent read of two libunwind jump tables: WIRE_B_TWIN against GRANT_B_TWIN

Images: X = WIRE_B_TWIN (sha256 `51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3`), Y = GRANT_B_TWIN (sha256 `5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417`). The reader computed both sha256 values and they match images.sha256. The functions are libunwind's `CFI_Parser<LocalAddressSpace>` (released source tag llvmorg-20.1.8; the `.comment` section of both images names clang 20.1.8 and LLD 20.1.8): `parseCIE` = `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEERS1_mPNS2_8CIE_InfoE` and `parseFDEInstructions` = `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDEInstructionsERS1_RKNS2_8FDE_InfoERKNS2_8CIE_InfoEmiPNS2_10PrologInfoE`. Offsets are from the function's `.symtab` start; addresses are virtual addresses inside the image.

## Method

The reader used its own decoder, not tools/handtable.py: capstone 5.0.7 (RV64, compressed mode on) for the instruction text, and a separate bit-field decoder for branch and jump displacements, destination registers, `auipc`/`addi` immediates and the `slli` shift. The two decoders agree on every branch and `jal` displacement in the four function bodies. Every instruction in the four bodies is 32 bits wide. Function bounds come from `.symtab` (`st_value`, `st_size`). The control-flow graph has one node per instruction: a conditional branch goes to its target and to the next word; `jal zero` goes to its target; `jal ra` (a call) goes to the next word; `ret` exits; the one `jr` in each function goes to every target of its table, so the jump-table arms are in the graph. A call to a no-return function (`__assert_fail`) is kept as a call that returns, which can only add paths; the one fall-through past the end of each body (after its last word, a call to `__assert_fail`) leaves the function and is not followed. The table base is the `auipc` address plus its upper immediate plus the `addi` immediate; the entry size is 4 (`slli` by 2, then `lw`); a target is the base plus the sign-extended 32-bit entry. The entry count is the bound plus one, because the guard is `bltu bound, index`: it branches away when the index is above the bound (unsigned) and falls through when the index is 0 to bound. 'Reaching' is a classic reaching-definitions data flow, run to a fixed point over that graph from the function entry, with an ENTRY pseudo-definition for the value the caller passes in; it covers every path, every loop and every path back through the arms. Calling-convention assumption (RISC-V LP64 psABI): a call keeps `sp` and `s0`–`s11` and can change `ra`, `t0`–`t6` and `a0`–`a7`. 'Only way into the dispatch' means: no edge of the graph (branch, jump, table target or fall-through) enters any word after the guard up to the `jr`, except the guard's fall-through and the fall-through from one dispatch word to the next.

## parseCIE, table base at +0x23c

**Verdict: CONFIRMED.** X has 47 entries, Y has 47; every slot has the same target by symbol and offset; one definition of the bound reaches the guard in each image; the guard's fall-through is the only way into the dispatch in each image.

- Function start: X `0x82488`, Y `0x87170`; size `0x390` in both.
- Guard: +0x258 `63ecba08` `bltu s5, a1` (taken to +0x2f0), the same word in X and Y. Compared registers: bound `s5`, index `a1`.
- Dispatch words (offset, X word, Y word):

| offset | X | Y |
|---|---|---|
| +0x238 | `17e5f9ff` `auipc a0, 0xfff9e` | `17a5f9ff` `auipc a0, 0xfff9a` |
| +0x23c | `130b455d` `addi s6, a0, 0x5d4` | `130b05ff` `addi s6, a0, -0x10` |
| +0x25c | `93952500` `slli a1, a1, 2` | `93952500` `slli a1, a1, 2` |
| +0x260 | `b3856501` `add a1, a1, s6` | `b3856501` `add a1, a1, s6` |
| +0x264 | `03a50500` `lw a0, 0(a1)` | `03a50500` `lw a0, 0(a1)` |
| +0x268 | `33056501` `add a0, a0, s6` | `33056501` `add a0, a0, s6` |
| +0x26c | `67000500` `jr a0` | `67000500` `jr a0` |

  Only the `auipc`/`addi` base pair differs between X and Y (it is PC-relative). Table base: X `0x20c94`, Y `0x21398`, both in the read-only, non-executable first PT_LOAD. Entry size: 4 bytes, signed, relative to the base.
- Every write to `s5` in the body (X and Y have the same words at the same offsets): +0x134 `lbu s5, 4(s4)`, +0x234 `addi s5, zero, 0x2e`, +0x324 `ld s5, 0x18(sp)`.
- Definitions of `s5` that reach the guard: X {+0x234}, Y {+0x234}: `addi s5, zero, 0x2e` = 46, so 47 entries. The incoming (ENTRY) value does not reach. The other writes do not reach.
- Index `a1`: one reaching definition, +0x254 `addi a1, a0, -0x4c` (X and Y). Base `s6`: one reaching definition at both `add` words, +0x23c (X and Y).
- Edges into +0x25c..+0x26c other than the fall-throughs: none in X, none in Y. No table target lands in that range. Distinct targets: 6 in X, 6 in Y.

| slot | case value | X word | X target | Y word | Y target | same? |
|---|---|---|---|---|---|---|
| 0 | 0x4c ('L') | `0x00061a64` | parseCIE+0x270 | `0x00066048` | parseCIE+0x270 | yes |
| 1 | 0x4d ('M') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 2 | 0x4e ('N') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 3 | 0x4f ('O') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 4 | 0x50 ('P') | `0x00061aa8` | parseCIE+0x2b4 | `0x0006608c` | parseCIE+0x2b4 | yes |
| 5 | 0x51 ('Q') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 6 | 0x52 ('R') | `0x00061a8c` | parseCIE+0x298 | `0x00066070` | parseCIE+0x298 | yes |
| 7 | 0x53 ('S') | `0x00061a3c` | parseCIE+0x248 | `0x00066020` | parseCIE+0x248 | yes |
| 8 | 0x54 ('T') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 9 | 0x55 ('U') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 10 | 0x56 ('V') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 11 | 0x57 ('W') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 12 | 0x58 ('X') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 13 | 0x59 ('Y') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 14 | 0x5a ('Z') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 15 | 0x5b | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 16 | 0x5c | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 17 | 0x5d | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 18 | 0x5e | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 19 | 0x5f | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 20 | 0x60 | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 21 | 0x61 ('a') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 22 | 0x62 ('b') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 23 | 0x63 ('c') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 24 | 0x64 ('d') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 25 | 0x65 ('e') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 26 | 0x66 ('f') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 27 | 0x67 ('g') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 28 | 0x68 ('h') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 29 | 0x69 ('i') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 30 | 0x6a ('j') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 31 | 0x6b ('k') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 32 | 0x6c ('l') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 33 | 0x6d ('m') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 34 | 0x6e ('n') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 35 | 0x6f ('o') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 36 | 0x70 ('p') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 37 | 0x71 ('q') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 38 | 0x72 ('r') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 39 | 0x73 ('s') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 40 | 0x74 ('t') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 41 | 0x75 ('u') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 42 | 0x76 ('v') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 43 | 0x77 ('w') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 44 | 0x78 ('x') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 45 | 0x79 ('y') | `0x00061a40` | parseCIE+0x24c | `0x00066024` | parseCIE+0x24c | yes |
| 46 | 0x7a ('z') | `0x00061a80` | parseCIE+0x28c | `0x00066064` | parseCIE+0x28c | yes |

## parseFDEInstructions, table base at +0x140

**Verdict: CONFIRMED.** X has 48 entries, Y has 48; every slot has the same target by symbol and offset; one definition of the bound reaches the guard in each image; the guard's fall-through is the only way into the dispatch in each image.

- Function start: X `0x83c18`, Y `0x88900`; size `0x1504` in both.
- Guard: +0x134 `e3e09427` `bltu s1, s9` (taken to +0xb94), the same word in X and Y. Compared registers: bound `s1`, index `s9`.
- Dispatch words (offset, X word, Y word):

| offset | X | Y |
|---|---|---|
| +0x138 | `93952c00` `slli a1, s9, 2` | `93952c00` `slli a1, s9, 2` |
| +0x13c | `17d6f9ff` `auipc a2, 0xfff9d` | `1796f9ff` `auipc a2, 0xfff99` |
| +0x140 | `1306c6ff` `addi a2, a2, -4` | `130686a1` `addi a2, a2, -0x5e8` |
| +0x144 | `b385c500` `add a1, a1, a2` | `b385c500` `add a1, a1, a2` |
| +0x148 | `83a50500` `lw a1, 0(a1)` | `83a50500` `lw a1, 0(a1)` |
| +0x14c | `b385c500` `add a1, a1, a2` | `b385c500` `add a1, a1, a2` |
| +0x150 | `67800500` `jr a1` | `67800500` `jr a1` |

  Only the `auipc`/`addi` base pair differs between X and Y (it is PC-relative). Table base: X `0x20d50`, Y `0x21454`, both in the read-only, non-executable first PT_LOAD. Entry size: 4 bytes, signed, relative to the base.
- Every write to `s1` in the body (X and Y have the same words at the same offsets): +0xd0 `addi s1, zero, 0x2f`, +0x12a8 `ld s1, -0x4f0(s0)`, +0x138c `ld s1, -0x4f0(s0)`, +0x13b0 `ld s1, 0x4f8(sp)`, +0x13fc `ld s1, -0x4f0(s0)`, +0x142c `ld s1, -0x4f0(s0)`, +0x145c `ld s1, -0x4f0(s0)`, +0x148c `ld s1, -0x4f0(s0)`.
- Definitions of `s1` that reach the guard: X {+0xd0}, Y {+0xd0}: `addi s1, zero, 0x2f` = 47, so 48 entries. The incoming (ENTRY) value does not reach. The other writes do not reach.
- Index `s9`: one reaching definition, +0x128 `lbu s9, 0(s8)` (X and Y). Base `a2`: one reaching definition at both `add` words, +0x140 (X and Y).
- Edges into +0x138..+0x150 other than the fall-throughs: none in X, none in Y. No table target lands in that range. Distinct targets: 26 in X, 26 in Y.

| slot | case value | X word | X target | Y word | Y target | same? |
|---|---|---|---|---|---|---|
| 0 | 0x00 | `0x0006301c` | parseFDEInstructions+0x154 | `0x00067600` | parseFDEInstructions+0x154 | yes |
| 1 | 0x01 | `0x0006357c` | parseFDEInstructions+0x6b4 | `0x00067b60` | parseFDEInstructions+0x6b4 | yes |
| 2 | 0x02 | `0x00063278` | parseFDEInstructions+0x3b0 | `0x0006785c` | parseFDEInstructions+0x3b0 | yes |
| 3 | 0x03 | `0x00063538` | parseFDEInstructions+0x670 | `0x00067b1c` | parseFDEInstructions+0x670 | yes |
| 4 | 0x04 | `0x000632b0` | parseFDEInstructions+0x3e8 | `0x00067894` | parseFDEInstructions+0x3e8 | yes |
| 5 | 0x05 | `0x0006347c` | parseFDEInstructions+0x5b4 | `0x00067a60` | parseFDEInstructions+0x5b4 | yes |
| 6 | 0x06 | `0x00063638` | parseFDEInstructions+0x770 | `0x00067c1c` | parseFDEInstructions+0x770 | yes |
| 7 | 0x07 | `0x00063694` | parseFDEInstructions+0x7cc | `0x00067c78` | parseFDEInstructions+0x7cc | yes |
| 8 | 0x08 | `0x000637f4` | parseFDEInstructions+0x92c | `0x00067dd8` | parseFDEInstructions+0x92c | yes |
| 9 | 0x09 | `0x00063770` | parseFDEInstructions+0x8a8 | `0x00067d54` | parseFDEInstructions+0x8a8 | yes |
| 10 | 0x0a | `0x00063238` | parseFDEInstructions+0x370 | `0x0006781c` | parseFDEInstructions+0x370 | yes |
| 11 | 0x0b | `0x00063500` | parseFDEInstructions+0x638 | `0x00067ae4` | parseFDEInstructions+0x638 | yes |
| 12 | 0x0c | `0x000633a8` | parseFDEInstructions+0x4e0 | `0x0006798c` | parseFDEInstructions+0x4e0 | yes |
| 13 | 0x0d | `0x000631d4` | parseFDEInstructions+0x30c | `0x000677b8` | parseFDEInstructions+0x30c | yes |
| 14 | 0x0e | `0x00063700` | parseFDEInstructions+0x838 | `0x00067ce4` | parseFDEInstructions+0x838 | yes |
| 15 | 0x0f | `0x0006372c` | parseFDEInstructions+0x864 | `0x00067d10` | parseFDEInstructions+0x864 | yes |
| 16 | 0x10 | `0x00063940` | parseFDEInstructions+0xa78 | `0x00067f24` | parseFDEInstructions+0xa78 | yes |
| 17 | 0x11 | `0x0006385c` | parseFDEInstructions+0x994 | `0x00067e40` | parseFDEInstructions+0x994 | yes |
| 18 | 0x12 | `0x00063034` | parseFDEInstructions+0x16c | `0x00067618` | parseFDEInstructions+0x16c | yes |
| 19 | 0x13 | `0x000633f0` | parseFDEInstructions+0x528 | `0x000679d4` | parseFDEInstructions+0x528 | yes |
| 20 | 0x14 | `0x000639d8` | parseFDEInstructions+0xb10 | `0x00067fbc` | parseFDEInstructions+0xb10 | yes |
| 21 | 0x15 | `0x000630e8` | parseFDEInstructions+0x220 | `0x000676cc` | parseFDEInstructions+0x220 | yes |
| 22 | 0x16 | `0x0006330c` | parseFDEInstructions+0x444 | `0x000678f0` | parseFDEInstructions+0x444 | yes |
| 23 | 0x17 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 24 | 0x18 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 25 | 0x19 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 26 | 0x1a | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 27 | 0x1b | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 28 | 0x1c | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 29 | 0x1d | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 30 | 0x1e | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 31 | 0x1f | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 32 | 0x20 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 33 | 0x21 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 34 | 0x22 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 35 | 0x23 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 36 | 0x24 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 37 | 0x25 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 38 | 0x26 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 39 | 0x27 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 40 | 0x28 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 41 | 0x29 | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 42 | 0x2a | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 43 | 0x2b | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 44 | 0x2c | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 45 | 0x2d | `0x00063a5c` | parseFDEInstructions+0xb94 | `0x00068040` | parseFDEInstructions+0xb94 | yes |
| 46 | 0x2e | `0x0006320c` | parseFDEInstructions+0x344 | `0x000677f0` | parseFDEInstructions+0x344 | yes |
| 47 | 0x2f | `0x000635b0` | parseFDEInstructions+0x6e8 | `0x00067b94` | parseFDEInstructions+0x6e8 | yes |

Reader: independent of the writer of this record; it did not run tools/handtable.py.
