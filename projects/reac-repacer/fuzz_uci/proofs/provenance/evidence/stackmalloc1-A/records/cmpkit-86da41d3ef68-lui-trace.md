# cmpkit 86da41d3ef68 rule 8: every lui of the 13 compared functions, traced by hand

Why: luiscan 9ae61e4a0e01 (records/cmpkit-86da41d3ef68-luiscan.out) cleared every lui row of this record on `memfed 0`
and the section test. In both images every row has insec 0, memfed 0, luiconst 0, exposure 0; TryAsanInitFromRtl's
value 0x10000 lies in the first PT_LOAD (the ELF header) but in no section (`inload 1`). The tool set's README at commit
6d8ff128a01 records a known limit of cmpkit 86da41d3ef68: rule 8's dataflow follows a lui value through addi / ld / sd /
jalr only, not through add / sub / sh*add, so `memfed 0` is not proof that the value never reaches an address. This file
traces each lui by hand.

Images: G = fuzz_grant.asan unstripped twin 57c26f993615 (donor), U = fuzz_uci.asan unstripped twin 56822e263d76 (target).

Method: each function's file bytes, decoded with capstone 5.0.7 (RV64, compressed decoding on). No function of the 13
holds a 2-byte parcel in either image, so there is no c.lui; every lui is a 4-byte word, and per function the count
equals luiscan's `luis` column (stack_malloc 1, TryAsanInitFromRtl 2, DTLS_on_tls_get_addr 2, FakeStack::GC 1,
AsyncSignalSafeLazyInitFakeStack 4; the other 8 functions have none). For each lui: every instruction, on every path,
that reads its register, or a register computed from it by ANY instruction (add / sub / sh*add / addi / shifts / logic /
mul), or a stack slot it was stored to, up to the next write of each such register; a register passed to a call is
followed into the call's argument list and its return. Each pc-relative target (auipc + lo12, jal) is computed from the
words and named by .symtab in each image. Listing columns: offset, address in G, address in U, the word (one word when G
and U hold the same word there), the text, and the targets (G ; U). Every word that differs between G and U is an
auipc, its lo12 partner or a jal, which the kit compared.

Ops followed (the tool set's README at commit 797c750bbb0: a `lui-const (dataflow)` settlement is not evidence when the lui register feeds a register-register or logical op): every instruction that reads a traced register and writes a register was followed to that register's next write, namely every register-register op (OP / OP-32: add, sub, sh1add / sh2add / sh3add, sll, srl, sra, slt, sltu, and, or, xor, mul and the other M ops, and the *w forms incl. negw) and every register-immediate op (OP-IMM / OP-IMM-32: addi incl. mv, andi, ori, xori incl. not, slti, sltiu, slli, srli, srai, addiw incl. sext.w, slliw, srliw, sraiw), plus loads / stores (base and data), branches, AMO / LR / SC, calls (arguments, return) and sp-relative spills / reloads; no traced value enters an FP register or a CSR. The logical ops a lui value passes are TryAsanInitFromRtl +0x4c / +0x50 / +0x54 (xor, and, xor: into the sc.w data) and AsyncSignalSafeLazyInitFakeStack +0x124 / +0x12c / +0x134 / +0x144 / +0x160 / +0x18c (and, and, and, and, xori, and: into the table index 0..63), both traced below; insec is 0 for every row in both images, so no row of this record is `lui-const (dataflow)`. No row changes.

## Result: 10 lui per image, none forms a static address, no verdict changes

| function (G / U) | lui | value | what the code does with it | address it reaches | the address's base, both images |
|---|---|---|---|---|---|
| __asan_stack_malloc_1 (G 0x3cf18 / U 0x3c1b8) | +0x58 `lui a3, 1` | 0x1000 | added to the FakeStack pointer s1 | loads / stores at s1 + 0x1000 + runtime terms; the frame's stores; MemToShadow(frame) | the value of TLS `_ZN6__asanL14fake_stack_tlsE` (tls_index G 0x9d550 / U 0x97d00) or the same-named callees' result: runtime, same |
| TryAsanInitFromRtl (G 0x5980c / U 0x58444) | +0x38 `lui a1, 0xff0` | 0xff0000 | the byte-2 mask in the data of `sc.w` | none | (the sc.w address is asan_inited+0, G 0xa5818 / U 0x9fcd8, not lui-derived) |
| | +0x40 `lui a2, 0x10` | 0x10000 | the byte value 1 in byte 2, the data of `sc.w` | none | as above |
| DTLS_on_tls_get_addr (G 0x69720 / U 0x68358) | +0x94 `lui s7, 1` + `addiw -8` | 0xff8 | the size argument of MmapOrDie (+0xa8) and UnmapOrDie (+0xf8) | none | - |
| | +0x128 `lui s8, 1` + `addiw -8` | 0xff8 | the size argument of MmapOrDie (+0x178) and UnmapOrDie (+0x1bc) | none | - |
| FakeStack::GC (G 0x3c958 / U 0x3bd6c) | +0x6c `lui s0, 1` | 0x1000 | added to `this` (a0 at entry) | flag loads / stores, the frame's +0x18 load, the shadow stores, PoisonShadow's argument | `this` (runtime) and the value of `__asan_shadow_memory_dynamic_address` (.got G 0x9c870 / U 0x97020): same |
| AsyncSignalSafeLazyInitFakeStack (G 0x5c280 / U 0x5aeb8) | +0xb0 `lui a2, 0x55555` | 0x5555555555555555 | popcount masks (lui + addiw + slli 32 + add) of the leading-zero count of the stack size | only the index 0..63 of +0x1a4 `lbu`, at T + index | T: unnamed .rodata G 0x20b1a / U 0x2093a, a 64-byte region in both, bytes equal |
| | +0xb4 `lui a4, 0x33333` | 0x3333333333333333 | as above | as above | as above |
| | +0xb8 `lui a5, 0xf0f1` | 0x0f0f0f0f0f0f0f0f | as above | as above | as above |
| | +0xbc `lui a6, 0x1010` | 0x0101010101010101 | as above | as above | as above |

Every lui word and every word that carries its value is the same word at the same offset in G and U. Where a value
reaches an address, the address is a runtime base plus displacements, and the base is the same object in both images
(the same TLS symbol, the same `this`, the same .got-named variable), or (LazyInit) a bounded index into a table whose
64 bytes are equal. The kit's verdicts for these functions stand.

### 1. __asan_stack_malloc_1 (G 0x3cf18 / U 0x3c1b8): `lui a3, 1` at +0x58, value 0x1000

The register it is added to, s1, holds the thread's FakeStack pointer: +0x24 `ld s1, 0(a0)`, a0 being what
__tls_get_addr returns for the tls_index cell formed at +0x18 / +0x1c (G 0x9d550 / U 0x97d00 in .got: module 1, offset -0x800, i.e.
`_ZN6__asanL14fake_stack_tlsE`+0 in both images); or, on the way back from +0x188, s1 = the field at +0x48 of the
AsanThread GetCurrentThread returns (+0x174) or the return value of AsyncSignalSafeLazyInitFakeStack (+0x184), the same
callees by name in both images. s2 = the word at s1+0x58 (+0x30), a1 = s2 - 7 (+0x44).

Every use, up to the next write:
- +0x78 `add a1, s1, a3`: a1 = s1 + 0x1000 (a3 itself is next read at +0x7c and written at +0x114).
- +0x7c `add a3, a1, a4`: a3 = s1 + 0x1000 + (0x200 << (s2 - 15)) (a4 from +0x60 / +0x68, before +0x80 rewrites a4).
- +0x98 `add a5, a3, a7`, a7 = a2 & a4 (+0x94; a2 = the word at s1+8 plus the loop count, a4 = (1 << (s2 - 7)) - 1):
  +0x9c `lbu t0, 0(a5)` LOAD and +0x120 `sb a0, 0(a5)` STORE at s1 + 0x1000 + (0x200 << (s2 - 15)) + (a2 & a4).
- +0x12c `add a1, a1, a2` (a2 = 1 << (s2 - 5), +0x124) and +0x134 `add s1, a1, a0` (a0 = (1 << s2) + (a7 << 7), +0x128 /
  +0x130): s1 = s1_old + 0x1000 + (1 << (s2 - 5)) + (1 << s2) + ((a2 & a4) << 7), a frame address.
  +0x138 `sd s0, 0x18(s1)` and +0x13c `sd a5, 0x78(s1)` STORE at frame + 0x18 / + 0x78 (the data of +0x13c is a5, the
  flag address above; the data of +0x138 is s0 = sp + 0x20).
- +0x140 `mv a0, s1`, +0x144 `jal` MemToShadow (G 0x3d410 / U 0x3c348, the asan_fake_stack.cpp copy, kit EQUAL by address):
  argument = the frame; its return a1 (+0x148) is the base of +0x154 / +0x158 `sd zero, 0(a1)` / `8(a1)`, so these two
  STORES are at MemToShadow(frame), computed in the callee from the frame.
- +0x14c `mv a0, s1`, +0x170 `ret`: the return value is the frame.
- The path +0xb0 -> +0xf4 returns a0 = 0 (the loop count); a1 (s1 + 0x1000), a3 and a5 are left over and not read
  (the function returns one value, in a0). s1 is restored at +0xfc / +0x164; nothing else reads a derived register.

Full address in both images: (value of TLS `_ZN6__asanL14fake_stack_tlsE`, or the same callee's result) + 0x1000 + terms
of s2, the hint word and the slot, all runtime. No static address is formed. The words at +0x58 to +0x170 are equal in
G and U; only the auipc / addi / jal words at +0x18 / +0x1c / +0x20 / +0x40 / +0xb8 / +0xbc / +0xc8 / +0x144 / +0x180
differ, and their targets are named the same above.

```
+off   G        U        word(s)            text                               target(s)
+0x018  0x3cf30  0x3c1d0  00060517|0005c517  auipc a0, 0x60 | auipc a0, 0x5c    auipc value 0x9cf30 ; auipc value 0x981d0
+0x01c  0x3cf34  0x3c1d4  62050513|b3050513  addi a0, a0, 0x620 | addi a0, a0, -0x4d0 pcrel -> 0x9d550 = no symbol [.got] ; pcrel -> 0x97d00 = no symbol [.got]
+0x020  0x3cf38  0x3c1d8  254050ef|6e9040ef  jal 0x5254 | jal 0x4ee8            -> 0x4218c __wrap___tls_get_addr+0x0 [.text] ; -> 0x410c0 __wrap___tls_get_addr+0x0 [.text]
+0x024  0x3cf3c  0x3c1dc  00053483           ld s1, 0(a0)
+0x028  0x3cf40  0x3c1e0  08048863           beqz s1, 0x90                      -> +0xb8
+0x02c  0x3cf44  0x3c1e4  0604c503           lbu a0, 0x60(s1)
+0x030  0x3cf48  0x3c1e8  0584b903           ld s2, 0x58(s1)
+0x044  0x3cf5c  0x3c1fc  ff990593           addi a1, s2, -7
+0x048  0x3cf60  0x3c200  00100513           addi a0, zero, 1
+0x04c  0x3cf64  0x3c204  00b51533           sll a0, a0, a1
+0x050  0x3cf68  0x3c208  0005061b           sext.w a2, a0
+0x054  0x3cf6c  0x3c20c  08c05263           blez a2, 0x84                      -> +0xd8
+0x058  0x3cf70  0x3c210  000016b7           lui a3, 1
+0x05c  0x3cf74  0x3c214  ff190613           addi a2, s2, -0xf
+0x060  0x3cf78  0x3c218  20000713           addi a4, zero, 0x200
+0x064  0x3cf7c  0x3c21c  fff00793           addi a5, zero, -1
+0x068  0x3cf80  0x3c220  00c71733           sll a4, a4, a2
+0x06c  0x3cf84  0x3c224  0084b603           ld a2, 8(s1)
+0x070  0x3cf88  0x3c228  00b797b3           sll a5, a5, a1
+0x074  0x3cf8c  0x3c22c  fff50813           addi a6, a0, -1
+0x078  0x3cf90  0x3c230  00d485b3           add a1, s1, a3
+0x07c  0x3cf94  0x3c234  00e586b3           add a3, a1, a4
+0x080  0x3cf98  0x3c238  fff7c713           not a4, a5
+0x084  0x3cf9c  0x3c23c  02081813           slli a6, a6, 0x20
+0x088  0x3cfa0  0x3c240  02085793           srli a5, a6, 0x20
+0x08c  0x3cfa4  0x3c244  00f607b3           add a5, a2, a5
+0x090  0x3cfa8  0x3c248  00178813           addi a6, a5, 1
+0x094  0x3cfac  0x3c24c  00e678b3           and a7, a2, a4
+0x098  0x3cfb0  0x3c250  011687b3           add a5, a3, a7
+0x09c  0x3cfb4  0x3c254  0007c283           lbu t0, 0(a5)
+0x0a0  0x3cfb8  0x3c258  06028663           beqz t0, 0x6c                      -> +0x10c
+0x0a4  0x3cfbc  0x3c25c  fff5051b           addiw a0, a0, -1
+0x0a8  0x3cfc0  0x3c260  00160613           addi a2, a2, 1
+0x0ac  0x3cfc4  0x3c264  fe0514e3           bnez a0, -0x18                     -> +0x94
+0x0b0  0x3cfc8  0x3c268  0104b423           sd a6, 8(s1)
+0x0b4  0x3cfcc  0x3c26c  0400006f           j 0x40                             -> +0xf4
+0x0f4  0x3d00c  0x3c2ac  01813083           ld ra, 0x18(sp)
+0x0f8  0x3d010  0x3c2b0  01013403           ld s0, 0x10(sp)
+0x0fc  0x3d014  0x3c2b4  00813483           ld s1, 8(sp)
+0x100  0x3d018  0x3c2b8  00013903           ld s2, 0(sp)
+0x104  0x3d01c  0x3c2bc  02010113           addi sp, sp, 0x20
+0x108  0x3d020  0x3c2c0  00008067           ret
+0x10c  0x3d024  0x3c2c4  00160613           addi a2, a2, 1
+0x110  0x3d028  0x3c2c8  00100513           addi a0, zero, 1
+0x114  0x3d02c  0x3c2cc  ffb90693           addi a3, s2, -5
+0x118  0x3d030  0x3c2d0  00789893           slli a7, a7, 7
+0x11c  0x3d034  0x3c2d4  00c4b423           sd a2, 8(s1)
+0x120  0x3d038  0x3c2d8  00a78023           sb a0, 0(a5)
+0x124  0x3d03c  0x3c2dc  00d51633           sll a2, a0, a3
+0x128  0x3d040  0x3c2e0  01251533           sll a0, a0, s2
+0x12c  0x3d044  0x3c2e4  00c585b3           add a1, a1, a2
+0x130  0x3d048  0x3c2e8  01150533           add a0, a0, a7
+0x134  0x3d04c  0x3c2ec  00a584b3           add s1, a1, a0
+0x138  0x3d050  0x3c2f0  0084bc23           sd s0, 0x18(s1)
+0x13c  0x3d054  0x3c2f4  06f4bc23           sd a5, 0x78(s1)
+0x140  0x3d058  0x3c2f8  00048513           mv a0, s1
+0x144  0x3d05c  0x3c2fc  3b4000ef|04c000ef  jal 0x3b4 | jal 0x4c               -> 0x3d410 _ZN6__asanL11MemToShadowEm+0x0 [.text] ; -> 0x3c348 _ZN6__asanL11MemToShadowEm+0x0 [.text]
+0x148  0x3d060  0x3c300  00050593           mv a1, a0
+0x14c  0x3d064  0x3c304  00048513           mv a0, s1
+0x150  0x3d068  0x3c308  00000613           mv a2, zero
+0x154  0x3d06c  0x3c30c  0005b023           sd zero, 0(a1)
+0x158  0x3d070  0x3c310  0005b423           sd zero, 8(a1)
+0x15c  0x3d074  0x3c314  01813083           ld ra, 0x18(sp)
+0x160  0x3d078  0x3c318  01013403           ld s0, 0x10(sp)
+0x164  0x3d07c  0x3c31c  00813483           ld s1, 8(sp)
+0x168  0x3d080  0x3c320  00013903           ld s2, 0(sp)
+0x16c  0x3d084  0x3c324  02010113           addi sp, sp, 0x20
+0x170  0x3d088  0x3c328  00008067           ret
+0x174  0x3d08c  0x3c32c  04853483           ld s1, 0x48(a0)
+0x178  0x3d090  0x3c330  00100593           addi a1, zero, 1
+0x17c  0x3d094  0x3c334  0095e663           bltu a1, s1, 0xc                   -> +0x188
+0x180  0x3d098  0x3c338  1e81f0ef|3811e0ef  jal 0x1f1e8 | jal 0x1eb80          -> 0x5c280 _ZN6__asan10AsanThread32AsyncSignalSafeLazyInitFakeStackEv+0x0 [.text] ; -> 0x5aeb8 _ZN6__asan10AsanThread32AsyncSignalSafeLazyInitFakeStackEv+0x0 [.text]
+0x184  0x3d09c  0x3c33c  00050493           mv s1, a0
+0x188  0x3d0a0  0x3c340  ea0492e3           bnez s1, -0x15c                    -> +0x2c
+0x18c  0x3d0a4  0x3c344  f4dff06f           j -0xb4                            -> +0xd8
```

### 2. TryAsanInitFromRtl (G 0x5980c / U 0x58444): `lui a1, 0xff0` at +0x38 (0xff0000) and `lui a2, 0x10` at +0x40 (0x10000)

The address of the `lr.w` / `sc.w`: a0 = (s0 + 2) & -4 (+0x34 / +0x3c), s0 = the auipc pair at +0xc / +0x10 =
`_ZN6__asanL11asan_initedE`+0 (G 0xa5818 / U 0x9fcd8). asan_inited is 4-aligned in both images, so a0 = asan_inited+0 in both, and byte 2
of the word is asan_inited+2 (the byte +0x8c `sb zero, 2(s0)` clears). The address is not lui-derived.

Every use, up to the next write:
- a2: +0x48 `mv a4, a2`; +0x4c `xor a4, a3, a4`; +0x50 `and a4, a4, a1`; +0x54 `xor a4, a3, a4`; +0x58 `sc.w a4, a4,
  (a0)`: a4 is the DATA of the store-conditional (the loaded word with byte 2 set to 1), never its address; sc.w writes
  a4. a2 is read again only at +0x48 on the retry loop +0x5c -> +0x44.
- a1: +0x50 `and` (the byte-2 mask), then the same chain into the data of +0x58. Not read otherwise.
- a1 / a2 are live at +0x80 `jal` AsanInitInternal (no parameter; the call clobbers them) and at +0x7c `ret` (the
  function returns a bool in a0): not read.

Full address in both images: asan_inited+0 (G 0xa5818 / U 0x9fcd8), not formed from either lui value. The values are store data.

```
+off   G        U        word(s)            text                               target(s)
+0x000  0x5980c  0x58444  ff010113           addi sp, sp, -0x10
+0x004  0x59810  0x58448  00113423           sd ra, 8(sp)
+0x008  0x59814  0x5844c  00813023           sd s0, 0(sp)
+0x00c  0x59818  0x58450  0004c517|00048517  auipc a0, 0x4c | auipc a0, 0x48    auipc value 0xa5818 ; auipc value 0xa0450
+0x010  0x5981c  0x58454  00050413|88850413  mv s0, a0 | addi s0, a0, -0x778    pcrel -> 0xa5818 = _ZN6__asanL11asan_initedE+0x0 [.bss] ; pcrel -> 0x9fcd8 = _ZN6__asanL11asan_initedE+0x0 [.bss]
+0x014  0x59820  0x58458  00040583           lb a1, 0(s0)
+0x018  0x59824  0x5845c  00100513           addi a0, zero, 1
+0x01c  0x59828  0x58460  0230000f           fence r, rw
+0x020  0x5982c  0x58464  00a59a63           bne a1, a0, 0x14                   -> +0x34
+0x024  0x59830  0x58468  00813083           ld ra, 8(sp)
+0x028  0x59834  0x5846c  00013403           ld s0, 0(sp)
+0x02c  0x59838  0x58470  01010113           addi sp, sp, 0x10
+0x030  0x5983c  0x58474  00008067           ret
+0x034  0x59840  0x58478  00240513           addi a0, s0, 2
+0x038  0x59844  0x5847c  00ff05b7           lui a1, 0xff0
+0x03c  0x59848  0x58480  ffc57513           andi a0, a0, -4
+0x040  0x5984c  0x58484  00010637           lui a2, 0x10
+0x044  0x59850  0x58488  140526af           lr.w.aq a3, (a0)
+0x048  0x59854  0x5848c  00060713           mv a4, a2
+0x04c  0x59858  0x58490  00e6c733           xor a4, a3, a4
+0x050  0x5985c  0x58494  00b77733           and a4, a4, a1
+0x054  0x59860  0x58498  00e6c733           xor a4, a3, a4
+0x058  0x59864  0x5849c  18e5272f           sc.w a4, a4, (a0)
+0x05c  0x59868  0x584a0  fe0714e3           bnez a4, -0x18                     -> +0x44
+0x060  0x5986c  0x584a4  02869693           slli a3, a3, 0x28
+0x064  0x59870  0x584a8  0386d693           srli a3, a3, 0x38
+0x068  0x59874  0x584ac  00068c63           beqz a3, 0x18                      -> +0x80
+0x06c  0x59878  0x584b0  00000513           mv a0, zero
+0x070  0x5987c  0x584b4  00813083           ld ra, 8(sp)
+0x074  0x59880  0x584b8  00013403           ld s0, 0(sp)
+0x078  0x59884  0x584bc  01010113           addi sp, sp, 0x10
+0x07c  0x59888  0x584c0  00008067           ret
+0x080  0x5988c  0x584c4  ccdff0ef           jal -0x334                         -> 0x59558 _ZN6__asanL16AsanInitInternalEv+0x0 [.text] ; -> 0x58190 _ZN6__asanL16AsanInitInternalEv+0x0 [.text]
+0x084  0x59890  0x584c8  00100513           addi a0, zero, 1
+0x088  0x59894  0x584cc  0310000f           fence rw, w
+0x08c  0x59898  0x584d0  00040123           sb zero, 2(s0)
+0x090  0x5989c  0x584d4  00813083           ld ra, 8(sp)
+0x094  0x598a0  0x584d8  00013403           ld s0, 0(sp)
+0x098  0x598a4  0x584dc  01010113           addi sp, sp, 0x10
+0x09c  0x598a8  0x584e0  00008067           ret
```

### 3. DTLS_on_tls_get_addr (G 0x69720 / U 0x68358): `lui s7, 1` at +0x94 and `lui s8, 1` at +0x128 (each + `addiw -8` = 0xff8)

Every use, up to the next write:
- s7: +0x9c `addiw s7, s7, -8` = 0xff8; +0xa0 `mv a0, s7`, +0xa8 `jal` MmapOrDie (a0 = the size; a1 = a .rodata string,
  a2 = 0); +0xf0 `mv a1, s7`, +0xf8 `jal` UnmapOrDie (a0 = the block, a1 = the size, a2 = 0). Written at +0x134 or
  restored at +0x200; no other read on any path.
- s8: +0x138 `addiw s8, s8, -8` = 0xff8; +0x16c `mv a0, s8`, +0x178 `jal` MmapOrDie (the size); +0x1b4 `mv a1, s8`,
  +0x1bc `jal` UnmapOrDie (the size). Restored at +0x204; no other read on any path.

Full address: none. 0xff8 is only the size argument of the same-named callees in both images; no load, store or jump in
this function uses it as or in a base.

```
+off   G        U        word(s)            text                               target(s)
+0x088  0x697a8  0x683e0  00060c13           mv s8, a2
+0x08c  0x697ac  0x683e4  00068493           mv s1, a3
+0x090  0x697b0  0x683e8  fffaa517|fffab517  auipc a0, 0xfffaa | auipc a0, 0xfffab auipc value 0x137b0 ; auipc value 0x133e8
+0x094  0x697b4  0x683ec  00001bb7           lui s7, 1
+0x098  0x697b8  0x683f0  45450593|71c50593  addi a1, a0, 0x454 | addi a1, a0, 0x71c pcrel -> 0x13c04 = no symbol [.rodata] ; pcrel -> 0x13b04 = no symbol [.rodata]
+0x09c  0x697bc  0x683f4  ff8b8b9b           addiw s7, s7, -8
+0x0a0  0x697c0  0x683f8  000b8513           mv a0, s7
+0x0a4  0x697c4  0x683fc  00000613           mv a2, zero
+0x0a8  0x697c8  0x68400  a90fc0ef           jal -0x3d70                        -> 0x65a58 _ZN11__sanitizer9MmapOrDieEmPKcb+0x0 [.text] ; -> 0x64690 _ZN11__sanitizer9MmapOrDieEmPKcb+0x0 [.text]
+0x0ec  0x6980c  0x68444  000b0513           mv a0, s6
+0x0f0  0x69810  0x68448  000b8593           mv a1, s7
+0x0f4  0x69814  0x6844c  00000613           mv a2, zero
+0x0f8  0x69818  0x68450  bc0fc0ef           jal -0x3c40                        -> 0x65bd8 _ZN11__sanitizer10UnmapOrDieEPvmb+0x0 [.text] ; -> 0x64810 _ZN11__sanitizer10UnmapOrDieEPvmb+0x0 [.text]
+0x0fc  0x6981c  0x68454  00040b13           mv s6, s0
+0x100  0x69820  0x68458  00048693           mv a3, s1
+0x104  0x69824  0x6845c  000c0613           mv a2, s8
+0x108  0x69828  0x68460  0c0b0a63           beqz s6, 0xd4                      -> +0x1dc
+0x124  0x69844  0x6847c  fffaa517|fffab517  auipc a0, 0xfffaa | auipc a0, 0xfffab auipc value 0x13844 ; auipc value 0x1347c
+0x128  0x69848  0x68480  00001c37           lui s8, 1
+0x12c  0x6984c  0x68484  000cd597|000c9597  auipc a1, 0xcd | auipc a1, 0xc9    auipc value 0x13684c ; auipc value 0x131484
+0x130  0x69850  0x68488  fffaa617|fffab617  auipc a2, 0xfffaa | auipc a2, 0xfffab auipc value 0x13850 ; auipc value 0x13488
+0x134  0x69854  0x6848c  3c050b93|68850b93  addi s7, a0, 0x3c0 | addi s7, a0, 0x688 pcrel -> 0x13c04 = no symbol [.rodata] ; pcrel -> 0x13b04 = no symbol [.rodata]
+0x138  0x69858  0x68490  ff8c0c1b           addiw s8, s8, -8
+0x13c  0x6985c  0x68494  02c58413|8b458413  addi s0, a1, 0x2c | addi s0, a1, -0x74c pcrel -> 0x136878 = _ZN11__sanitizerL19number_of_live_dtlsE+0x0 [.bss] ; pcrel -> 0x130d38 = _ZN11__sanitizerL19number_of_live_dtlsE+0x0 [.bss]
+0x14c  0x6986c  0x684a4  00000513           mv a0, zero
+0x150  0x69870  0x684a8  f01a0a13           addi s4, s4, -0xff
+0x154  0x69874  0x684ac  00050b13           mv s6, a0
+0x158  0x69878  0x684b0  074cfa63           bgeu s9, s4, 0x74                  -> +0x1cc
+0x15c  0x6987c  0x684b4  000b3503           ld a0, 0(s6)
+0x160  0x69880  0x684b8  0230000f           fence r, rw
+0x164  0x69884  0x684bc  ffb504e3           beq a0, s11, -0x18                 -> +0x14c
+0x168  0x69888  0x684c0  fe0514e3           bnez a0, -0x18                     -> +0x150
+0x16c  0x6988c  0x684c4  000c0513           mv a0, s8
+0x170  0x69890  0x684c8  000b8593           mv a1, s7
+0x174  0x69894  0x684cc  00000613           mv a2, zero
+0x178  0x69898  0x684d0  9c0fc0ef           jal -0x3e40                        -> 0x65a58 _ZN11__sanitizer9MmapOrDieEmPKcb+0x0 [.text] ; -> 0x64690 _ZN11__sanitizer9MmapOrDieEmPKcb+0x0 [.text]
+0x17c  0x6989c  0x684d4  160b34af           lr.d.aqrl s1, (s6)
+0x180  0x698a0  0x684d8  02049a63           bnez s1, 0x34                      -> +0x1b4
+0x184  0x698a4  0x684dc  1aab35af           sc.d.rl a1, a0, (s6)
+0x188  0x698a8  0x684e0  fe059ae3           bnez a1, -0xc                      -> +0x17c
+0x18c  0x698ac  0x684e4  00100593           addi a1, zero, 1
+0x190  0x698b0  0x684e8  00b4362f           amoadd.d a2, a1, (s0)
+0x194  0x698b4  0x684ec  000d2583           lw a1, 0(s10)
+0x198  0x698b8  0x684f0  00200693           addi a3, zero, 2
+0x19c  0x698bc  0x684f4  fad5eae3           bltu a1, a3, -0x4c                 -> +0x150
+0x1a0  0x698c0  0x684f8  00050493           mv s1, a0
+0x1a4  0x698c4  0x684fc  00813503           ld a0, 8(sp)
+0x1a8  0x698c8  0x68500  000a8593           mv a1, s5
+0x1ac  0x698cc  0x68504  ee4fd0ef           jal -0x291c                        -> 0x66fb0 _ZN11__sanitizer6ReportEPKcz+0x0 [.text] ; -> 0x65be8 _ZN11__sanitizer6ReportEPKcz+0x0 [.text]
+0x1b0  0x698d0  0x68508  0100006f           j 0x10                             -> +0x1c0
+0x1b4  0x698d4  0x6850c  000c0593           mv a1, s8
+0x1b8  0x698d8  0x68510  00000613           mv a2, zero
+0x1bc  0x698dc  0x68514  afcfc0ef           jal -0x3d04                        -> 0x65bd8 _ZN11__sanitizer10UnmapOrDieEPvmb+0x0 [.text] ; -> 0x64810 _ZN11__sanitizer10UnmapOrDieEPvmb+0x0 [.text]
+0x1c0  0x698e0  0x68518  00048513           mv a0, s1
+0x1c4  0x698e4  0x6851c  f8dff06f           j -0x74                            -> +0x150
+0x200  0x69920  0x68558  04813b83           ld s7, 0x48(sp)
+0x204  0x69924  0x6855c  04013c03           ld s8, 0x40(sp)
```

### 4. FakeStack::GC (G 0x3c958 / U 0x3bd6c): `lui s0, 1` at +0x6c, value 0x1000

s9 = `this` (a0 at entry, +0x3c). +0x88 `add s0, s9, s0`: s0 = this + 0x1000, not written again before the restore at
+0x2b0.

Every use, up to the next write:
- +0x100 `add s8, s0, s8`, s8 = ((-1 << (10 - s4)) & 0x3ff) << (w - 15) (+0xd4 to +0xf8; w = the word at this+0x58, s4 the
  class): +0x134 `add a1, s8, s11`, +0x138 `lbu a0, 0(a1)` LOAD and +0x16c `sb s10, 0(a1)` STORE at this + 0x1000 + s8 +
  s11 (s11 the slot). s8 is rewritten per class at +0xf8 and restored at +0x2d0.
- +0x150 `add a0, s0, a0`, +0x154 `add a0, a0, a2`, +0x15c `add a0, a0, a2`: a0 = this + 0x1000 + (s4 << w) +
  (1 << (w - 5)) + (s11 << (s4 + 6)), a frame; +0x160 `ld a2, 0x18(a0)` LOAD at frame + 0x18.
- +0x184 to +0x1b8 and +0x1e4 to +0x284: the frame in a0 is only a branch operand (compared with bounds read through
  .got and with the shadow base).
- +0x1c0 `srli a0, a0, 3`, +0x1c4 `add a1, a1, a0` with a1 = the value of `__asan_shadow_memory_dynamic_address`
  (+0x170 `ld a1, 0(s6)`; s6 = the address in the .got cell G 0x9c870 / U 0x97020, `__asan_shadow_memory_dynamic_address` in both,
  +0x8c): +0x1cc `sd s7, 0(a1)` STORE of
  0xf5f5f5f5f5f5f5f5 at shadow base + (frame >> 3) + 8k (+0x1d4 `addi a1, a1, 8`, loop to +0x1dc). +0x1c8 rewrites a0.
- +0x1bc -> +0x114: the frame in a0 is the first argument of +0x11c `jal` PoisonShadow (a1 = the frame size from the
  stack slot written at +0x10c, a2 = 0xf5).
- +0x288 `auipc a0` rewrites a0 on the CheckFailed path.

Full address in both images: this + 0x1000 + runtime terms, and [`__asan_shadow_memory_dynamic_address`] + (frame >> 3);
`this` is the caller's argument, the shadow base is the same .got-named variable. No static address is formed.

```
+off   G        U        word(s)            text                               target(s)
+0x038  0x3c990  0x3bda4  00058493           mv s1, a1
+0x03c  0x3c994  0x3bda8  00050c93           mv s9, a0
+0x068  0x3c9c0  0x3bdd4  00000d13           mv s10, zero
+0x06c  0x3c9c4  0x3bdd8  00001437           lui s0, 1
+0x070  0x3c9c8  0x3bddc  00060517|0005b517  auipc a0, 0x60 | auipc a0, 0x5b    auipc value 0x9c9c8 ; auipc value 0x96ddc
+0x088  0x3c9e0  0x3bdf4  008c8433           add s0, s9, s0
+0x08c  0x3c9e4  0x3bdf8  ea853b03|24453b03  ld s6, -0x158(a0) | ld s6, 0x244(a0) pcrel -> 0x9c870 = no symbol [.got]; 8-byte cell value 0xa4b38 = __asan_shadow_memory_dynamic_address+0x0 [.bss] ; pcrel -> 0x97020 = no symbol [.got]; 8-byte cell value 0x9eff8 = __asan_shadow_memory_dynamic_address+0x0 [.bss]
+0x0b0  0x3ca08  0x3be1c  95c7bb83|5487bb83  ld s7, -0x6a4(a5) | ld s7, 0x548(a5) pcrel -> 0x10338 = no symbol [.rodata]; 8-byte cell value 0xf5f5f5f5f5f5f5f5 = no symbol [no section]
+0x0d4  0x3ca2c  0x3be40  058cb503           ld a0, 0x58(s9)
+0x0d8  0x3ca30  0x3be44  00a00593           addi a1, zero, 0xa
+0x0dc  0x3ca34  0x3be48  414585bb           subw a1, a1, s4
+0x0e0  0x3ca38  0x3be4c  006a0a93           addi s5, s4, 6
+0x0e4  0x3ca3c  0x3be50  fff00613           addi a2, zero, -1
+0x0e8  0x3ca40  0x3be54  00b615b3           sll a1, a2, a1
+0x0ec  0x3ca44  0x3be58  3ff5f593           andi a1, a1, 0x3ff
+0x0f0  0x3ca48  0x3be5c  ff150613           addi a2, a0, -0xf
+0x0f4  0x3ca4c  0x3be60  414509b3           sub s3, a0, s4
+0x0f8  0x3ca50  0x3be64  00c59c33           sll s8, a1, a2
+0x0fc  0x3ca54  0x3be68  ffa98993           addi s3, s3, -6
+0x100  0x3ca58  0x3be6c  01840c33           add s8, s0, s8
+0x104  0x3ca5c  0x3be70  04000513           addi a0, zero, 0x40
+0x108  0x3ca60  0x3be74  01451533           sll a0, a0, s4
+0x10c  0x3ca64  0x3be78  02a13023           sd a0, 0x20(sp)
+0x110  0x3ca68  0x3be7c  0240006f           j 0x24                             -> +0x134
+0x114  0x3ca6c  0x3be80  0f500613           addi a2, zero, 0xf5
+0x118  0x3ca70  0x3be84  02013583           ld a1, 0x20(sp)
+0x11c  0x3ca74  0x3be88  77d160ef|7a0160ef  jal 0x16f7c | jal 0x167a0          -> 0x539f0 _ZN6__asan12PoisonShadowEmmh+0x0 [.text] ; -> 0x52628 _ZN6__asan12PoisonShadowEmmh+0x0 [.text]
+0x128  0x3ca80  0x3be94  001d8d93           addi s11, s11, 1
+0x12c  0x3ca84  0x3be98  013dd533           srl a0, s11, s3
+0x130  0x3ca88  0x3be9c  f8051ae3           bnez a0, -0x6c                     -> +0xc4
+0x134  0x3ca8c  0x3bea0  01bc05b3           add a1, s8, s11
+0x138  0x3ca90  0x3bea4  0005c503           lbu a0, 0(a1)
+0x13c  0x3ca94  0x3bea8  fe0506e3           beqz a0, -0x14                     -> +0x128
+0x140  0x3ca98  0x3beac  058cb503           ld a0, 0x58(s9)
+0x144  0x3ca9c  0x3beb0  ffb50613           addi a2, a0, -5
+0x148  0x3caa0  0x3beb4  00aa1533           sll a0, s4, a0
+0x14c  0x3caa4  0x3beb8  00c39633           sll a2, t2, a2
+0x150  0x3caa8  0x3bebc  00a40533           add a0, s0, a0
+0x154  0x3caac  0x3bec0  00c50533           add a0, a0, a2
+0x158  0x3cab0  0x3bec4  015d9633           sll a2, s11, s5
+0x15c  0x3cab4  0x3bec8  00c50533           add a0, a0, a2
+0x160  0x3cab8  0x3becc  01853603           ld a2, 0x18(a0)
+0x164  0x3cabc  0x3bed0  fcc972e3           bgeu s2, a2, -0x3c                 -> +0x128
+0x168  0x3cac0  0x3bed4  fc9670e3           bgeu a2, s1, -0x40                 -> +0x128
+0x16c  0x3cac4  0x3bed8  01a58023           sb s10, 0(a1)
+0x170  0x3cac8  0x3bedc  000b3583           ld a1, 0(s6)
+0x1bc  0x3cb14  0x3bf28  f54e6ce3           bltu t3, s4, -0xa8                 -> +0x114
+0x1c0  0x3cb18  0x3bf2c  00355513           srli a0, a0, 3
+0x1c4  0x3cb1c  0x3bf30  00a585b3           add a1, a1, a0
+0x1c8  0x3cb20  0x3bf34  00100513           addi a0, zero, 1
+0x1cc  0x3cb24  0x3bf38  0175b023           sd s7, 0(a1)
+0x1d0  0x3cb28  0x3bf3c  01455633           srl a2, a0, s4
+0x1d4  0x3cb2c  0x3bf40  00858593           addi a1, a1, 8
+0x1d8  0x3cb30  0x3bf44  00150513           addi a0, a0, 1
+0x1dc  0x3cb34  0x3bf48  fe0608e3           beqz a2, -0x10                     -> +0x1cc
+0x1e0  0x3cb38  0x3bf4c  f49ff06f           j -0xb8                            -> +0x128
+0x288  0x3cbe0  0x3bff4  fffe3517|fffe4517  auipc a0, 0xfffe3 | auipc a0, 0xfffe4 auipc value 0x1fbe0 ; auipc value 0x1fff4
+0x2b0  0x3cc08  0x3c01c  08013403           ld s0, 0x80(sp)
+0x2d0  0x3cc28  0x3c03c  04013c03           ld s8, 0x40(sp)
```

### 5. AsyncSignalSafeLazyInitFakeStack (G 0x5c280 / U 0x5aeb8): 4 lui at +0xb0 / +0xb4 / +0xb8 / +0xbc

The values (lui + addiw, then +0xdc to +0xf8 `slli 32` + `add`): a2 = 0x5555555555555555, a4 = 0x3333333333333333,
a5 = 0x0f0f0f0f0f0f0f0f, a6 = 0x0101010101010101. a3 = the stack size (+0x40 / +0x64).

Every use, up to the next write:
- +0xac to +0x11c: a1 = NOT (a3 with every bit below its top bit set). +0x120 to +0x14c (`and` / `sub` / `add` with a2,
  a4, a5; `mul` with a6; `srli 0x38`): a1 = the number of set bits of that, i.e. the number of leading zeros of a3,
  0..64. a2 is rewritten at +0x154, a5 at +0x164, a6 is not read after +0x148, a4 is rewritten at +0x150.
- +0x150 `negw a4, a1`, +0x158 `sll a4, a2, a4`: a4 = 1 << ((64 - a1) & 63); +0x160 `xori a1, a1, 0x3f`, +0x164
  `sll a5, a2, a1`: a5 = 1 << (63 - a1). +0x15c / +0x168: branch operands (compared with a3).
- On the failure paths a4 / a5 are the fifth argument (v2, an integer the report prints) of +0x210 / +0x22c `jal`
  CheckFailed (+0x228 `mv a4, a5`); +0x1f4 `mv a4, a5` rewrites a4 on the third.
- +0x188 `neg a2, a4`, +0x18c `and a2, a4, a2` (the lowest set bit), +0x190 `mul a1, a2, a1` with a1 = the 8 bytes at
  .rodata 0x103b0 (+0x180 / +0x184; 0x0218a392cd3d5dbf in both images), +0x198 `srli a1, a1, 0x3a`: a1 = the top 6 bits,
  an index in 0..63. +0x1a0 `add a1, a2, a1` with a2 = the auipc pair +0x194 / +0x19c = T, +0x1a4 `lbu a1, 0(a1)`: LOAD at
  T + index; the load rewrites a1. (The path +0x90 -> +0x16c takes a4 = a3 without the lui values; the index is 0..63
  there too.)
- +0x1c0 `jal` FakeStack::Create has one parameter (a0, the byte loaded above after clamping); the a4 / a6 still in
  registers there are not arguments and the call clobbers them.

T: unnamed .rodata at G 0x20b1a / U 0x2093a. The region to the next FUNC / OBJECT symbol (G 0x20b5a / U 0x2097a) is 64 bytes in both images, and the
64 bytes are equal: 00010207030d081304190e1c0922142805111a260f2e1d300a1f2336153229393f060c12181b212710252d2f1e3531383e0b1720242c34373d162b333c2a3b3a.
So T + index reads the same byte in both images for every index 0..63. (The kit compared T by its full bytes: the
BYTECMP.md acceptance at +0x19c.)

Full address in both images: T + index, index 0..63, T named by its 64 equal bytes; the lui values never form a static
address.

```
+off   G        U        word(s)            text                               target(s)
+0x08c  0x5c30c  0x5af44  02059063           bnez a1, 0x20                      -> +0xac
+0x090  0x5c310  0x5af48  00068713           mv a4, a3
+0x094  0x5c314  0x5af4c  0d80006f           j 0xd8                             -> +0x16c
+0x0ac  0x5c32c  0x5af64  0016d593           srli a1, a3, 1
+0x0b0  0x5c330  0x5af68  55555637           lui a2, 0x55555
+0x0b4  0x5c334  0x5af6c  33333737           lui a4, 0x33333
+0x0b8  0x5c338  0x5af70  0f0f17b7           lui a5, 0xf0f1
+0x0bc  0x5c33c  0x5af74  01010837           lui a6, 0x1010
+0x0c0  0x5c340  0x5af78  00b6e5b3           or a1, a3, a1
+0x0c4  0x5c344  0x5af7c  5556061b           addiw a2, a2, 0x555
+0x0c8  0x5c348  0x5af80  3337071b           addiw a4, a4, 0x333
+0x0cc  0x5c34c  0x5af84  f0f7879b           addiw a5, a5, -0xf1
+0x0d0  0x5c350  0x5af88  1018081b           addiw a6, a6, 0x101
+0x0d4  0x5c354  0x5af8c  0025d893           srli a7, a1, 2
+0x0d8  0x5c358  0x5af90  0115e5b3           or a1, a1, a7
+0x0dc  0x5c35c  0x5af94  02061893           slli a7, a2, 0x20
+0x0e0  0x5c360  0x5af98  01160633           add a2, a2, a7
+0x0e4  0x5c364  0x5af9c  02071893           slli a7, a4, 0x20
+0x0e8  0x5c368  0x5afa0  01170733           add a4, a4, a7
+0x0ec  0x5c36c  0x5afa4  02079893           slli a7, a5, 0x20
+0x0f0  0x5c370  0x5afa8  011787b3           add a5, a5, a7
+0x0f4  0x5c374  0x5afac  02081893           slli a7, a6, 0x20
+0x0f8  0x5c378  0x5afb0  01180833           add a6, a6, a7
+0x0fc  0x5c37c  0x5afb4  0045d893           srli a7, a1, 4
+0x100  0x5c380  0x5afb8  0115e5b3           or a1, a1, a7
+0x104  0x5c384  0x5afbc  0085d893           srli a7, a1, 8
+0x108  0x5c388  0x5afc0  0115e5b3           or a1, a1, a7
+0x10c  0x5c38c  0x5afc4  0105d893           srli a7, a1, 0x10
+0x110  0x5c390  0x5afc8  0115e5b3           or a1, a1, a7
+0x114  0x5c394  0x5afcc  0205d893           srli a7, a1, 0x20
+0x118  0x5c398  0x5afd0  0115e5b3           or a1, a1, a7
+0x11c  0x5c39c  0x5afd4  fff5c593           not a1, a1
+0x120  0x5c3a0  0x5afd8  0015d893           srli a7, a1, 1
+0x124  0x5c3a4  0x5afdc  00c8f633           and a2, a7, a2
+0x128  0x5c3a8  0x5afe0  40c585b3           sub a1, a1, a2
+0x12c  0x5c3ac  0x5afe4  00e5f633           and a2, a1, a4
+0x130  0x5c3b0  0x5afe8  0025d593           srli a1, a1, 2
+0x134  0x5c3b4  0x5afec  00e5f5b3           and a1, a1, a4
+0x138  0x5c3b8  0x5aff0  00b605b3           add a1, a2, a1
+0x13c  0x5c3bc  0x5aff4  0045d613           srli a2, a1, 4
+0x140  0x5c3c0  0x5aff8  00c585b3           add a1, a1, a2
+0x144  0x5c3c4  0x5affc  00f5f5b3           and a1, a1, a5
+0x148  0x5c3c8  0x5b000  030585b3           mul a1, a1, a6
+0x14c  0x5c3cc  0x5b004  0385d593           srli a1, a1, 0x38
+0x150  0x5c3d0  0x5b008  40b0073b           negw a4, a1
+0x154  0x5c3d4  0x5b00c  00100613           addi a2, zero, 1
+0x158  0x5c3d8  0x5b010  00e61733           sll a4, a2, a4
+0x15c  0x5c3dc  0x5b014  0ae6f063           bgeu a3, a4, 0xa0                  -> +0x1fc
+0x160  0x5c3e0  0x5b018  03f5c593           xori a1, a1, 0x3f
+0x164  0x5c3e4  0x5b01c  00b617b3           sll a5, a2, a1
+0x168  0x5c3e8  0x5b020  0ad7f663           bgeu a5, a3, 0xac                  -> +0x214
+0x16c  0x5c3ec  0x5b024  00040597|0003c597  auipc a1, 0x40 | auipc a1, 0x3c    auipc value 0x9c3ec ; auipc value 0x97024
+0x170  0x5c3f0  0x5b028  47c5b583|ff45b583  ld a1, 0x47c(a1) | ld a1, -0xc(a1) pcrel -> 0x9c868 = no symbol [.got]; 8-byte cell value 0xa2338 = _ZN6__asan28asan_flags_dont_use_directlyE+0x0 [.bss] ; pcrel -> 0x97018 = no symbol [.got]; 8-byte cell value 0x9c7f8 = _ZN6__asan28asan_flags_dont_use_directlyE+0x0 [.bss]
+0x174  0x5c3f4  0x5b02c  0205a683           lw a3, 0x20(a1)
+0x178  0x5c3f8  0x5b030  0245a783           lw a5, 0x24(a1)
+0x17c  0x5c3fc  0x5b034  06d7e263           bltu a5, a3, 0x64                  -> +0x1e0
+0x180  0x5c400  0x5b038  fffb4597|fffb5597  auipc a1, 0xfffb4 | auipc a1, 0xfffb5 auipc value 0x10400 ; auipc value 0x10038
+0x184  0x5c404  0x5b03c  fb05b583|3785b583  ld a1, -0x50(a1) | ld a1, 0x378(a1) pcrel -> 0x103b0 = no symbol [.rodata]; 8-byte cell value 0x218a392cd3d5dbf = no symbol [no section]
+0x188  0x5c408  0x5b040  40e00633           neg a2, a4
+0x18c  0x5c40c  0x5b044  00c77633           and a2, a4, a2
+0x190  0x5c410  0x5b048  02b605b3           mul a1, a2, a1
+0x194  0x5c414  0x5b04c  fffc4617|fffc6617  auipc a2, 0xfffc4 | auipc a2, 0xfffc6 auipc value 0x20414 ; auipc value 0x2104c
+0x198  0x5c418  0x5b050  03a5d593           srli a1, a1, 0x3a
+0x19c  0x5c41c  0x5b054  70660613|8ee60613  addi a2, a2, 0x706 | addi a2, a2, -0x712 pcrel -> 0x20b1a = no symbol [.rodata] ; pcrel -> 0x2093a = no symbol [.rodata]
+0x1a0  0x5c420  0x5b058  00b605b3           add a1, a2, a1
+0x1a4  0x5c424  0x5b05c  0005c583           lbu a1, 0(a1)
+0x1a8  0x5c428  0x5b060  00f5e463           bltu a1, a5, 8                     -> +0x1b0
+0x1ac  0x5c42c  0x5b064  00078593           mv a1, a5
+0x1b0  0x5c430  0x5b068  00050413           mv s0, a0
+0x1b4  0x5c434  0x5b06c  00b6e463           bltu a3, a1, 8                     -> +0x1bc
+0x1b8  0x5c438  0x5b070  00068593           mv a1, a3
+0x1bc  0x5c43c  0x5b074  00058513           mv a0, a1
+0x1c0  0x5c440  0x5b078  970e00ef|94de00ef  jal -0x1fe90 | jal -0x1f6b4        -> 0x3c5b0 _ZN6__asan9FakeStack6CreateEm+0x0 [.text] ; -> 0x3b9c4 _ZN6__asan9FakeStack6CreateEm+0x0 [.text]
+0x1e0  0x5c460  0x5b098  fffc1517|fffc2517  auipc a0, 0xfffc1 | auipc a0, 0xfffc2 auipc value 0x1d460 ; auipc value 0x1d098
+0x1e4  0x5c464  0x5b09c  fffc2597|fffc3597  auipc a1, 0xfffc2 | auipc a1, 0xfffc3 auipc value 0x1e464 ; auipc value 0x1e09c
+0x1e8  0x5c468  0x5b0a0  06f50513|26d50513  addi a0, a0, 0x6f | addi a0, a0, 0x26d pcrel -> 0x1d4cf = no symbol [.rodata] ; pcrel -> 0x1d305 = no symbol [.rodata]
+0x1ec  0x5c46c  0x5b0a4  ea958613|09a58613  addi a2, a1, -0x157 | addi a2, a1, 0x9a pcrel -> 0x1e30d = no symbol [.rodata] ; pcrel -> 0x1e136 = no symbol [.rodata]
+0x1f0  0x5c470  0x5b0a8  0ef00593           addi a1, zero, 0xef
+0x1f4  0x5c474  0x5b0ac  00078713           mv a4, a5
+0x1f8  0x5c478  0x5b0b0  4180f0ef           jal 0xf418                         -> 0x6b890 _ZN11__sanitizer11CheckFailedEPKciS1_yy+0x0 [.text] ; -> 0x6a4c8 _ZN11__sanitizer11CheckFailedEPKciS1_yy+0x0 [.text]
+0x1fc  0x5c47c  0x5b0b4  fffc2517|fffc3517  auipc a0, 0xfffc2 | auipc a0, 0xfffc3 auipc value 0x1e47c ; auipc value 0x1e0b4
+0x200  0x5c480  0x5b0b8  fffb8597|fffb9597  auipc a1, 0xfffb8 | auipc a1, 0xfffb9 auipc value 0x14480 ; auipc value 0x140b8
+0x204  0x5c484  0x5b0bc  acc50513|cbd50513  addi a0, a0, -0x534 | addi a0, a0, -0x343 pcrel -> 0x1df48 = no symbol [.rodata] ; pcrel -> 0x1dd71 = no symbol [.rodata]
+0x208  0x5c488  0x5b0c0  4da58613|7a258613  addi a2, a1, 0x4da | addi a2, a1, 0x7a2 pcrel -> 0x1495a = no symbol [.rodata] ; pcrel -> 0x1485a = no symbol [.rodata]
+0x20c  0x5c48c  0x5b0c4  1d000593           addi a1, zero, 0x1d0
+0x210  0x5c490  0x5b0c8  4000f0ef           jal 0xf400                         -> 0x6b890 _ZN11__sanitizer11CheckFailedEPKciS1_yy+0x0 [.text] ; -> 0x6a4c8 _ZN11__sanitizer11CheckFailedEPKciS1_yy+0x0 [.text]
+0x214  0x5c494  0x5b0cc  fffc2517|fffc3517  auipc a0, 0xfffc2 | auipc a0, 0xfffc3 auipc value 0x1e494 ; auipc value 0x1e0cc
+0x218  0x5c498  0x5b0d0  fffb9597|fffbb597  auipc a1, 0xfffb9 | auipc a1, 0xfffbb auipc value 0x15498 ; auipc value 0x160d0
+0x21c  0x5c49c  0x5b0d4  ab450513|ca550513  addi a0, a0, -0x54c | addi a0, a0, -0x35b pcrel -> 0x1df48 = no symbol [.rodata] ; pcrel -> 0x1dd71 = no symbol [.rodata]
+0x220  0x5c4a0  0x5b0d8  57958613|80958613  addi a2, a1, 0x579 | addi a2, a1, -0x7f7 pcrel -> 0x15a11 = no symbol [.rodata] ; pcrel -> 0x158d9 = no symbol [.rodata]
+0x224  0x5c4a4  0x5b0dc  1d100593           addi a1, zero, 0x1d1
+0x228  0x5c4a8  0x5b0e0  00078713           mv a4, a5
+0x22c  0x5c4ac  0x5b0e4  3e40f0ef           jal 0xf3e4                         -> 0x6b890 _ZN11__sanitizer11CheckFailedEPKciS1_yy+0x0 [.text] ; -> 0x6a4c8 _ZN11__sanitizer11CheckFailedEPKciS1_yy+0x0 [.text]
```
