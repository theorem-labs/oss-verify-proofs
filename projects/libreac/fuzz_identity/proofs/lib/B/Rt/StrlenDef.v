(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: only the contract of the strlen wrapper of libreac/fuzz_identity.asan-ubsan (trampoline 0x421f4 -> ___interceptor_strlen 0x42284 -> musl strlen 0x94f50), restated from cgif_file_fuzzer lib/YG0d.v:401-419 astrnlen_realizes without the n bound (no `getr regs 11 = w64 n`, no `0 <= n < 2 ^ 63`, no `k + 8 <= n`; the string ends at the NUL at x + k, so first_byte is stated at k + 1), and with `rom_view segs W mem` replaced by `aro_unowned segs B (aview segs (w_H W) mem)` (lib/B/Rt/WrapRo.v: only the unowned read-only bytes, which a caller can carry across __asan_stack_malloc_<c>); module names. The text is lib/A/Rt/StrlenDef.v's; only STRLEN_ENTRY, the WrapRo module and the comments differ. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import WrapRo.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* The address the program code calls: `jal ra, 0x421f4` (__interceptor_trampoline_strlen, `j 0x42284`),
   fuzz_identity.asan-ubsan objdump; cgif_file_fuzzer.asan-ubsan counterpart 0x41920 -> 0x419b8. *)
Definition STRLEN_ENTRY : Z := 0x421f4.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* Read footprint (fuzz_identity.asan-ubsan objdump; the interceptor is the asan build's, instruction for
   instruction, 0x68 bytes higher): the bytes x .. x + k (src_ok, first_byte); the rest of the 8-byte word that
   holds the NUL (musl strlen's word loop, 0x94fa4); the 8-byte-aligned shadow words of the range's shadow hull
   (the inline quick check, 0x4232c/0x42330) and the shadow bytes between them (0x42418, 0x42434); two unowned
   read-only words, musl strlen's constants at 0x10350 and 0x10368 (aro_unowned); the runtime cells the allocator
   invariant AR fixes (asan_inited 0xa5f98, real_strlen 0x9e390, the flags pointer 0x9c680, the shadow base pointer
   0x9c690); and the flag byte *(0x9c680) + 251 (0x422e0), for which both values return k. No other read-only byte
   is read on a path the walk takes. The deepest stack the call uses is 2224 bytes below sp: its own frame 2144
   (`addi sp,sp,-2032` 0x42284, `addi sp,sp,-112` 0x422ac), __asan_region_is_poisoned 64 (0x5443c), mem_is_zero 16
   (0x6417c); that is inside the 2 * ESTACK window.
   The string may be in the heap, in a side-stack (fake) frame or in unowned .rodata: for a .rodata string the
   caller gets its bytes from arodata_okP and its shadow from the start-up shadow cells of the core (e.g.
   0x7fffc22c = 7 for "S-0808" at 0x21160). *)
Definition astrlen_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x k,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> 0 < x ->
0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x (k + 1) 0 k ->
src_ok segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
aro_unowned segs B (aview segs (w_H W) mem) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End c.
End b.
