(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: only the contract of the strlen wrapper of libreac/fuzz_identity.asan (trampoline 0x4218c -> ___interceptor_strlen 0x4221c -> musl strlen 0x94c64), restated from cgif_file_fuzzer lib/YG0d.v:401-419 astrnlen_realizes without the n bound (no `getr regs 11 = w64 n`, no `0 <= n < 2 ^ 63`, no `k + 8 <= n`; the string ends at the NUL at x + k, so first_byte is stated at k + 1), and with `rom_view segs W mem` replaced by `aro_unowned segs B (aview segs (w_H W) mem)` (lib/A/Rt/WrapRo.v: only the unowned read-only bytes, which a caller can carry across __asan_stack_malloc_<c>); module names. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_identity lib/A/Rt/StrlenDef.v (origin/ossv/recipes 70952e1c8c9)
   to reac-repacer/fuzz_uci image A (fuzz_uci.asan, sha256 6ea017c24525) on the fuzz_uci A core (276afc86670b): module
   paths; record class TfibSyms -> UciSyms (code only; the donor's own Modified-by lines are kept as its record).
   Numerals moved by symbol + offset from the fuzz_identity unstripped twin to the fuzz_uci unstripped twin (each
   function is the same code up to pc-relative fields: bytecmp 7daa0e2a03d9 with repin_check 9cbc3553c09e's target pass); a .got slot moves to the slot that
   holds the same symbol. Every changed numeral, old -> new, symbol + offset in fuzz_identity.asan [occurrences]:
     0x103d8 -> 0x103d0   .rodata word loaded by ___interceptor_strlen+0x260 (report path)   [1 comment]
     0x4218c -> 0x41068   __interceptor_trampoline_strlen+0x0   [1 code, 1 comment]
     0x4221c -> 0x410f4   ___interceptor_strlen+0x0   [2 comment]
     0x42244 -> 0x4111c   ___interceptor_strlen+0x28   [1 comment]
     0x42278 -> 0x41150   ___interceptor_strlen+0x5c   [1 comment]
     0x422c4 -> 0x4119c   ___interceptor_strlen+0xa8   [1 comment]
     0x422c8 -> 0x411a0   ___interceptor_strlen+0xac   [1 comment]
     0x423b0 -> 0x41288   ___interceptor_strlen+0x194   [1 comment]
     0x423cc -> 0x412a4   ___interceptor_strlen+0x1b0   [1 comment]
     0x543d4 -> 0x52fb0   __asan_region_is_poisoned+0x0   [1 comment]
     0x64114 -> 0x62cf0   __sanitizer::mem_is_zero+0x0   [1 comment]
     0x94cb8 -> 0x909f4   strlen+0x54   [1 comment]
     0x9c3a0 -> 0x97010   .got slot holding __sanitizer::common_flags_dont_use (uci tfib_D_GOT_common_flags)   [2 comment]
     0x9c3b0 -> 0x97020   .got slot holding __asan_shadow_memory_dynamic_address (uci tfib_D_GOT_asan_shadow_memory_dynamic_address)   [1 comment]
     0x9e0b0 -> 0x98d20   __interception::real_strlen+0x0   [1 comment]
     0xa5c98 -> 0x9fcd8   __asan::asan_inited+0x0   [1 comment]
   Also: comment: uci has no strlen call in the fuzz target; the callers are musl functions.
   Also: comment: the donor's fuzz_identity-only examples (its .rodata stems 0x21140, 0x21160, 0x21180, 0x211a0, the shadow cell 0x7fffc228 of "S-0808", and arodata_okP, which this unit has not) are dropped: they name identity program data with no uci counterpart.
   Unchanged on purpose: 0x10350, 0x10368, 0x10370 (musl's HIGHS/ONES constants and their end: the same address in
   both images, read by the auipc/ld pairs at strlen+0x3c..0x48 and memchr+0x58..0x64).
   Unchanged on purpose: cgif_file_fuzzer.asan coordinates in comments (0x418f0, 0x41908, 0x41988, 0x430d4).
   Statement text (amemchr_realizes / astrlen_realizes) unchanged apart from module paths, the rename and the entry. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Rt Require Import WrapRo.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* The address the program code calls: `jal ra, 0x41068` (__interceptor_trampoline_strlen, `j 0x410f4`),
   fuzz_uci.asan objdump; cgif_file_fuzzer.asan counterpart 0x418f0 -> 0x41988. In fuzz_uci.asan the fuzz target makes no
   strlen call; musl calls this trampoline (e.g. strncat+0x20 at 0x90a50). *)
Definition STRLEN_ENTRY : Z := 0x41068.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* Read footprint (fuzz_uci.asan objdump): the bytes x .. x + k (src_ok, first_byte); the rest of the 8-byte word
   that holds the NUL (musl strlen's word loop, 0x909f4); the 8-byte-aligned shadow words of the range's shadow hull
   (the inline quick check, 0x4119c/0x411a0) and the shadow bytes between them (0x41288, 0x412a4); two unowned
   read-only words, musl strlen's constants at 0x10350 and 0x10368 (aro_unowned); the runtime cells the allocator
   invariant AR fixes (asan_inited 0x9fcd8, real_strlen 0x98d20, the flags pointer 0x97010, the shadow base pointer
   0x97020); and the flag byte *(0x97010) + 251 (0x41150), for which both values return k. No other read-only byte
   is read on a path the walk takes (0x103d0 and the report strings are read only on the report path). The deepest
   stack the call uses is 2224 bytes below sp: its own frame 2144 (`addi sp,sp,-2032` 0x410f4, `addi sp,sp,-112`
   0x4111c), __asan_region_is_poisoned 64 (0x52fb0), mem_is_zero 16 (0x62cf0); that is inside the 2 * ESTACK window.
   The string may be in the heap, in a side-stack (fake) frame or in unowned .rodata. *)
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
