(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: cgif_file_fuzzer lib/YG0d.v's amemchr0_realizes, in the general form libreac/fuzz_disco proves it (lib/Rt/MemchrDef.v amemchr_realizesM, origin/cold/h-rw-dis-7-rt 91c9538449b): any byte c in a1, any n below 2^32, the ASan premises over all n bytes, and a found or not-found result; disco's consts_view premise replaced by aro_unowned over the view of memory (lib/A/Rt/WrapRo.v), which a caller carries and from which the walk derives the two constants musl memchr reads (0x10350 and 0x10368); module paths. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_identity/lib/A/Rt/MemchrDef.v (donor image sha256 c954b804786c), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
(* Address check, fuzz_identity.asan (sha256 c954b804...291b) against cgif_file_fuzzer.asan (7093581a...70f0):
(* Modified by Theorem Labs, 2026-10: derived from lib/A/MemchrDef.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_pin's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/MemchrDef.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
   pc       word      instruction           cgif pc  cgif word  cgif name (lib/A/YB1w.v)
   0x421a4  7c40106f  j 0x43968             0x41908  7cc0106f   tfib_A_memchr (j 0x430d4 = tfib_A_icpt_memchr)
   The program calls this trampoline (__interceptor_trampoline_memchr) at 0x81180 and 0x81e2c. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Rt Require Import WrapRo.
Import ListNotations.
Open Scope Z_scope.
Definition MEMCHR_ENTRY : Z := 0x41928.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Definition amemchr_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x c n,
ecall_pre segs B ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 c -> getr regs 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> amem_range x n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
aro_unowned segs B (aview segs (w_H W) mem) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte segs W mem x n c k /\ getr regs' 10 = (if k <? n then w64 (x + k) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End c.
End b.
