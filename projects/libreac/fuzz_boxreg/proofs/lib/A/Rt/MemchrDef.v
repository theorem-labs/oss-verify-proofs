(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: only cgif_file_fuzzer lib/YG0d.v's amemchr0_realizes, restated for the memchr wrapper of libreac/fuzz_boxreg with any byte c in a1, any n below 2^32, and a found or not-found result; module paths. *)
(* Modified by Theorem Labs, 2026-10: taken unchanged from libreac/fuzz_disco's proved general memchr contract (a working branch 3b8a77d146c, lib/Rt/MemchrDef.v), the shared text per a Theorem Labs lane, module paths only (fuzz_disco.lib.Rt -> fuzz_boxreg.lib.A.Rt); it replaces boxreg's narrowed statement. Image-generic (segs, B, pc, lo, hi are parameters); boxreg's A (fuzz_boxreg.asan) instance names the memchr trampoline and the musl constants' range lo .. hi. *)
(* R2 exit form (a Theorem Labs lane 00:09Z): fast_unwind_on_fatal / _on_check are 0, so a report or CheckFailed entry, if executed, reaches libunwind's _LIBUNWIND_ABORT sites; this contract admits no state that reaches one (the premises refute the branches above), and a walk that uses it must end any such route at the entry as a refusal (ok_or_refused), never step into it. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import ConstsViewDef.
Import ListNotations.
Open Scope Z_scope.
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
rom_view segs W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte segs W mem x n c k /\ getr regs' 10 = (if k <? n then w64 (x + k) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition amemchr_realizesM (lo hi pc : Z) : Prop :=
forall ly S W regs mem md x c n,
ecall_pre segs B ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 c -> getr regs 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> amem_range x n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
consts_view segs lo hi W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte segs W mem x n c k /\ getr regs' 10 = (if k <? n then w64 (x + k) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End c.
End b.
