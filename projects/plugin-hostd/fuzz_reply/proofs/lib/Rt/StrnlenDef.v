(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: only cgif_file_fuzzer lib/YG0d.v's astrnlen_realizes, restated for the strnlen wrapper over a buffer that is addressable for all n bytes (the sibling of lib/Rt/MemchrDef.v's amemchr_realizes): n < 2^32, [x, x+n) checked and present, and the result is the first NUL index k within n, or n when there is none, so the k + 8 <= n premise and the slack-word premise are dropped; the stack frame stays 2 * ESTACK, because the wrapper calls musl strnlen, which calls the memchr wrapper. The constant-bytes form takes lib/Rt/ConstsViewDef.v's consts_view over lo / hi; module paths. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_disco/lib/Rt/StrnlenDef.v
   (a working branch a58fbc98b07, the shared strnlen text, a Theorem Labs lane 23:57Z), with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef.
Import ListNotations.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Definition astrnlen_whole_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x n,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> (forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
rom_view segs W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte segs W mem x n 0 k /\ getr regs' 10 = w64 k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition astrnlen_whole_realizesM (lo hi pc : Z) : Prop :=
forall ly S W regs mem md x n,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> (forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
consts_view segs lo hi W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte segs W mem x n 0 k /\ getr regs' 10 = w64 k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End c.
End b.
