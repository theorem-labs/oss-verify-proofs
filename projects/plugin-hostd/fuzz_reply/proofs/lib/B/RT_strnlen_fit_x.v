(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RT_strnlen_fit_x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/RT_strnlen_fit_x.v, with its module paths, module names and addresses changed; 8 of its 38 lines of code are new or changed. *)
(* The strnlen wrapper's runtime contract at image B's (fuzz_reply.asan-ubsan) site, over a generic allocator
   invariant ARx under the five-law record lib/Rt/RTx.v rt_laws plus YCbqG's zero-shadow law (the two inputs of
   lib/B/RTxIcpt.v icpt_laws_of_rt).  The image-B twin of lib/A/RT_strnlen_fit_x.v, with B names.  No function is
   walked here: the walk is lib/B/Rt/Strnlen.v strnlen_icpt_realizesM_x / strnlen_icpt_realizes_x (the wrapper at
   0x421e8, musl strnlen, the memchr wrapper at 0x42208 by lib/B/Rt/Memchr_x.v; Qed over YE2y.icpt_laws_x).
   - rt_strnlen_fit_x is RTx.v's astrnlen_whole_realizesM_x at segs := pa_segs PB_fr, lo / hi = 0x10350 / 0x10370
     (musl memchr's mask window, the cells consts_view reads) and pc := SIGMA WS_strnlen (W_place.v:44, 0x421e8).
   - rt_strnlen_whole_fit_x is RTx.v's astrnlen_whole_realizes_x (rom_view in place of consts_view) at the same segs
     and pc: the text of the B top's ASTRNLEN_x (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:811 on window c052f9c9a32).
   - pa_segs PB_fr is tfibsegs (W_img.v PB_fr: pa_segs := frsegs, the AsanUbsan loaded segments = YB1v.v:12 tfibsegs),
     and IcptRealizesX.v's texts are RTx.v's at tfibsegs (RTxIcpt.astrnlen_whole_realizesM_x_iff /
     astrnlen_whole_realizes_x_iff), so each proof is the walk's theorem after the pc is rewritten to its numeral. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Rt Require Strnlen.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require RTx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RTxIcpt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_tbl W_place W_kit W_img.
Import ListNotations.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* the strnlen wrapper's site is the walk's entry (W_place.v:44; Rt/Strnlen.v SNL_ENTRY) *)
Lemma snl_id_sigma : SIGMA WS_strnlen = 0x421e8.
Proof. reflexivity. Qed.

Theorem rt_strnlen_fit_x : forall B (ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop),
  RTx.rt_laws tfibsegs B ARx -> YCbqG.ARx_zshadow_law tfibsegs B ARx -> TfibSyms B ->
  RTx.astrnlen_whole_realizesM_x segs B ARx 0x10350 0x10370 (SIGMA WS_strnlen).
Proof.
  intros B ARx RL ZS TB. rewrite snl_id_sigma.
  apply (proj1 (RTxIcpt.astrnlen_whole_realizesM_x_iff B ARx 0x10350 0x10370 0x421e8)).
  exact (Strnlen.strnlen_icpt_realizesM_x B ARx (RTxIcpt.icpt_laws_of_rt B ARx RL ZS) TB).
Qed.

Theorem rt_strnlen_whole_fit_x : forall B (ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop),
  RTx.rt_laws tfibsegs B ARx -> YCbqG.ARx_zshadow_law tfibsegs B ARx -> TfibSyms B ->
  RTx.astrnlen_whole_realizes_x segs B ARx (SIGMA WS_strnlen).
Proof.
  intros B ARx RL ZS TB. rewrite snl_id_sigma.
  apply (proj1 (RTxIcpt.astrnlen_whole_realizes_x_iff B ARx 0x421e8)).
  exact (Strnlen.strnlen_icpt_realizes_x B ARx (RTxIcpt.icpt_laws_of_rt B ARx RL ZS) TB).
Qed.

End b.
