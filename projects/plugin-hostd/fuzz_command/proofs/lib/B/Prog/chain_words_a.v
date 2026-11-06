(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the assembly of the walk of chain_words (0x8da84) on the ASan+UBSan build of
   plugin-hostd/fuzz_command, the B twin of lib/A/Prog/chain_words_a.v (A walk a working branch
   5e2cdad423e): the six segments of lib/B/Prog/chain_words_d.v and the induction over the passes of the member
   loop (head 0x8dcfc) take every entry state with cw_pre to cw_post (cw_run); chain_words.v turns that into the
   statement.

   What B adds to A's assembly: the post is apost_baseF, so the two recorder calls (S4, S5) end at an FP state
   fxrel-related to the entry's and take the join segment at every such state (from_KJq, chain_words_d.v). S6
   makes no call, so it is taken here in its FP-generic form `forall fx0, cw_S6P (fx := fx0) B MT` and
   instantiated at the state each call returned at. Both refusal cuts of B (KR1 before the loop, where F is still
   in s3 and s6, and KR2 inside it, where F is in the frame slots) come from S5. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import chain_words_c chain_words_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* every pass of the member loop reaches the post: by induction on the passes left, ntok - 2 - j; a pass j with
   j >= ntok - 2 has no state (INV_KL asks j < ntok - 2) *)
Lemma cw_loop : cw_S3P B MT -> forall c, cw_pre B MT c ->
  from_KR2 B MT c -> from_KD B MT c -> forall j, from_KL B MT c j.
Proof.
intros S3 c HP HR HD.
assert (H : forall n j, (Z.to_nat (x_ntok c - 2 - j) <= n)%nat -> from_KL B MT c j).
{ induction n as [|n IH]; intros j Hj.
  - intros ly3 S3' W3 regs3 mem3 md3 (_ & _ & Hj' & _). exfalso. lia.
  - destruct (Z_lt_le_dec j (x_ntok c - 2)) as [Hlt | Hge].
    + apply (S3 c j HP HR HD). apply IH. lia.
    + intros ly3 S3' W3 regs3 mem3 md3 (_ & _ & Hj' & _). exfalso. lia. }
intros j. exact (H _ j (le_n _)).
Qed.
Theorem cw_run : cw_S1P B MT -> cw_S2P B MT -> cw_S3P B MT -> cw_S4P B MT -> cw_S5P B MT ->
  (forall fx0 : YK11.FPState, cw_S6P (fx := fx0) B MT) ->
  forall c, cw_pre B MT c -> frm0 fx ->
  SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_chain_words) (x_regs c) (x_mem c) (x_md c)) (cw_post B MT c).
Proof.
intros S1 S2 S3 S4 S5 S6 c HP HFRM.
assert (HPf : forall f, cw_pre B MT (cw_setpos c f)) by (intros f; exact (cw_pre_setpos B MT c f HP)).
(* the join at every FP state a recorder call may return at: S6 makes no call, so it holds at each of them *)
assert (HJq : forall f, from_KJq B MT (cw_setpos c f))
  by (intros f fq _; exact (S6 fq (cw_setpos c f) (HPf f))).
assert (HRf : forall f, from_KR1 B MT (cw_setpos c f) /\ from_KR2 B MT (cw_setpos c f))
  by (intros f; exact (S5 _ (HPf f) HFRM (HJq f))).
assert (HDf : forall f, from_KD B MT (cw_setpos c f)) by (intros f; exact (S4 _ (HPf f) HFRM (HJq f))).
apply (S1 c HP (fun f => proj1 (HRf f))).
intros f. apply (S2 _ (HPf f) (proj1 (HRf f))).
exact (cw_loop S3 _ (HPf f) (proj2 (HRf f)) (HDf f) 0).
Qed.
End e.
End f.
End d.
