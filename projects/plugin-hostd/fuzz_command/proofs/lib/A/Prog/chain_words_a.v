(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the assembly of the walk of chain_words (0x8dfd4) on the ASan build of
   plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v (the top theorem of
   cgif_raw_addframe's walk, which chains the segment lemmas): the six segments of chain_words_d.v and the induction
   over the passes of the member loop (head 0x8e234) take every entry state with cw_pre and rounding mode 0 to
   cw_post (cw_run). The last segment S6 is taken at every FP state: the recorder calls of S4 and S5 return at the
   FP state fx1 they leave. chain_words_exact.v turns cw_run into the statement. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx chain_words_c chain_words_d.
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
Lemma cw_loop : forall rlo rhi, cw_S3P B MT rlo rhi -> forall c, cw_pre B MT rlo rhi c ->
  from_KR B MT c -> from_KD B MT c -> forall j, from_KL B MT c j.
Proof.
intros rlo rhi S3 c HP HR HD.
assert (H : forall n j, (Z.to_nat (x_ntok c - 2 - j) <= n)%nat -> from_KL B MT c j).
{ induction n as [|n IH]; intros j Hj.
  - intros ly3 S3' W3 regs3 mem3 md3 (_ & Hj' & _). exfalso. lia.
  - destruct (Z_lt_le_dec j (x_ntok c - 2)) as [Hlt | Hge].
    + apply (S3 c j HP HR HD). apply IH. lia.
    + intros ly3 S3' W3 regs3 mem3 md3 (_ & Hj' & _). exfalso. lia. }
intros j. exact (H _ j (le_n _)).
Qed.
Theorem cw_run : forall rlo rhi, cw_S1P B MT rlo rhi -> cw_S2P B MT rlo rhi -> cw_S3P B MT rlo rhi ->
  cw_S4P B MT rlo rhi -> cw_S5P B MT rlo rhi -> (forall fx0 : YK11.FPState, cw_S6P (fx := fx0) B MT rlo rhi) ->
  forall c, frm0 fx -> cw_pre B MT rlo rhi c ->
  SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_chain_words) (x_regs c) (x_mem c) (x_md c)) (cw_post B MT c).
Proof.
intros rlo rhi S1 S2 S3 S4 S5 S6 c HFRM HP.
assert (HPf : forall f, cw_pre B MT rlo rhi (cw_setpos c f))
  by (intros f; exact (cw_pre_setpos B MT rlo rhi c f HP)).
assert (HJf : forall f (fx0 : YK11.FPState), from_KJ (fx := fx0) B MT (cw_setpos c f))
  by (intros f fx0; exact (S6 fx0 _ (HPf f))).
assert (HRf : forall f, from_KR B MT (cw_setpos c f)) by (intros f; exact (S5 _ HFRM (HPf f) (HJf f))).
assert (HDf : forall f, from_KD B MT (cw_setpos c f)) by (intros f; exact (S4 _ HFRM (HPf f) (HJf f))).
apply (S1 c HP HRf).
intros f. apply (S2 _ (HPf f) (HRf f)).
exact (cw_loop rlo rhi S3 _ (HPf f) (HRf f) (HDf f) 0).
Qed.
End e.
End f.
End d.
