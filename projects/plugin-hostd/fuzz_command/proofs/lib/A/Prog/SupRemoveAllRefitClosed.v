(* The closing pattern of the statement-pass re-fit, on the worked example: sup_remove_all's re-fitted ASan
   walk (lib/A/Prog/sup_remove_all_refit.v, tsup_remove_all_spec_holds) with the per-binary record hypotheses it
   names discharged at the pinned image (lib/A/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and
   the sink head AE2k.tfib_sink_head), as lib/A/Prog/RecBClosed.v
   does for its 23 walks: LAWS is the core's AR_laws_ok, TL is cmd_palib, SIGP is cmd_sig_prog_PB, VOBJS is
   cmd_val_objs_PB, IMG is cmd_img_facts_tfib, and PRW is cmd_prw_tfib (the program's statics lie in tfibsegs'
   read-write window, AB13.v's tfib_rw_window). What remains is HB, MTL and the callees' contracts at every FP
   state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m AB1v AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require rec_calls_free_c answer_c sup_remove_all_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require sup_remove_all_refit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.


Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem tsup_remove_all_closed
  (TREC_CALLS_FREE : forall fx0 : YK11.FPState,
     @rec_calls_free_c.trec_calls_free_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT) :
  sup_remove_all_c.tsup_remove_all_spec B MT.
Proof.
exact (sup_remove_all_refit.tsup_remove_all_spec_holds B MT TREC_CALLS_FREE TANSWER CmdRecRest.cmd_val_objs_PB HB
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) MTL CmdRecRest.cmd_sig_prog_PB (CmdRecRest.cmd_prw_tfib B HB)
  (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.
End closed.
