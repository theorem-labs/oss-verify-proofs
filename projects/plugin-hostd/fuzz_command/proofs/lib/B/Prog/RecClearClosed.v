(* Modified by Theorem Labs, 2026-10: the closing file of rec_clear's ASan+UBSan walk (a Theorem Labs lane's PASS4-REFIT.md section
   F, on the B image): trec_clear_closed proves a Theorem Labs lane's trec_clear_spec (lib/B/Prog/rec_clear_c.v) at the pinned
   image, lib/B/Prog/CmdImg.v's instance PB_cmd (segments tfibsegs) with B's sink head YE2k.tfib_sink_head, both
   passed explicitly. It discharges the walk's (lib/B/Prog/rec_clear.v, trec_clear_holds) per-binary hypotheses as
   a Theorem Labs lane's lib/A/Prog/RecBClosed.v (a working branch f349bdaedba) and lib/A/Prog/SupRemoveAllRefitClosed.v
   do on A: TL is CmdRecRest.cmd_palib, VOBJS is CmdRecRest.cmd_val_objs_PB, cmd_sig_prog_PB is CmdRecRest's lemma of
   that name, cmd_img_facts_tfib is CmdRecImg's lemma of that name, and PRW is CmdRecRest.cmd_prw_tfib (the program's
   statics lie in tfibsegs' read-write window, lib/B/YB13.v's tfib_rw_window). What remains: the allocator record HB,
   the meter's laws MTL, and the callee's and the runtime entries' contracts in the statement's `forall fx0` form. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require rec_calls_free_c rec_clear_c rec_clear.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SK := YE2k.tfib_sink_head.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PB_cmd c).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem trec_clear_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK PB_cmd B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc SK SEGS B MT)
  (AFREE_NULL4 : forall fx0 : YK11.FPState, @YC5d.afree_null04_rule fx0 rc SK SEGS B MT)
  (AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG CS___asan_memset)) :
  @rec_clear_c.trec_clear_spec fx rc SK PB_cmd B MT.
Proof.
exact (@rec_clear.trec_clear_holds fx rc SK PB_cmd B MT HB (CmdRecRest.cmd_palib B HB) MTL TRCF AFREE4 AFREE_NULL4
  AMEMSET CmdRecRest.cmd_val_objs_PB (CmdRecImg.cmd_img_facts_tfib) CmdRecRest.cmd_sig_prog_PB
  (CmdRecRest.cmd_prw_tfib B HB)).
Qed.
End closed.
