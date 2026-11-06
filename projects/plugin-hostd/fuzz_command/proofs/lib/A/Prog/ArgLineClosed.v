(* The closing pattern of the re-fit to statement passes 4-5 for arg_line: the ASan walk (lib/A/Prog/arg_line.v,
   arg_line_holds) with the per-binary record hypotheses it names discharged at the pinned image (lib/A/Prog/CmdImg.v's
   instance PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head), as SupRemoveAllRefitClosed.v
   does: LAWS is the core's AR_laws_ok, TL is cmd_palib, VOBJS is cmd_val_objs_PB, SIGP is cmd_sig_prog_PB, IMG is
   cmd_img_facts_tfib, and PRW is the kit's cmd_prw_tfib (lib/A/Prog/CmdRecRest.v: the program's statics lie in
   tfibsegs' read-write window). What remains is the statement's own hypotheses (rec_canonical's contract and the
   strlen entry, at every FP state), HB and MTL. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require rec_canonical_c arg_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require arg_line.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
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
Theorem targ_line_closed
  (TREC_CANONICAL : forall fx0 : YK11.FPState,
     @rec_canonical_c.trec_canonical_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (ASTRLEN : forall fx0 : YK11.FPState,
     @RtString.astrlen_realizes fx0 rc SEGS B (@pa_sigma _ cmd_listing PB_cmd CS___interceptor_trampoline_strlen)) :
  arg_line_c.targ_line_spec B MT.
Proof.
exact (arg_line.arg_line_holds B MT HB (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) MTL
  CmdRecRest.cmd_val_objs_PB CmdRecRest.cmd_sig_prog_PB (CmdRecImg.cmd_img_facts_tfib B HB) (CmdRecRest.cmd_prw_tfib B HB)
  TREC_CANONICAL ASTRLEN).
Qed.
End closed.
Print Assumptions targ_line_closed.
