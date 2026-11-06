(* The closing pattern of the statement-pass re-fit for reply's ASan walk (lib/A/Prog/reply.v, treply_proof):
   the per-binary record hypotheses it names discharged at the pinned image (lib/A/Prog/CmdImg.v's instance PB_cmd,
   whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head), as the worked example
   SupRemoveAllRefitClosed.v does: TL is cmd_palib, SIGP is cmd_sig_prog_PB, IMG is cmd_img_facts_tfib (the walk takes
   LAWS as the core's AR_laws_ok itself and names no PRW). What remains is the statement's own hypotheses (socket_send's
   contract and the strlen and free wrappers' contracts, at every FP state), HB and MTL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require socket_send_c reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require reply.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem treply_closed
  (SOCKET_SEND : forall fx0 : YK11.FPState,
     @socket_send_c.tsocket_send_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (STRLEN : forall fx0 : YK11.FPState,
     @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strlen))
  (AFREE : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc AE2k.tfib_sink_head SEGS B MT) :
  reply_c.treply_spec B MT.
Proof.
exact (reply.treply_proof B MT SOCKET_SEND STRLEN AFREE HB (CmdRecRest.cmd_palib B HB) MTL
  CmdRecRest.cmd_sig_prog_PB (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.
End closed.
Print Assumptions treply_closed.
