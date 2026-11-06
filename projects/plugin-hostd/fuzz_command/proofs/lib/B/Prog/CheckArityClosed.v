(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, lib/B/Prog/LLVMFuzzerTestOneInput.v tLLVMFuzzerTestOneInput_holds) at the pinned image (lib/B/Prog/CmdImg.v's PB_cmd, segments tfibsegs, sink head YE2k.tfib_sink_head), in the form of lib/A/Prog/SupRemoveAllRefitClosed.v (a Theorem Labs lane's PASS4-REFIT.md section F): LAWS is the core's AR_laws_ok, TL is cmd_palib, SIGP is cmd_sig_prog_PB, IMG is cmd_img_facts_tfib, VOBJS is cmd_val_objs_PB, PRW is the kit's cmd_prw_tfib and segment E's cmd_prog_rd is the kit's cmd_prog_rom (lib/B/Prog/CmdRecRest.v). What remains is the statement's own hypotheses (the callees' and the runtime entries' contracts at every FP state), HB, MTL and MTFL. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInputClosed.v, with its module paths and module names changed; 13 of its 39 lines of code are new or changed and 37 lines of the source are left out. *)
(* The closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for check_arity on the ASan+UBSan build of
   plugin-hostd/fuzz_command (image B): the walk lib/B/Prog/check_arity_e.v (pb_check_arity) with the per-binary
   record hypotheses it names discharged at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments
   are tfibsegs, and the sink head YE2k.tfib_sink_head), as lib/A/Prog/SupRemoveAllRefitClosed.v does on image A:
   LAWS is the core's AR_laws_ok (a Let of the walk), TL is CmdRecRest.cmd_palib, IMG is
   CmdRecImg.cmd_img_facts_tfib. check_arity writes nothing outside its own frame and allocates nothing, so the walk
   names no PRW and no meter law. What remains is HB and the four runtime entries' contracts at every FP state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m YB1v YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require check_arity_c check_arity_e.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PB_cmd s).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Theorem tcheck_arity_closed
  (ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp))
  (ASTRCSPN : forall fx0 : YK11.FPState,
     @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158)
  (ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp))
  (ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp)) :
  @check_arity_c.tcheck_arity_spec fx rc YE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@check_arity_e.pb_check_arity fx rc YE2k.tfib_sink_head PB_cmd B HB (CmdRecRest.cmd_palib B HB)
  (CmdRecImg.cmd_img_facts_tfib B HB) ASTRCMP ASTRCSPN ASTRNCMP ABCMP MT).
Qed.
End closed.
