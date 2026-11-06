(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment K of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86a04 .. the jal to check_round_trip at 0x86a38) from its five steps, each taken at every FP state (check_reply and check_words return at an FP state of their own); the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_Kall.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (cl_BX_of_FR0: a segment from its local steps). Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo CmdGlob CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c send_message_c check_reply_c
  check_arity_c check_words_c check_refusal_c check_round_trip_c verbs_receive_c LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_Kcut.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require LLVMFuzzerTestOneInput_Kreply
  LLVMFuzzerTestOneInput_Karity LLVMFuzzerTestOneInput_Kwords LLVMFuzzerTestOneInput_Krefusal.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the four callees' statements, exactly LLVMFuzzerTestOneInput_c.v's Section hypotheses (every FP state) *)
Hypothesis HCHECK_REPLY : forall fx0 : YK11.FPState, @tcheck_reply_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_ARITY : forall fx0 : YK11.FPState, @tcheck_arity_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_WORDS : forall fx0 : YK11.FPState, @tcheck_words_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_REFUSAL : forall fx0 : YK11.FPState, @tcheck_refusal_spec fx0 rc SK PI B MT.
(* the walk's per-binary facts, with the names of a Theorem Labs lane's RULING-STMT.md section 1; every record fact the steps use
   is a lemma of lib/B/Prog/CmdRecFacts.v over these, and the harness facts are the cut file's lt_kregs_props /
   lt_msg_props, proved from harness_props_holds_a *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.

(* segment K: from the words built (0x86a04) through check_reply, check_arity, check_words and check_refusal to
   check_round_trip's entry *)
Theorem lt_seg_K : forall m, LTA_RT B MT m -> LT_K_stmt (fx := fx) B MT m.
Proof.
exact (lt_seg_K_compose B MT
  (fun fx1 => LLVMFuzzerTestOneInput_Kreply.lt_seg_K0 (fx := fx1) B MT HCHECK_REPLY LAWS HB IMG SIGP MTFL)
  (fun fx1 => LLVMFuzzerTestOneInput_Karity.lt_seg_K1 (fx := fx1) B MT HCHECK_ARITY HB LAWS SIGP IMG)
  (fun fx1 => LLVMFuzzerTestOneInput_Kwords.lt_seg_K2 (fx := fx1) B MT HCHECK_WORDS HB LAWS SIGP MTL IMG)
  (fun fx1 => LLVMFuzzerTestOneInput_Krefusal.lt_seg_K3 (fx := fx1) B MT HCHECK_REFUSAL HB LAWS SIGP IMG)
  (fun fx1 => LLVMFuzzerTestOneInput_Krefusal.lt_seg_K4 (fx := fx1) B MT LAWS SIGP)).
Qed.

End e.
End f.
End d.
