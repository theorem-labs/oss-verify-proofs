(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of answer (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan,
   entry 0x8aa10, 209 instructions, 836 bytes): tanswer_spec of a Theorem Labs lane's lib/B/Prog/answer_c.v (a working branch
   f490061c104), assembled from four segments as the A walk lib/A/Prog/answer.v (a working branch d28426fbb96)
   does: the entry to BODY (answer_e.v), BODY to JOIN and HEAD (answer_br.v, with the snprintf step of answer_snp.v),
   syntax_instantiate's loop from HEAD to JOIN (answer_l.v), and JOIN to the return (answer_t.v); the cut statements
   are answer_s1.v's. B's code differs from A's in the loop (B's registers and its five UBSan trap sites) and in the
   snprintf contract (the shared one, RtPFCmd.asnprintf_sh); the post is apost_baseF: JOIN is used at the FP state the
   snprintf call returns on the refused arm and at the entry's FP state on the loop's exit.
   Report / trap / abort edges, each refuted at its branch (the segment files say where and from what):
   0x8abac (beqz s3, UBSan) in answer_bm.v; 0x8ac08, 0x8ac38, 0x8ac64, 0x8ac80 (UBSan), 0x8ac6c -> 0x8ad50
   (__asan_report_load1), 0x8ac78 -> 0x8ac7c and 0x8ad44 -> 0x8ad48 (__asan_report_store1), 0x8ac34 and 0x8aca0
   (abort) in answer_l.v. The entry's and the tail's branches (0x8aa7c, 0x8aa9c, 0x8acc8) are decided by the record's
   use-after-return cell and the frame address (answer_e.v, answer_t.v).
   Section hypotheses beyond the statement's: the allocator record HB, the meter's laws MTL and frame laws MTFL, the
   side-stack entries' record TLF (PaLibF), and, in the form a Theorem Labs lane states them only at the pinned image (PI := PB_cmd,
   tfibsegs), cmd_palib, cmd_sig_prog_PB, cmd_img_facts_tfib and cmd_frame_flag_law; PRW for the store into
   g_rec.state. AnswerClosed.v discharges all of them but HB, MTL and MTFL at the pinned image. Base: a Theorem Labs lane
   fc8bcbd8b42 (the snprintf contract's band premise `+ 8`, discharged in answer_snp.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YP09 YI00 YI04 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj CmdRo CmdGlob CmdChk CmdPaLib PaLibF CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import mix_call_c hand_back_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
answer_s1 answer_e answer_br answer_l answer_t.
Import ListNotations.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's own Section hypotheses (answer_c.v:93-100), word for word *)
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC7 : forall fx0 : YK11.FPState, @astack_malloc_sz_realizes fx0 rc SEGS B (SIG CS___asan_stack_malloc_7) 7.
Hypothesis ASTACK_FREE7 : forall fx0 : YK11.FPState, @astack_free_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_7) 7.
Hypothesis ASET_SHADOW00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Hypothesis ASET_SHADOWF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses (a Theorem Labs lane's RULING-STMT.md section 1): the allocator record, the meter's laws, the side-stack
   entries' record; and the facts a Theorem Labs lane states only at the pinned image (CmdRecRest.v cmd_palib, cmd_sig_prog_PB,
   cmd_frame_flag_law; CmdRecImg.v cmd_img_facts_tfib), each under its lemma's name, at this walk's abstract image;
   PRW for the store into g_rec.state (CmdRecCells.PROG_WRITABLE) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TLF : PALibF (PI := PI) B.
Hypothesis cmd_palib : forall B0, CmdBSyms B0 -> PALib (PI := PI) B0.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog (PI := PI).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Hypothesis cmd_frame_flag_law : forall B0, frame_flag_lawP SEGS B0.

(* answer's statement, from the four segments *)
Theorem tanswer_spec_holds : tanswer_spec B MT.
Proof.
(* JOIN at every FP state: the refused arm reaches it at the FP state the snprintf call returns *)
pose proof (fun fx1 : YK11.FPState => @an_join_ok fx1 rc SK PI B MT THAND_BACK ASTACK_FREE7 ASET_SHADOWF8 HB MTL MTFL
  cmd_sig_prog_PB cmd_img_facts_tfib cmd_frame_flag_law) as JOIN.
pose proof (an_head_ok B MT (JOIN fx)) as HEAD.
pose proof (an_body_ok B MT TMIX_CALL ASNPRINTF VOBJS HB cmd_sig_prog_PB PRW cmd_img_facts_tfib JOIN HEAD) as BODY.
unfold tanswer_spec.
intros ly S W regs mem md ch c sh old e x chg R O HPRE HFRM Hfr HROD HRO H10 Hc H11 Hsh H12 HREP HOLD Hold HSH HCALL
  HEV HLIVE HMO.
exact (an_entry_ok B MT ASTACK_MALLOC7 ASET_SHADOW00 ASET_SHADOWF8 HB cmd_palib TLF MTL MTFL cmd_img_facts_tfib
  cmd_frame_flag_law BODY
  ly S W regs mem md ch c sh old e x chg R O
  (conj HPRE (conj Hfr (conj HROD (conj HRO (conj H10 (conj H11 (conj H12 (conj HREP (conj HOLD
  (conj HSH (conj HCALL (conj HEV (conj HLIVE (conj HMO (conj (conj Hc (conj Hsh Hold)) HFRM)))))))))))))))).
Qed.
End e.
End f.
End d.
Print Assumptions tanswer_spec_holds.
