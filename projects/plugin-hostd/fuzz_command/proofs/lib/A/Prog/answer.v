(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of answer (plugin-hostd/fuzz_command, 0x8a4c0, 198 instructions), assembled in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v (pb_cgif_closeX from the segment lemmas): the entry to BODY (answer_e.v), BODY to JOIN and HEAD (answer_br.v), syntax_instantiate's loop from HEAD to JOIN (answer_l.v), and JOIN to the return (answer_t.v); the cut statements and the entry context are lib/A/Prog/answer_s1.v. *)
(* Modified by Theorem Labs, 2026-10: re-fitted to statement passes 4, 4b and 5: the callee and runtime contracts at every FP state, the rounding-mode premise passed to BODY, the FP-existential post; JOIN is used at every FP state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YP09 YI00 YI04 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj CmdRo CmdGlob CmdChk CmdPaLib PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import mix_call_c hand_back_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import answer_s1 answer_e answer_br answer_l answer_t.
Import ListNotations.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's own Section hypotheses (answer_c.v:73-80), word for word *)
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC7 : forall fx0 : YK11.FPState, @astack_malloc_sz_realizes fx0 rc SEGS B (SIG CS___asan_stack_malloc_7) 7.
Hypothesis ASTACK_FREE7 : forall fx0 : YK11.FPState, @astack_free_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_7) 7.
Hypothesis ASET_SHADOW00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Hypothesis ASET_SHADOWF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary walk facts, with cgif's names *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
(* the image facts (CmdRecBase.v's cmd_img_facts): the segments take IMG and apply its field cif_prog_img and the
   CmdRecFacts.v lemmas (RRO, RPG, cmd_addressable_chk, cmd_aread_ok_chk, cmd_rec_cells, cmd_ro_ok_of_aro) by exact *)
Hypothesis IMG : cmd_img_facts SEGS B.

(* answer's statement, from the four segments. JOIN holds at every FP state: the refusal arm reaches it at the FP
   state the snprintf wrapper returns (answer_br.v). *)
Theorem tanswer_spec_holds : tanswer_spec B MT.
Proof.
pose proof (fun fx0 : YK11.FPState => an_join_ok (fx := fx0) B MT THAND_BACK ASTACK_FREE7 ASET_SHADOWF8 LAWS HB ML MTL
  MTFL FFL SIGP IMG) as JOIN.
pose proof (an_head_ok B MT LAWS (JOIN fx)) as HEAD.
pose proof (an_body_ok B MT TMIX_CALL ASNPRINTF VOBJS LAWS HB SIGP PRW IMG JOIN HEAD) as BODY.
unfold tanswer_spec.
intros ly S W regs mem md ch c sh old e x chg R O HPRE HFRM Hfr HROD HRO H10 Hc H11 Hsh H12 HREP HOLD Hold HSH HCALL
  HEV HLIVE HMO.
exact (an_entry_ok B MT ASTACK_MALLOC7 ASET_SHADOW00 ASET_SHADOWF8 LAWS HB TL TLF ML SMP MTL MTFL FFL IMG BODY
  ly S W regs mem md ch c sh old e x chg R O
  (conj HPRE (conj Hfr (conj HROD (conj HRO (conj H10 (conj H11 (conj H12 (conj HREP (conj HOLD
   (conj HSH (conj HCALL (conj HEV (conj HLIVE (conj HMO (conj Hc (conj Hsh Hold)))))))))))))))) HFRM).
Qed.
End e.
End f.
End d.
