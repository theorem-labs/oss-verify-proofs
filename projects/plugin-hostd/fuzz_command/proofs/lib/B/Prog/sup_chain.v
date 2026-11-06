(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: sup_chain's walk on plugin-hostd/fuzz_command's ASan+UBSan build
   (fuzz_command.asan-ubsan, entry 0x8c1c4 = BASE + AF_sup_chain, 940 bytes): a Theorem Labs lane's lib/B/Prog/sup_chain_c.v
   `tsup_chain_spec` (statement from a Theorem Labs lane f490061c104; kit from a Theorem Labs lane fc8bcbd8b42), proved over its callee and
   runtime contracts (each at every FP state, as the statement states them).

   The walk is the B re-walk of the ASan walk lib/A/Prog/sup_chain.v + sup_chain_s1 .. s8 (a working branch
   3cc8391594b), cut where the A walk cuts it, at B's addresses:
   - sup_chain_s2.v `scb_head`: entry 0x8c1c4 to the loop head 0x8c3d0 (prologue and realignment, the class-1
     side-stack frame by __asan_stack_malloc_1, record (17), xmalloc (12n + 1), the two inlined arg_i (snprintf into
     the frame, arg_s), list[0] = 0 with its store1 check refuted, the loop set-up);
   - sup_chain_s3.v `scb_loop`: the loop 0x8c3d0 .. 0x8c444 (four UBSan checks and the load4 check refuted per pass,
     sprintf of each member), by induction on the passes left;
   - sup_chain_s4.v `scb_tail`: 0x8c444 to the return (arg_s of the list text, free, rec_shape_of("chain", 5),
     answer under the live frame, the frame's release 0x8c47c .. 0x8c4e4, the epilogue);
   the interface between them is lib/B/Prog/sup_chain_d.v (scb_lctx, scb_inv, scb_postF), the callee-free helpers
   lib/B/Prog/sup_chain_aux.v. The FP state changes at each printf call; every segment is stated at its own FP state
   with rounding mode 0 and the entry's f registers kept but f10 (scb_frm0, scb_fxok), and scb_postF_baseF turns the
   tail's post into apost_baseF at the entry's FP state.

   Walk hypotheses (a Theorem Labs lane convention: a fact a Theorem Labs lane states only at the pinned image is a hypothesis under its
   lemma's name; lib/B/Prog/SupChainClosed.v discharges them at PB_cmd): HB, MTL, MTLF, cmd_sig_prog_PB, cmd_palib,
   cmd_palibf, cmd_img_facts_tfib, cmd_frame_flag_law. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo CmdPaLib PaLibF CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c xmalloc_c arg_s_c rec_shape_of_c answer_c sup_chain_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_chain_d sup_chain_s2 sup_chain_s3 sup_chain_s4.
Import ListNotations.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's (sup_chain_c.v:109-119) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis ASPRINTF : forall fx0 : YK11.FPState, @asprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_sprintf) 0xa6bf8 0x604158.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_palib : forall B0, CmdBSyms B0 -> PALib B0.
Hypothesis cmd_palibf : forall B0, CmdBSyms B0 -> PALibF B0.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Hypothesis cmd_frame_flag_law : forall B0, frame_flag_lawP SEGS B0.

Theorem tsup_chain_spec_holds : tsup_chain_spec B MT.
Proof.
intros ly S W regs mem md ch id pids ids R O HPRE HRM0 HRO HROk H10 HID H11 HPR H12 HIDS HIDR HPNZ HP4 HARR HBYTES
  HREP HFR7 HNEV HLIVE HMOK.
apply (@scb_head fx rc SK PI B MT TRECORD TXMALLOC TARG_S ASTACK_MALLOC1 ASNPRINTF VOBJS HB MTL MTLF cmd_palibf
  cmd_sig_prog_PB cmd_palib cmd_img_facts_tfib ly S W regs mem md ch id pids ids R O HPRE HRM0 HRO H10 HID H11 HPR H12
  HIDS HPNZ HP4 HARR HBYTES HREP HFR7 HNEV HLIVE HMOK).
intros fx1 WL regsL memL mdL lyL SL fpos lst bl1 Frec O1 p1 p2 F1 X1 HLC HI0.
apply (@scb_loop rc SK PI B MT ASPRINTF HB cmd_img_facts_tfib ly S W regs mem md id pids ids R O lyL SL WL memL mdL
  fpos lst bl1 Frec O1 p1 p2 (@fp_regs fx) (@fp_csr fx) HIDS HIDR HPNZ HP4 HPR HLC fx1 regsL _ F1 X1 HI0).
intros fx2 regs' mem' md' F2 X2 HIn.
eapply SRr_mono.
- exact (@scb_tail rc SK PI B MT TARG_S TREC_SHAPE_OF TANSWER AFREE_LAW AFREE4 VOBJS HB MTL MTLF cmd_sig_prog_PB
    cmd_palib cmd_img_facts_tfib cmd_frame_flag_law ly S W regs mem md ch id pids ids R O lyL SL WL memL mdL fpos lst
    bl1 Frec O1 p1 p2 (@fp_regs fx) (@fp_csr fx) fx2 regs' mem' md' HPRE HRO HID HIDS HIDR HREP HFR7 HNEV HLIVE HMOK
    HLC F2 X2 HIn).
- intros W' c' _ HP. exact (@scb_postF_baseF fx rc SK PI B _ _ regs ly S W mem md _ _ W' c' HP).
Qed.
End e.
End f.
End d.

Print Assumptions tsup_chain_spec_holds.
