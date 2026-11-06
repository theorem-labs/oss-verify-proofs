(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reply on the ASan build of plugin-hostd/fuzz_command, proving
   treply_spec (lib/A/Prog/reply_c.v) in cgif_file_fuzzer's walk style (A/ACh1.v..ACh8.v): the verified symbolic
   executor over the position-abstract listing (PaLibF's SRr_run_pi_AJ, PaCallRun's SRr_run_pi_AJ_call), the strlen
   wrapper through STRLEN and the kit's aj_art_at (PaArt.v), socket_send through its statement and the
   call rule (PaNoChain.v cl_callS_wide), and the tail jump into the free wrapper through cgif's afree04_rule (PaCall.v
   afree04_sub). reply has no inline check, no loop and no side-stack frame.
   Repaired 2026-10-29 to the statement pass: RLO/RHI fixed (CmdGlob.v
   CMD_RLO/CMD_RHI), LAWS from YG0q.AR_laws_ok, socket_send's astack_pres from the new astack_pres premise through
   the journal (YCbq.v astack_pres_journal), the text's tail word from cmd_heap_tail_vis, and the live-bytes bound of
   the post from socket_send's bound and the free (YCbq.v blocks_bytes_bsum).
   Re-pointed 2026-10-29 to the base lemmas of the record facts: cmd_heap_tail_vis
   (CmdRecImg.v), cmd_prog_unowned (CmdRecImg.v) and relro_img (CmdRecRo.v) over `SEGS B LAWS HB` and the record
   hypothesis IMG : cmd_img_facts SEGS B, in place of three Section hypotheses.
   Re-fitted 2026-10-29 to statement passes 4, 4b and 5:
   reply's post stays apost_base and no callee reaches printf (socket_send's post is apost_base), so the old
   closing stands (the case with no printf-reaching callee); the callee and runtime-entry hypotheses take every FP
   state and are used at the entry's fx (pass 4b); astack_pres is gone (pass 5): socket_send's chain at s0 =
   the text (a heap block) is achain_low, the free wrapper's chain_pre is achain_chain_pre on afn_pre's chain. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/reply.v, with its module paths and module names changed; 366 of its 450 lines of code are new or changed and 291 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/reac_segconf_parse.v, with its module paths and module names changed; 23 of its 56 lines of code are new or changed and 417 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment A8a of reac_segconf_parse_file's walk, the theorem
   pf_a8a_holds : S_A8a B of lib/A/Prog/pf_pieces.v (SEG 0x887a4 -> NEW 0x8890c, FOUND 0x88964 or CLR 0x880fc).
   Segment A8a's proof, by the G3 walk owner, 2026-10-30. The pieces:
     pf_a8a_k.v  the kit: the seg_get spine, a8c (the facts every point of A8a has) and its keep, the internal cuts
                 a8L (the search loop's head 0x887d0 after j entries) and a8F (0x887f0, no entry has the name)
     pf_a8a_s.v  a8_seg_main (SEG -> NEW when c->n = 0, else the loop head with j = 0; check #29),
                 a8_loop_step / a8_loop_all (the strcmp search, FOUND on a match, 0x887f0 after the last entry)
     pf_a8a_r.v  a8_kf_main (0x887f0 -> NEW when n < 32, else check #30, c->overflow++ and the refuse call,
                 then CLR at the FP state refuse returned)
   The Section hypotheses are the callee texts pf_pieces.v's list names for A8a (strcmp, refuse), the record fact
   TL (PALib: the errno cell lies outside every footprint, for the strcmp call), the listing's facts SIGP (the
   call target pa_sigma SS_refuse) and OBJ (the literal F_bound's object atom at 0x88818), and the two the lead
   allows only at the rebuild after a refuse call (VRO, SSPX). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegAddr SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a8a_k pf_a8a_s pf_a8a_r.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
(* the strcmp wrapper at 0x887d8 (pf_pieces.v's list: RtString.astrcmp_realizes, row 17) *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
(* refuse at 0x88834 (pf_pieces.v's list: refuse_contract at BASE + AF_refuse and image A's numbers) *)
Hypothesis REF : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B
  (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance (SegObj.v): the call target pa_sigma SS_refuse =
   BASE + AF_refuse, and the object atom of 0x88818's auipc / addi pair (a2 = seg_litA_rc F_bound) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* ONLY for pf_a6_k.a6_base_move after the refuse call (the lead's rule, 2026-10-30): refuse's post gives only its
   journal; the journal keeps an image byte only when it is not in as_owned_static B (YCbq.v:479), and whether the
   GOT word 0xa36d8 and the guard 0x5ff078 are owned statics is a record fact of listing stage 2
   (SegRecCells.seg_rec_cells); arodata_okP after refuse needs pa_relro_img, which is VRO *)
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Theorem pf_a8a_holds : S_A8a B.
Proof.
unfold S_A8a. intros f0 n HNEW HFOUND HCLR.
apply (a8_seg_main (fx := f0) B TL n HNEW).
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HL.
apply (a8_loop_all (fx := f0) B TL ASTRCMP n v pos lyc Sc Wc cf nm o ln d np name HFOUND
  (fun rX' memc' mdc' HF => a8_kf_main (fx := f0) B REF SIGP OBJ VRO SSPX n HNEW HCLR v pos lyc Sc Wc rX' memc' mdc'
     cf nm o ln d np name HF)
  (length (rc_seg cf)) 0 ltac:(lia) rX memc mdc HL).
Qed.
End e.
End f.
End d.
