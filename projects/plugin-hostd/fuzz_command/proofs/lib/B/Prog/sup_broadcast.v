(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of sup_broadcast on the ASan+UBSan build of plugin-hostd/fuzz_command
   (fuzz_command.asan-ubsan, 0x8b4f0, 19 instructions), proving tsup_broadcast_spec of sup_broadcast_c.v (the B
   statement at pass 5): the B twin of a Theorem Labs lane's A walk (lib/A/Prog/sup_broadcast.v at a5a5ff08765). B keeps record()
   as a function, so the walk is three straight-line runs and three calls:
     sup_broadcast_s4.v  0x8b4f0 .. `jal record`, record (cl_callS_pg), the return 0x8b50c;
     sup_broadcast_s5.v  0x8b50c .. `jal arg_line`, arg_line (cl_callS_pg), the return 0x8b518;
     sup_broadcast_s6.v  0x8b518 .. `j answer`, the tail call of answer (PaFx.v cl_callS_pgF) and the post.
   The stage interfaces are sup_broadcast_s3.v's; the recorder after each call is record_c.v's post and RecBridge.v's
   rec_bridge_slot / rec_bridge_add / rec_slot_entry; the block bookkeeping is sup_broadcast_s2.v's. The frame chains
   at the calls (PASS4-REFIT.md section B): s0 = the line, a heap block below alloc_ceiling, at record and arg_line
   (achain_low); at the tail jump s0 is the entry's and answer's chain is afn_pre's (achain_kept, achain_ly_top).
   The per-binary facts are Section hypotheses under the names of a Theorem Labs lane's RULING-STMT.md section 1: HB, LAWS, MTL,
   SIGP, IMG (cmd_img_facts: cif_prog_img, cif_prog_not_ro, cif_relro_img, cif_ro_unowned, CmdRecRo's
   cmd_ro_in_img, cmd_ro_obj_bytes, cmd_ro_ok_of_aro, CmdRecImg's cmd_prog_unowned); TRECORD, TARG_LINE, TANSWER and
   VOBJS are the statement's own. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_line_c answer_c sup_broadcast_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_broadcast_s1 sup_broadcast_s3 sup_broadcast_s4 sup_broadcast_s5 sup_broadcast_s6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's hypotheses (sup_broadcast_c.v:68-71) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.

Theorem tsup_broadcast_spec_holds : tsup_broadcast_spec B MT.
Proof.
unfold tsup_broadcast_spec.
intros ly S W regs mem md ch pl line R O. cbv zeta.
intros HPRE HFRM Hfr8 HROD _ H10 Hpl (HBLK & HAP & HSTR & HLEN) HREC Hev Hlive HMOK.
pose proof (conj HPRE (conj HFRM (conj Hfr8 (conj HROD (conj H10 (conj Hpl (conj HBLK (conj HAP (conj HSTR (conj HLEN
  (conj HREC (conj Hev (conj Hlive HMOK))))))))))))) as HENT.
change (sbb_ent B MT ly S W regs mem md ch pl line R O) in HENT.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
destruct sbb_stk as (WSTK & _).
assert (Hsp32 : 32 <= spZ regs) by lia.
change (SRr SEGS W (cfg_at SEGS (BASE + AF_sup_broadcast) regs mem md)
  (apost_baseF SEGS B SUP_BROADCAST_STK (sb_FP O) regs ly S W mem md (EV_SUP_BROADCAST R) (sb_post B MT ly S R line O))).
(* 0x8b4f0 .. `jal record` *)
apply (sbb_reach_rec B LAWS ly S W regs mem md ch O _ HPRE).
intros regsX memX mdX HJX HspX X1 X8 X10 XCS XF XKEEP.
pose proof (sbb_at_rec_of B MT LAWS IMG ly S W regs mem md ch pl line R O regsX memX mdX HENT HJX HspX X1 X8 X10 XCS
  XF XKEEP) as HATR.
(* the call of record, and its return 0x8b50c *)
eapply SRr_bind; [exact (sbb_call_record B MT HB LAWS MTL SIGP IMG TRECORD ly S W regs mem md ch pl line R O regsX memX mdX
  HENT HATR)|].
intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HJ1c & HP1 & HQ1).
destruct (sbb_ret_rec_of B MT HB LAWS IMG ly S W regs mem md ch pl line R O regsX memX mdX ly1 S1 W1 regs1 mem1 md1
  HENT HATR HJ1 HJ1c HP1 HQ1) as (F & O1 & HRR).
pose proof HRR as (HJR & _).
(* 0x8b50c .. `jal arg_line` *)
apply (sbb_reach_al B LAWS ly S W regs mem md O ly1 S1 W1 regs1 mem1 md1 _ _ HJR).
intros regsY memY mdY HJY Y1 Y9 Y11 YR YKEEP.
pose proof (sbb_at_al_of B MT ly S W regs mem md ch pl line R O ly1 S1 W1 regs1 mem1 md1 F O1 regsY memY mdY HENT HRR
  HJY Y1 Y9 Y11 YR YKEEP) as HATA.
(* the call of arg_line, and its return 0x8b518 *)
eapply SRr_bind; [exact (sbb_call_arg_line B MT HB LAWS MTL SIGP IMG TARG_LINE ly S W regs mem md ch pl line R O
  ly1 S1 W1 regsY memY mdY F O1 HENT HATA)|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 & HQ2).
destruct (sbb_ret_al_of B MT HB LAWS MTL IMG ly S W regs mem md ch pl line R O ly1 S1 W1 regsY memY mdY F O1
  ly2 S2 W2 regs2 mem2 md2 HENT HATA HJ2 HJ2c HP2 HQ2) as (p & HRA).
pose proof HRA as (HJA & HspA & A9 & _ & HFA & _).
(* 0x8b518 .. `j answer` *)
apply (sbb_reach_tail B LAWS VOBJS ly S W regs mem md O ly2 S2 W2 regs2 mem2 md2 _ (rec_slot R) _ HJA HspA Hsp32 A9 HFA).
intros regsT memT mdT HJT T1 T2 T8 T9 T10 T11 T12 TR TKEEP.
destruct (sbb_at_ans_of B MT HB LAWS MTL IMG ly S W regs mem md ch pl line R O ly1 S1 F O1 ly2 S2 W2 regs2 mem2 md2 p
  regsT memT mdT HENT HRA HJT T1 T2 T8 T9 T10 T11 T12 TR TKEEP) as (old & HATN).
(* the tail call of answer, and the post *)
eapply SRr_mono; [exact (sbb_call_answer B MT HB LAWS SIGP IMG TANSWER ly S W regs mem md ch pl line R O ly1 S1 F O1
  ly2 S2 W2 regsT memT mdT p old HENT HATN)|].
intros W3 c3 _ HPOST.
exact (sbb_final B MT LAWS MTL ly S W regs mem md ch pl line R O ly1 S1 F O1 ly2 S2 W2 regsT memT mdT p old W3 c3
  HENT HATN HPOST).
Qed.

End e.
End f.
End d.
