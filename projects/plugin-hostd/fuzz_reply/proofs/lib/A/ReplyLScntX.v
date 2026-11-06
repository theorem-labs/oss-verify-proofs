(* SEG_EXIT's LS_cnt row over the CLOSED operation range 0 <= t <= OPS_MAX (a Theorem Labs lane 05:37Z, W8: the exit cut holds
   only lregs_X's `0 <= t <= OPS_MAX`, and t = OPS_MAX = 512 reaches X from the latch).  ReplyLScnt.v's
   fr_LS3cp_cnt_exit and ReplyLScntRP.v's rp_cnt_exit_rf / rp_cnt_exit_later take `0 <= t < OPS_MAX`; their room bounds
   (ReplyTrPeakCnt.tc_sec_cut, ReplyLS3p.MARGIN / MARGIN24) are stated at t <= 511 and |es| <= 16.  This file re-derives
   them at t <= 512 with |es| <= 4 (fr_RINV's four slots, fr_RINV_es_le) and proves the three rows over the closed range:
   fr_LS3cp_cnt_exit_c, rp_cnt_exit_rf_c, rp_cnt_exit_later_c.  proves no function (kind: invariant lemma).

   THE ROOM AT t = 512 (SEG_EXIT's peak is the constant 5, relay_finish's rf_pk):
   - secondary: ReplyLSCntM.fr_LS3c_sec_cut gives cnt_sec <= t + |es| + 3 |hs| + 2 + SEC0 <= 512 + 4 + 12 + 2 + 64 = 594
     (lsx_sec_cut; 593 at t = 511), and 594 + 5 <= 1,024: 425 left;
   - class c (1..30): ReplyLS3p.fr_LS3cp_cls_cut gives pt_s c * (cnt - X) + pt_v c * mass <= pt_v c * WRITE_MAX * t with
     X = CLS0 + 1 + 18 + 2 |es| + t <= CUT_X5 := 64 + 1 + 18 + 8 + 512 = 603.  The mass only lowers cnt, so at mass 0
     cnt + MARGIN5 c <= RL_PRIM c, MARGIN5 c := RL_PRIM c - (603 + pt_v c * (WRITE_MAX * 512) / pt_s c) (lsx_cls_cut).
     MARGIN5_table: class 1 has 67,108,864 - (603 + 2 * 65,535 * 512) = 421, every other class at least 30,074; so the
     constant peak 5 leaves at least 416 in class 1;
   - class 24 against 2^15: MARGIN24_5 = 2^15 - (603 + 3 * 65,535 * 512 / 5,889) = 15,072 (lsx_c24_cut); 15,067 left.
   No row is false at t = OPS_MAX.  A larger peak would be: class 1 has room for a constant peak of at most 421 there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSRemove3 ReplyLSRrPre ReplyLSDrain3 ReplyLSEvent3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyLS3cArms ReplyTrPeakW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSCntM ReplyLS3p ReplyTrPeakCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLScnt ReplyLScntRP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
(* roomp / cnt_ok_pk: lib/A/W_journal_x.v; the peaks rf_pk / cshe_pk / sr_pk: lib/A/W_contract_x.v *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract_x.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== the room at t <= 512, |es| <= 4 *)
Definition CUT_X5 : Z := CLS0 + 1 + 18 + 2 * 4 + 512.
Definition MARGIN5 (c : Z) : Z := RL_PRIM c - (CUT_X5 + pt_v c * (SlotInv.WRITE_MAX * 512) / pt_s c).
Definition MARGIN24_5 : Z := 2 ^ 15 - (CUT_X5 + pt_v 24 * (SlotInv.WRITE_MAX * 512) / pt_s 24).

Lemma CUT_X5_val : CUT_X5 = 603.
Proof. reflexivity. Qed.
Lemma MARGIN5_table : map MARGIN5 (map Z.of_nat (seq 1 30)) =
  [421; 27162607; 20314697; 15227971; 13419634; 10146457; 8806054; 7762777; 6934374; 6262898; 5708522; 5243492;
   4848029; 4507727; 4211862; 3952306; 2571408; 1939511; 1285278; 976532; 646047; 489505; 323561; 244448; 161477;
   122104; 80537; 60751; 39967; 30074].
Proof. vm_compute. reflexivity. Qed.
Lemma MARGIN5_min : forall c, 1 <= c <= 30 -> 421 <= MARGIN5 c.
Proof.
  intros c Hc.
  assert (E : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/
              c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/
              c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  repeat (destruct E as [-> | E]; [apply Z.leb_le; vm_compute; reflexivity |]).
  subst c. apply Z.leb_le; vm_compute; reflexivity.
Qed.
Lemma MARGIN24_5_val : MARGIN24_5 = 15072.
Proof. vm_compute. reflexivity. Qed.

(* the cut's potential at t <= 512: the count past X <= CUT_X5 is paid by pt_v c * WRITE_MAX * 512 *)
Lemma lsx_room_gen : forall LIM c cnt X ms t, 0 <= t <= 512 -> X <= CUT_X5 -> 0 <= ms ->
  pt_s c * (cnt - X) + pt_v c * ms <= pt_v c * (SlotInv.WRITE_MAX * t) ->
  cnt + (LIM - (CUT_X5 + pt_v c * (SlotInv.WRITE_MAX * 512) / pt_s c)) <= LIM.
Proof.
  intros LIM c cnt X ms t Ht HX Hms Hc. pose proof (pt_s_ge c) as Hs. pose proof (pt_v_range c) as Hv.
  assert (A : pt_v c * (SlotInv.WRITE_MAX * t) <= pt_v c * (SlotInv.WRITE_MAX * 512))
    by (apply Z.mul_le_mono_nonneg_l; [lia | unfold SlotInv.WRITE_MAX; lia]).
  assert (M : 0 <= pt_v c * ms) by (apply Z.mul_nonneg_nonneg; lia).
  assert (B0 : pt_s c * (cnt - CUT_X5) <= pt_v c * (SlotInv.WRITE_MAX * 512)).
  { assert (pt_s c * (cnt - CUT_X5) <= pt_s c * (cnt - X)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  assert (C : cnt - CUT_X5 <= pt_v c * (SlotInv.WRITE_MAX * 512) / pt_s c) by (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

Section x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* the secondary count at a cut with t <= 512: at most 594 *)
Lemma lsx_sec_cut : forall cx t m ly S, fr_LS3c B cx t m ly S -> ReplyCnt.msz_ok (lm_es m) (lm_hs m) ->
  fr_RINV cx t m -> 0 <= t <= OPS_MAX -> ReplyCnt.cnt_sec (ablocks B ly S) <= 594.
Proof.
  intros cx t m ly S HLS Hm HRI Ht.
  pose proof (ReplyLSCntM.fr_LS3c_sec_cut B cx t m ly S HLS Hm) as C.
  pose proof (fr_RINV_es_le cx t m HRI) as E4.
  pose proof HRI as (_ & (Hhs & _) & _).
  assert (Z.of_nat (length (lm_hs m)) = 4) by (rewrite Hhs; reflexivity).
  unfold ReplyCnt.SEC0, OPS_MAX in *. lia.
Qed.
(* a primary class's count at a cut with t <= 512 *)
Lemma lsx_cls_cut : forall cx t m ly S c, fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> 0 <= t <= OPS_MAX ->
  ReplyCnt.cnt_cls c (ablocks B ly S) + MARGIN5 c <= RL_PRIM c.
Proof.
  intros cx t m ly S c H HRI Ht. pose proof (fr_LS3cp_cls_cut B cx t m ly S c H) as Hc.
  pose proof (fr_RINV_es_le cx t m HRI) as E4. pose proof (pt_mass_nonneg m). unfold OPS_MAX in Ht.
  unfold MARGIN5.
  apply (lsx_room_gen (RL_PRIM c) c _ (CLS0 + 1 + 18 + 2 * Z.of_nat (length (lm_es m)) + t) (pt_mass m) t);
    [lia | unfold CUT_X5; lia | lia | exact Hc].
Qed.
(* class 24 against 2^15 at a cut with t <= 512 *)
Lemma lsx_c24_cut : forall cx t m ly S, fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> 0 <= t <= OPS_MAX ->
  ReplyCnt.cnt24 (ablocks B ly S) + MARGIN24_5 <= 2 ^ 15.
Proof.
  intros cx t m ly S H HRI Ht. pose proof (fr_LS3cp_cls_cut B cx t m ly S 24 H) as Hc.
  pose proof (fr_RINV_es_le cx t m HRI) as E4. pose proof (pt_mass_nonneg m). unfold OPS_MAX in Ht.
  unfold MARGIN24_5, ReplyCnt.cnt24. change PresetRoom.K_BATCH_CLASS with 24.
  apply (lsx_room_gen (2 ^ 15) 24 _ (CLS0 + 1 + 18 + 2 * Z.of_nat (length (lm_es m)) + t) (pt_mass m) t);
    [lia | unfold CUT_X5; lia | lia | exact Hc].
Qed.

(* ================================================================== SEG_EXIT's row, closed range *)
(* ReplyLScnt.v fr_LS3cp_cnt_exit over 0 <= t <= OPS_MAX *)
Lemma fr_LS3cp_cnt_exit_c : forall cx t m ly S,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t <= OPS_MAX ->
  (acnt Psec (ablocks B ly S) + pk_exit Psec <= Lsec)%nat /\ (acnt P24 (ablocks B ly S) + pk_exit P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_exit (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S HLS HRI Hm Ht. unfold pk_exit.
  split; [|split].
  - pose proof (lsx_sec_cut cx t m ly S (proj1 HLS) Hm HRI Ht) as C.
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, lsc_Lsec.
    change (Z.of_nat (acnt Psec (ablocks B ly S))) with (ReplyCnt.cnt_sec (ablocks B ly S)). lia.
  - pose proof (lsx_c24_cut cx t m ly S HLS HRI Ht) as C. rewrite MARGIN24_5_val in C.
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, lsc_L24.
    change (Z.of_nat (acnt P24 (ablocks B ly S))) with (ReplyCnt.cnt24 (ablocks B ly S)). lia.
  - intros c Hc1. pose proof (lsx_cls_cut cx t m ly S c HLS HRI Ht) as C. pose proof (MARGIN5_min c Hc1) as M.
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, (lsc_LPRIM c Hc1).
    change (Z.of_nat (acnt (Pcls c) (ablocks B ly S))) with (ReplyCnt.cnt_cls c (ablocks B ly S)).
    change (ReplyLS3p.RL_PRIM c) with (ReplyCnt.RL_PRIM c). lia.
Qed.
End x.

Section xrp.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable RP : roomp.
Hypothesis HRP_CNT : RP_CNT RP.
(* ReplyLScntRP.v rp_cnt_exit_rf over 0 <= t <= OPS_MAX: relay_finish's call at the cut *)
Lemma rp_cnt_exit_rf_c : forall cx t m ly S,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t <= OPS_MAX ->
  cnt_ok_pk RP rf_pk (ablocks B ly S).
Proof.
  intros cx t m ly S HLS HRI Hm Ht. apply (lsc_rp_of_acnt RP HRP_CNT).
  exact (fr_LS3cp_cnt_exit_c B cx t m ly S HLS HRI Hm Ht).
Qed.
(* ReplyLScntRP.v rp_cnt_exit_later over 0 <= t <= OPS_MAX: check_shape_ends' and source_reset's calls at a later
   state, relay_finish having grown each count by at most rf_pk *)
Lemma rp_cnt_exit_later_c : forall cx t m ly S (lyx : alayout) (Sx : astate),
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t <= OPS_MAX ->
  (forall P, (acnt P (ablocks B lyx Sx) <= acnt P (ablocks B ly S) + rf_pk P)%nat) ->
  cnt_ok_pk RP cshe_pk (ablocks B lyx Sx) /\ cnt_ok_pk RP sr_pk (ablocks B lyx Sx).
Proof.
  intros cx t m ly S lyx Sx HLS HRI Hm Ht HG.
  pose proof (fr_LS3cp_cnt_exit_c B cx t m ly S HLS HRI Hm Ht) as R.
  split; apply (lsc_rp_mono RP HRP_CNT pk_exit _ (ablocks B ly S) _ R); intros P; specialize (HG P);
    unfold cshe_pk, sr_pk, rf_pk, pk_exit in *; lia.
Qed.
End xrp.
