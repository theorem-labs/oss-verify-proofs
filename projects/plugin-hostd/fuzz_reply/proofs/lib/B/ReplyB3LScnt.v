(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_gone_base_x.v, with its module paths and module names changed; 445 of its 513 lines of code are new or changed and 590 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyRINVB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  ReplyB3Base ReplyB3LS3 ReplyLSBDrainPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  ReplyB3LS3Arms ReplyLSCntL ReplyB3LS3c ReplyB3LS3cArms ReplyTrPeakW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3LSCntL.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  ReplyB3LSCntM ReplyB3LS3p ReplyB3TrPeakCnt ReplyB3TrPeakCntR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3TrPeakCnl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
  W_LLVMFuzzerTestOneInput_remove W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation wr_n := W_LLVMFuzzerTestOneInput_write.wr_n.
Local Notation wr_pick := W_LLVMFuzzerTestOneInput_write.wr_pick.
Local Notation rm_ent := W_LLVMFuzzerTestOneInput_remove.rm_ent.
Local Notation rm_at := W_LLVMFuzzerTestOneInput_remove.rm_at.
Local Notation gn_id := W_LLVMFuzzerTestOneInput_gone_base.gn_id.
Local Notation gn_pair_ok := W_LLVMFuzzerTestOneInput_gone_base.gn_pair_ok.
Local Notation gn_pairs := W_LLVMFuzzerTestOneInput_gone_base.gn_pairs.

Definition zn (b : bool) : nat := if b then 1%nat else 0%nat.
Definition pk_oa (P : Z -> bool) : nat := (zn (P ATABLE) + zn (P APARTIAL))%nat.
Definition pk_lp (l : hlist) (n : Z) : (Z -> bool) -> nat :=
  fun P => ((if P (lp_vbytes l) && lp_grow l then 1 else 0) + (if P (n + 1)%Z then 1 else 0))%nat.
Definition pk_event (e : list byte) (P : Z -> bool) : nat := (zn (P (re_len e)) + 2)%nat.
Definition pk_exit (P : Z -> bool) : nat := 5%nat.

Definition lsc_pq (p : rentry * (hsrc * nat)) : Prop :=
  re_eof (fst p) = 0 ->
    (re_skip (fst p) = 0 \/ re_skip (fst p) = 1) /\ re_skip (fst p) = hs_overlong (fst (snd p)) /\
    (re_skip (fst p) = 0 -> bzs (re_U (fst p)) = bzs (hs_W (fst (snd p)))) /\
    Z.of_nat (length (re_U (fst p))) <= APARTIAL /\ 0 <= hs_off (fst (snd p)).
Definition pk_drain (m : lmod) (h : hsrc) (j : nat) (P : Z -> bool) : nat :=
  (Z.to_nat (tr_peakP P (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                         (nth j (lm_es m) dr_e0) h)) +
   (cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P + 2))%nat.
Definition pk_rm (m : lmod) (h : hsrc) (j0 : nat) (P : Z -> bool) : nat :=
  (Z.to_nat (tr_peakP P (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) +
   (if (re_eof (rm_ent m j0) =? 0)%Z then cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P else 0) + 4)%nat.
Definition gn_cnl (P : Z -> bool) (p : rentry * (hsrc * nat)) : nat :=
  if re_eof (fst p) =? 0 then cnl_pk (hs_held (fst (snd p))) (map (map (Z_to_bv 8)) (dr_lines (fst (snd p)))) P
  else 0%nat.

Lemma zn_le1 : forall b, (zn b <= 1)%nat.
Proof. intros [|]; cbn; lia. Qed.

Section lsc.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable CALL_ROOM_B : Z.

Lemma lsc_RL_pos : forall c, 1 <= c <= 30 -> 30055 <= RL_PRIM c.
Proof.
  intros c Hc. pose proof (MARGIN_min c Hc) as M. unfold MARGIN in M.
  assert (D : 0 <= pt_v c * (SlotInv.WRITE_MAX * 511) / pt_s c).
  { pose proof (pt_s_ge c). pose proof (pt_v_range c). apply Z.div_pos; [|lia].
    apply Z.mul_nonneg_nonneg; [lia | unfold SlotInv.WRITE_MAX; lia]. }
  assert (CX : CUT_X = 626) by reflexivity.
  change (ReplyCnt.RL_PRIM c) with (ReplyB3LS3p.RL_PRIM c). lia.
Qed.
Lemma lsc_LPRIM : forall c, 1 <= c <= 30 -> Z.of_nat (LPRIM c) = ReplyB3LS3p.RL_PRIM c.
Proof.
  intros c Hc. pose proof (lsc_RL_pos c Hc). unfold LPRIM. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma lsc_L24 : Z.of_nat L24 = 2 ^ 15.
Proof. unfold L24. rewrite Z2Nat.id by lia. reflexivity. Qed.
Lemma lsc_Lsec : Z.of_nat Lsec = 1024.
Proof. reflexivity. Qed.

Lemma lsc_room : forall cx t m ly S (PK : (Z -> bool) -> nat) K24 Kc,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (PK Psec) <= 431 ->
  K24 <= 15083 -> pt_s 24 * (Z.of_nat (PK P24) - K24) <= pt_v 24 * pt_mass m ->
  Kc <= 30055 -> (forall c, 1 <= c <= 30 -> pt_s c * (Z.of_nat (PK (Pcls c)) - Kc) <= pt_v c * pt_mass m) ->
  (acnt Psec (ablocks B ly S) + PK Psec <= Lsec)%nat /\ (acnt P24 (ablocks B ly S) + PK P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + PK (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S PK K24 Kc HLS HRI Hm Ht Hs H24k H24 Hck Hc.
  pose proof (fr_RINV_es_le cx t m HRI) as E4.
  assert (Ht' : 0 <= t <= 511) by (unfold OPS_MAX in Ht; lia).
  assert (E16 : (length (lm_es m) <= 16)%nat) by lia.
  split; [|split].
  - pose proof (tc_sec_cut B CALL_ROOM_B cx t m ly S (proj1 HLS) Hm HRI Ht) as C.
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, lsc_Lsec.
    change (Z.of_nat (acnt Psec (ablocks B ly S))) with (ReplyCnt.cnt_sec (ablocks B ly S)). lia.
  - pose proof (fr_LS3cp_c24_room B CALL_ROOM_B cx t m ly S _ HLS Ht' E16 H24) as C. rewrite MARGIN24_val in C.
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, lsc_L24.
    change (Z.of_nat (acnt P24 (ablocks B ly S))) with (ReplyB3LSCntL.cnt24 (ablocks B ly S)). lia.
  - intros c Hc1. pose proof (fr_LS3cp_cls_room B CALL_ROOM_B cx t m ly S c _ HLS Ht' E16 (Hc c Hc1)) as C.
    pose proof (MARGIN_min c Hc1) as M.
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, (lsc_LPRIM c Hc1).
    change (Z.of_nat (acnt (Pcls c) (ablocks B ly S))) with (ReplyB3LSCntL.cnt_cls c (ablocks B ly S)). lia.
Qed.
Lemma lsc_room_const : forall cx t m ly S (PK : (Z -> bool) -> nat) (K : nat),
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  (K <= 431)%nat -> (forall P, (PK P <= K)%nat) ->
  (acnt Psec (ablocks B ly S) + PK Psec <= Lsec)%nat /\ (acnt P24 (ablocks B ly S) + PK P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + PK (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S PK K HLS HRI Hm Ht HK HP.
  pose proof (pt_mass_nonneg m) as Hms.
  assert (G : forall c, pt_s c * (Z.of_nat (PK (Pcls c)) - Z.of_nat K) <= pt_v c * pt_mass m).
  { intros c. pose proof (HP (Pcls c)). pose proof (pt_s_ge c). pose proof (pt_v_range c). nia. }
  apply (lsc_room cx t m ly S PK (Z.of_nat K) (Z.of_nat K) HLS HRI Hm Ht).
  - pose proof (HP Psec). lia.
  - lia.
  - pose proof (HP P24). pose proof (pt_s_ge 24). pose proof (pt_v_range 24). nia.
  - lia.
  - intros c _. apply G.
Qed.

Lemma fr_LS3cp_cnt_add : forall cx t m ly S,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> ad_at_op cx m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  (acnt Psec (ablocks B ly S) + pk_oa Psec <= Lsec)%nat /\ (acnt P24 (ablocks B ly S) + pk_oa P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_oa (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S HLS HRI _ Hm Ht. apply (lsc_room_const cx t m ly S pk_oa 2 HLS HRI Hm Ht); [lia|].
  intros P. unfold pk_oa. pose proof (zn_le1 (P ATABLE)). pose proof (zn_le1 (P APARTIAL)). lia.
Qed.
Lemma fr_LS3cp_cnt_write : forall cx t m si h ly S,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> wr_pick cx m si h -> 0 < wr_n cx m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  (acnt Psec (ablocks B ly S) + pk_lp (hs_pending h) (wr_n cx m) Psec <= Lsec)%nat /\
  (acnt P24 (ablocks B ly S) + pk_lp (hs_pending h) (wr_n cx m) P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 ->
     (acnt (Pcls c) (ablocks B ly S) + pk_lp (hs_pending h) (wr_n cx m) (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m si h ly S HLS HRI _ _ Hm Ht. apply (lsc_room_const cx t m ly S _ 2 HLS HRI Hm Ht); [lia|].
  intros P. unfold pk_lp. destruct (P (lp_vbytes (hs_pending h)) && lp_grow (hs_pending h));
    destruct (P (wr_n cx m + 1)); lia.
Qed.
Lemma fr_LS3cp_cnt_event : forall cx t m ly S e,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  (acnt Psec (ablocks B ly S) + pk_event e Psec <= Lsec)%nat /\
  (acnt P24 (ablocks B ly S) + pk_event e P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_event e (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S e HLS HRI _ Hm Ht. apply (lsc_room_const cx t m ly S _ 3 HLS HRI Hm Ht); [lia|].
  intros P. unfold pk_event. pose proof (zn_le1 (P (re_len e))). lia.
Qed.
Lemma fr_LS3cp_cnt_exit : forall cx t m ly S,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  (acnt Psec (ablocks B ly S) + pk_exit Psec <= Lsec)%nat /\ (acnt P24 (ablocks B ly S) + pk_exit P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_exit (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S HLS HRI Hm Ht. apply (lsc_room_const cx t m ly S _ 5 HLS HRI Hm Ht); [lia|].
  intros P. unfold pk_exit. lia.
Qed.

Lemma lsc_kept_le : forall (P : Z -> bool) (cx : lfcx (rc := rc)) T cap out,
  (acnt P (xcnt_kept (input_blks cx) T cap out) <= 3)%nat.
Proof.
  intros P cx T cap out. unfold xcnt_kept, input_blks, aout_blks. rewrite !acnt_app.
  assert (A1 : forall (b : bool) (x : Z * Z), (acnt P (if b then [] else [x]) <= 1)%nat).
  { intros [|] [a n]; unfold acnt; cbn [map List.filter snd]; [cbn; lia|]. destruct (P n); cbn; lia. }
  pose proof (A1 (c_n cx =? 0) (c_p cx, c_n cx)). pose proof (A1 (T =? 0) (T, ATABLE)).
  pose proof (A1 (cap =? 0) (out, cap)). lia.
Qed.
Lemma fr_cnt_pro : forall (cx : lfcx (rc := rc)) T cap out (S2 : astate),
  xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T cap out ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) ->
  (acnt Psec (ablocks B (c_ly cx) S2) + pk_oa Psec <= Lsec)%nat /\
  (acnt P24 (ablocks B (c_ly cx) S2) + pk_oa P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B (c_ly cx) S2) + pk_oa (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx T cap out S2 (X1 & X2) E. rewrite E.
  assert (PO : forall P, (pk_oa P <= 2)%nat).
  { intros P. unfold pk_oa. pose proof (zn_le1 (P ATABLE)). pose proof (zn_le1 (P APARTIAL)). lia. }
  unfold cnt_sec, cnt_cls, SEC0, CLS0 in *.
  split; [|split].
  - pose proof (lsc_kept_le Psec cx T cap out). pose proof (PO Psec).
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, lsc_Lsec. lia.
  - pose proof (X2 kBatchClass ltac:(change kBatchClass with 24; lia)) as X.
    pose proof (lsc_kept_le P24 cx T cap out). pose proof (PO P24).
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, lsc_L24. unfold P24 in *. lia.
  - intros c Hc. pose proof (X2 c Hc). pose proof (lsc_kept_le (Pcls c) cx T cap out). pose proof (PO (Pcls c)).
    pose proof (lsc_RL_pos c Hc).
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, (lsc_LPRIM c Hc).
    change (ReplyB3LS3p.RL_PRIM c) with (ReplyCnt.RL_PRIM c). lia.
Qed.

Lemma lsc_cnl_call : forall (j : nat) (nm : Z -> RelayRunT.addr YO0i.sptr) (h h'' : hsrc) (P : Z -> bool),
  hl_recs (hs_expected h) = [] ->
  map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  Z.to_nat (tr_peakP P (HarnessTr.check_no_loss_tr j (ListTr.sh_of nm (hs_held h''))
                          (map (ListTr.shr nm) (hl_recs (hs_expected h''))))) =
  cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P.
Proof.
  intros j nm h h'' P E0 Ex Eh. unfold cnl_pk. rewrite cnl_tr_names, Ex, E0, Eh. reflexivity.
Qed.

Lemma lsc_w_cls : forall (X : Type) c (tr : list (RelayRunT.rev X)),
  tr_peakP (Pcls c) tr = ReplyTrPeakW.tr_peak_w (w_cls c) tr.
Proof. intros. rewrite tr_peakP_w. reflexivity. Qed.
Lemma lsc_w_sec : forall (X : Type) (tr : list (RelayRunT.rev X)), tr_peakP Psec tr = ReplyTrPeakW.tr_peak_w w_sec tr.
Proof. intros. rewrite tr_peakP_w. reflexivity. Qed.

Lemma lsc_pay : forall c X Y K1 K2 D PB M, 1 <= c <= 30 -> 0 <= PB <= M ->
  (c = 1 -> 21 * (X - K1) <= 22 * PB) -> (c <> 1 -> PresetRoom.lo c * (X - K1) <= 2 * PB) ->
  pt_s c * (Y - K2) <= PB ->
  pt_s c * (X + Y + D - (K1 + K2 + D)) <= pt_v c * M.
Proof.
  intros c X Y K1 K2 D PB M Hc HPB H1 Hn HY.
  replace (X + Y + D - (K1 + K2 + D)) with (X + Y - (K1 + K2)) by ring.
  destruct (Z.eq_dec c 1) as [->|N1]; [|destruct (Z.eq_dec c 2) as [->|N2]].
  - specialize (H1 eq_refl). assert (E : PresetRoom.lo 1 = 1) by (vm_compute; reflexivity).
    assert (Es : pt_s 1 = 21) by (unfold pt_s; rewrite E; reflexivity). assert (Ev : pt_v 1 = 42) by reflexivity.
    rewrite Es, Ev in *. lia.
  - specialize (Hn ltac:(lia)). assert (E : PresetRoom.lo 2 = 17) by (vm_compute; reflexivity).
    assert (Es : pt_s 2 = 21) by (unfold pt_s; rewrite E; reflexivity). assert (Ev : pt_v 2 = 4) by reflexivity.
    rewrite E in Hn. rewrite Es, Ev in *. lia.
  - specialize (Hn N1). pose proof (lo_ge21 c ltac:(lia)) as L.
    assert (Es : pt_s c = PresetRoom.lo c) by (unfold pt_s; lia).
    assert (Ev : pt_v c = 3)
      by (unfold pt_v; rewrite (proj2 (Z.eqb_neq c 1) N1), (proj2 (Z.eqb_neq c 2) N2); reflexivity).
    rewrite Es, Ev in *. nia.
Qed.

Lemma fr_LS3cp_cnt_drain : forall cx t m ly S si h j,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (acnt Psec (ablocks B ly S) + pk_drain m h j Psec <= Lsec)%nat /\
  (acnt P24 (ablocks B ly S) + pk_drain m h j P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_drain m h j (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S si h j HLS HRI _ Hpick Hj Hfdj Heof Hm Ht HU HXP Hoffs.
  destruct (dpre_pair cx t m si h j HRI Hpick Hj Hfdj) as (Hp & Hent & _).
  destruct Hp as (_ & _ & _ & Hre & _). destruct Hent as (_ & _ & _ & _ & Hsk).
  destruct (Hre Heof) as (Hov & HW).
  destruct (tc_dr_facts cx t m si h j HRI Hpick Hj Hfdj Heof HU) as (_ & Href & _ & _).
  pose proof (pair_bytes_nonneg (nth j (lm_es m) dr_e0) h) as HPB0.
  assert (HPBm : pair_bytes (nth j (lm_es m) dr_e0) h <= pt_mass m).
  { pose proof Hpick as (_ & _ & Hh).
    pose proof (pt_pair_le_mass m si h j (nth j (lm_es m) dr_e0) Hh (nth_error_nth' (lm_es m) dr_e0 Hj) Hoffs) as M.
    unfold pair_bytes. destruct (re_skip (nth j (lm_es m) dr_e0) =? 0); lia. }
  pose proof (cnl_drain_bytes _ h Hsk Hov HW) as CB.
  pose proof (cnl_pk_sec (hs_held h) _ (cnl_drain_short h Href)) as CS.
  assert (EPK : forall P, Z.of_nat (pk_drain m h j P) =
    tr_peakP P (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) +
    tr_peakP P (cnl_tr (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h))) + 2).
  { intros P. unfold pk_drain, cnl_pk. rewrite !Nat2Z.inj_add, !Z2Nat.id by apply tr_peakP_nonneg. lia. }
  apply (lsc_room cx t m ly S (pk_drain m h j) (5 + 2 + 2) (5 + 2 + 2) HLS HRI Hm Ht).
  - rewrite EPK, lsc_w_sec. pose proof (fr_LS_drain_sec_peak cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP). lia.
  - lia.
  - rewrite EPK. unfold P24. change kBatchClass with 24.
    apply (lsc_pay 24 _ _ 5 2 2 _ _ ltac:(lia) (conj HPB0 HPBm)).
    + intros E. lia.
    + intros _. rewrite lsc_w_cls. pose proof (fr_LS_drain_cls_peak 24 cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP).
      nia.
    + pose proof (cnl_pk_cls 24 (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h))). lia.
  - lia.
  - intros c Hc. rewrite EPK. apply (lsc_pay c _ _ 5 2 2 _ _ Hc (conj HPB0 HPBm)).
    + intros ->. rewrite lsc_w_cls. pose proof (fr_LS_drain_c1_peak cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP). lia.
    + intros _. rewrite lsc_w_cls. pose proof (fr_LS_drain_cls_peak c cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP).
      nia.
    + pose proof (cnl_pk_cls c (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h))). lia.
Qed.

Lemma fr_LS3cp_cnt_rm : forall cx t m ly S si h j0,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (acnt Psec (ablocks B ly S) + pk_rm m h j0 Psec <= Lsec)%nat /\
  (acnt P24 (ablocks B ly S) + pk_rm m h j0 P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_rm m h j0 (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (Hp & HE & _ & _).
  destruct Hp as (_ & _ & _ & Hre & _). destruct HE as (_ & _ & _ & _ & Hsk).
  destruct (tc_rm_facts cx t m si h j0 HRI Hat HU) as (_ & _ & _ & HJ).
  pose proof (pair_bytes_nonneg (rm_ent m j0) h) as HPB0.
  assert (HPBm : pair_bytes (rm_ent m j0) h <= pt_mass m).
  { pose proof Hat as (_ & _ & _ & _ & _ & Hh & Hj0 & _).
    pose proof (pt_pair_le_mass m si h j0 (rm_ent m j0) Hh
                  (nth_error_nth' (lm_es m) relay_remove_b_c.no_entry Hj0) Hoffs) as M.
    unfold pair_bytes. destruct (re_skip (rm_ent m j0) =? 0); lia. }
  assert (CN : Z.of_nat (if re_eof (rm_ent m j0) =? 0
                         then cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) Psec else 0%nat) <= 2 /\
               forall c, pt_s c * (Z.of_nat (if re_eof (rm_ent m j0) =? 0
                         then cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) (Pcls c) else 0%nat) - 2) <=
                         pair_bytes (rm_ent m j0) h).
  { destruct (re_eof (rm_ent m j0) =? 0) eqn:Eo.
    - apply Z.eqb_eq in Eo. destruct (Hre Eo) as (Hov & HW). destruct (HJ Eo) as (Href & _).
      unfold cnl_pk. split.
      + rewrite Z2Nat.id by apply tr_peakP_nonneg. exact (cnl_pk_sec _ _ (cnl_drain_short h Href)).
      + intros c. rewrite Z2Nat.id by apply tr_peakP_nonneg.
        pose proof (cnl_pk_cls c (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h))).
        pose proof (cnl_drain_bytes _ h Hsk Hov HW). lia.
    - split; [cbn; lia|]. intros c. pose proof (pt_s_ge c). cbn. lia. }
  destruct CN as [CNs CNc].
  assert (EPK : forall P, Z.of_nat (pk_rm m h j0 P) = tr_peakP P (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) +
     Z.of_nat (if re_eof (rm_ent m j0) =? 0 then cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P else 0%nat) +
     4).
  { intros P. unfold pk_rm. rewrite !Nat2Z.inj_add. rewrite Z2Nat.id by apply tr_peakP_nonneg. lia. }
  apply (lsc_room cx t m ly S (pk_rm m h j0) (5 + 2 + 4) (5 + 2 + 4) HLS HRI Hm Ht).
  - rewrite EPK, lsc_w_sec. pose proof (fr_LS_rm_sec_peak cx t m si h j0 HRI Hat HU Hpos). lia.
  - lia.
  - rewrite EPK. unfold P24. change kBatchClass with 24.
    apply (lsc_pay 24 _ _ 5 2 4 _ _ ltac:(lia) (conj HPB0 HPBm)).
    + intros E. lia.
    + intros _. rewrite lsc_w_cls. pose proof (fr_LS_rm_cls_peak 24 cx t m si h j0 HRI Hat HU Hpos). nia.
    + exact (CNc 24).
  - lia.
  - intros c Hc. rewrite EPK. apply (lsc_pay c _ _ 5 2 4 _ _ Hc (conj HPB0 HPBm)).
    + intros ->. rewrite lsc_w_cls. pose proof (fr_LS_rm_c1_peak cx t m si h j0 HRI Hat HU Hpos). lia.
    + intros _. rewrite lsc_w_cls. pose proof (fr_LS_rm_cls_peak c cx t m si h j0 HRI Hat HU Hpos). nia.
    + exact (CNc c).
Qed.

Definition pk_gone (cx : lfcx) (m : lmod) (hs : list (hsrc * nat)) (P : Z -> bool) : nat :=
  (Z.to_nat (tr_peakP P (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs)) +
   fold_right Nat.add 0%nat (map (gn_cnl P) (combine (lm_es m) hs)) + 3)%nat.

Lemma lsc_gn_cnl : forall ps, Forall lsc_pq ps ->
  Z.of_nat (fold_right Nat.add 0%nat (map (gn_cnl Psec) ps)) <= 2 * Z.of_nat (length ps) /\
  (forall c, pt_s c * (Z.of_nat (fold_right Nat.add 0%nat (map (gn_cnl (Pcls c)) ps)) - 2 * Z.of_nat (length ps)) <=
     fold_right Z.add 0 (map (fun p => if re_eof (fst p) =? 0 then pair_bytes (fst p) (fst (snd p)) else 0) ps)).
Proof.
  induction ps as [|p ps IH]; intros HF.
  - cbn. split; [lia|]. intros c. lia.
  - inversion HF as [|? ? Hp HF']; subst. destruct (IH HF') as [I1 I2].
    assert (P1 : Z.of_nat (gn_cnl Psec p) <= 2 /\
                 forall c, pt_s c * (Z.of_nat (gn_cnl (Pcls c) p) - 2) <=
                           (if re_eof (fst p) =? 0 then pair_bytes (fst p) (fst (snd p)) else 0)).
    { unfold gn_cnl. destruct (re_eof (fst p) =? 0) eqn:Eo.
      - apply Z.eqb_eq in Eo. destruct (Hp Eo) as (Hsk & Hov & HW & HU & _).
        pose proof (tc_ref_state (fst p) (fst (snd p)) Hsk Hov HW HU) as Href.
        unfold cnl_pk. split.
        + rewrite Z2Nat.id by apply tr_peakP_nonneg. exact (cnl_pk_sec _ _ (cnl_drain_short _ Href)).
        + intros c. rewrite Z2Nat.id by apply tr_peakP_nonneg.
          pose proof (cnl_pk_cls c (hs_held (fst (snd p))) (map (map (Z_to_bv 8)) (dr_lines (fst (snd p))))).
          pose proof (cnl_drain_bytes (fst p) (fst (snd p)) Hsk Hov HW). lia.
      - split; [cbn; lia|]. intros c. pose proof (pt_s_ge c). cbn. lia. }
    destruct P1 as [P1s P1c]. cbn [map fold_right length]. split.
    + rewrite Nat2Z.inj_add, Nat2Z.inj_succ. lia.
    + intros c. specialize (I2 c). specialize (P1c c). pose proof (pt_s_ge c).
      rewrite Nat2Z.inj_add, Nat2Z.inj_succ. nia.
Qed.

Lemma lsc_slots_sum : forall (f : nat -> Z) (ps : list (rentry * (hsrc * nat))),
  fold_right Z.add 0 (map (fun p => if re_eof (fst p) =? 0 then f (snd (snd p)) else 0) ps) =
  fold_right Z.add 0 (map f (rig_slots ps)).
Proof.
  intros f ps. induction ps as [|p ps IH]; [reflexivity|].
  unfold rig_slots in *. cbn [map concat fold_right]. destruct (re_eof (fst p) =? 0); cbn; rewrite IH; lia.
Qed.
Lemma lsc_seq_sum : forall (g : option hsrc -> Z) (l : list (option hsrc)),
  fold_right Z.add 0 (map (fun k => g (nth k l None)) (seq 0 (length l))) = fold_right Z.add 0 (map g l).
Proof.
  intros g l. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map fold_right nth]. rewrite <- seq_shift, map_map. cbn [nth]. rewrite IH. reflexivity.
Qed.
Lemma lsc_map_fst_combine : forall (A C : Type) (l : list A) (l' : list C), length l = length l' ->
  map fst (combine l l') = l.
Proof.
  intros A C l. induction l as [|a l IH]; intros [|b l'] E; cbn in *; try reflexivity; try discriminate.
  rewrite IH by lia. reflexivity.
Qed.
Lemma lsc_rig_pb_mass : forall cx t m hs, fr_RINV cx t m -> gn_pairs m hs ->
  (forall k h, nth k (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  rig_pb (lm_es m) hs <= pt_mass m.
Proof.
  intros cx t m hs HRI (Hlen & HF & HND) Hoff.
  pose proof HRI as (_ & (Hl4 & _) & _).
  set (f := fun k => slot_pend (nth k (lm_hs m) None)).
  assert (A : forall ps, Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) ps ->
     fold_right Z.add 0 (map (fun p => if re_eof (fst p) =? 0 then pair_bytes (fst p) (fst (snd p)) else 0) ps) <=
     fold_right Z.add 0 (map (fun p => if re_eof (fst p) =? 0 then f (snd (snd p)) else 0) ps) +
     fold_right Z.add 0 (map (fun p => pt_eu (fst p)) ps)).
  { induction ps as [|p ps IH]; intros HF'; [cbn; lia|]. inversion HF' as [|? ? Hp HF'']; subst.
    specialize (IH HF''). cbn [map fold_right].
    destruct (re_eof (fst p) =? 0) eqn:Eo; [|pose proof (pt_eu_nonneg (fst p)); lia].
    apply Z.eqb_eq in Eo. destruct (Hp Eo) as (_ & Hn & _).
    assert (E : f (snd (snd p)) = Z.of_nat (length (pending_stream (fst (snd p))))).
    { unfold f. rewrite Hn. symmetry. apply ls3_ps_sp. exact (Hoff _ _ Hn). }
    assert (Ep : pair_bytes (fst p) (fst (snd p)) <= Z.of_nat (length (pending_stream (fst (snd p)))) + pt_eu (fst p))
      by (unfold pair_bytes, pt_eu; destruct (re_skip (fst p) =? 0); lia).
    lia. }
  pose proof (A _ HF) as A1. rewrite lsc_slots_sum in A1.
  assert (A2 : fold_right Z.add 0 (map f (rig_slots (combine (lm_es m) hs))) <=
               fold_right Z.add 0 (map f (seq 0 (length (lm_hs m))))).
  { apply pt_sum_incl.
    - intros k. unfold f. apply pt_pend_nonneg.
    - first [exact HND | apply NoDup_ListNoDup; exact HND].
    - intros k Hk. unfold rig_slots in Hk. apply in_concat in Hk as (l & Hl & Hk).
      apply in_map_iff in Hl as (p & <- & Hp).
      revert Hk. destruct (re_eof (fst p) =? 0) eqn:Eo; intros Hk; [|destruct Hk].
      destruct Hk as [<- | []]. rewrite Forall_forall in HF. apply Z.eqb_eq in Eo.
      destruct (HF p Hp Eo) as (H4 & _). apply in_seq. rewrite Hl4. lia. }
  unfold f in A1, A2. rewrite (lsc_seq_sum slot_pend (lm_hs m)) in A2.
  assert (A3 : fold_right Z.add 0 (map (fun p => pt_eu (fst p)) (combine (lm_es m) hs)) =
               fold_right Z.add 0 (map pt_eu (lm_es m))).
  { rewrite <- (map_map fst pt_eu), lsc_map_fst_combine by lia. reflexivity. }
  unfold rig_pb, pt_mass, pend_bytes. lia.
Qed.
Lemma lsc_rig_ok : forall cx t m hs, fr_RINV cx t m -> gn_pairs m hs ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall k h, nth k (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  rig_ok (lm_es m) hs.
Proof.
  intros cx t m hs HRI (_ & HF & _) HU Hoff. pose proof HRI as (_ & (_ & _ & _ & HE & _) & _).
  unfold rig_ok. rewrite Forall_forall in HF, HU, HE |- *. intros p Hp Eo.
  destruct (HF p Hp Eo) as (_ & Hn & _ & Hov & HW & _).
  destruct p as [e [h k]]. cbn [fst snd] in *.
  pose proof (in_combine_l _ _ _ _ Hp) as He.
  destruct (HE e He) as (_ & _ & _ & _ & Hsk).
  split; [exact Hsk|]. split; [exact Hov|]. split; [exact HW|]. split; [exact (HU e He)|].
  destruct (Hoff k h Hn) as [(_ & ->) | (r & rs & _ & Ho & _)]; lia.
Qed.

Lemma fr_LS3cp_cnt_gone : forall cx t m ly S hs,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall k h, nth k (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (acnt Psec (ablocks B ly S) + pk_gone cx m hs Psec <= Lsec)%nat /\
  (acnt P24 (ablocks B ly S) + pk_gone cx m hs P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_gone cx m hs (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S hs HLS HRI Hgp Hm Ht HU Hpos Hoff.
  pose proof (lsc_rig_ok cx t m hs HRI Hgp HU Hoff) as Hok.
  pose proof (tc_rm_cap m Hpos) as Hcap.
  pose proof (lsc_rig_pb_mass cx t m hs HRI Hgp Hoff) as HPBm.
  assert (HPB0 : 0 <= rig_pb (lm_es m) hs).
  { unfold rig_pb. apply zsum_map_nonneg. intros p. destruct (re_eof (fst p) =? 0); [apply pair_bytes_nonneg | lia]. }
  pose proof (fr_RINV_es_le cx t m HRI) as E4.
  assert (Lc : length (combine (lm_es m) hs) = length (lm_es m)) by (rewrite length_combine; destruct Hgp as (Hl & _); lia).
  destruct (lsc_gn_cnl (combine (lm_es m) hs) Hok) as (G1 & G2). rewrite Lc in G1, G2.
  assert (EPK : forall P, Z.of_nat (pk_gone cx m hs P) =
    tr_peakP P (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) +
    Z.of_nat (fold_right Nat.add 0%nat (map (gn_cnl P) (combine (lm_es m) hs))) + 3).
  { intros P. unfold pk_gone. rewrite !Nat2Z.inj_add. rewrite Z2Nat.id by apply tr_peakP_nonneg. lia. }
  assert (Hn : 0 <= Z.of_nat (length (lm_es m)) <= 4) by lia.
  apply (lsc_room cx t m ly S (pk_gone cx m hs)
           (4 * Z.of_nat (length (lm_es m)) + 1 + 2 * Z.of_nat (length (lm_es m)) + 3)
           (4 * Z.of_nat (length (lm_es m)) + 1 + 2 * Z.of_nat (length (lm_es m)) + 3) HLS HRI Hm Ht).
  - rewrite EPK, lsc_w_sec.
    pose proof (rig_sec_peak (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs
                  Hcap Hok). lia.
  - lia.
  - rewrite EPK. unfold P24. change kBatchClass with 24.
    apply (lsc_pay 24 _ _ (4 * Z.of_nat (length (lm_es m)) + 1) (2 * Z.of_nat (length (lm_es m))) 3 _ _ ltac:(lia)
             (conj HPB0 HPBm)).
    + intros E. lia.
    + intros _. rewrite lsc_w_cls.
      pose proof (rig_cls_peak 24 (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs
                    Hcap Hok). nia.
    + exact (G2 24).
  - lia.
  - intros c Hc. rewrite EPK.
    apply (lsc_pay c _ _ (4 * Z.of_nat (length (lm_es m)) + 1) (2 * Z.of_nat (length (lm_es m))) 3 _ _ Hc
             (conj HPB0 HPBm)).
    + intros ->. rewrite lsc_w_cls.
      pose proof (rig_c1_peak (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs
                    Hcap Hok). lia.
    + intros _. rewrite lsc_w_cls.
      pose proof (rig_cls_peak c (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs
                    Hcap Hok). nia.
    + exact (G2 c).
Qed.
End lsc.
