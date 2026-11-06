(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_gone_base_x.v, with its module paths and module names changed; 337 of its 409 lines of code are new or changed and 586 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfNames YG00cf YGcfRoomKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyRINVB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBArms ReplyB3Base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3 ReplyLSBDrainPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  ReplyB3LS3Arms ReplyLSCntL ReplyB3LS3c ReplyB3LS3cArms ReplyTrPeakW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  ReplyB3LSCntM ReplyB3LS3p ReplyB3TrPeakCnt ReplyB3TrPeakCntR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3TrPeakCnl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LScnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CfRBridgeRulesB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Abbreviation rm_ent := W_LLVMFuzzerTestOneInput_remove.rm_ent.
Local Abbreviation rm_at := W_LLVMFuzzerTestOneInput_remove.rm_at.
Local Abbreviation rm_rr_ok := W_LLVMFuzzerTestOneInput_remove.rm_rr_ok.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition lsc_af (pk : (Z -> bool) -> nat) (l : list (Z * Z)) : Prop :=
  (acnt Psec l + pk Psec <= Lsec)%nat /\ (acnt P24 l + pk P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) l + pk (Pcls c) <= LPRIM c)%nat).
Lemma lsc_af_mono : forall pk pk' l l', lsc_af pk l ->
  (forall P, (acnt P l' + pk' P <= acnt P l + pk P)%nat) -> lsc_af pk' l'.
Proof.
  intros pk pk' l l' (A1 & A2 & A3) H. split; [pose proof (H Psec); lia|].
  split; [pose proof (H P24); lia|]. intros c Hc. pose proof (H (Pcls c)). specialize (A3 c Hc). lia.
Qed.
Lemma lsc_net_le_peak : forall (X : Type) (P : Z -> bool) (tr : list (RelayRunT.rev X)),
  ReplyTrPeakW.tr_net_w (fun n => zb (P n)) tr <= tr_peakP P tr.
Proof.
  intros X P tr. rewrite tr_peakP_w.
  pose proof (ReplyTrPeakW.tr_peak_w_mid (fun n => zb (P n)) tr [] []) as H. rewrite !app_nil_r in H.
  change (ReplyTrPeakW.tr_peak_w (fun n => zb (P n)) (@nil (RelayRunT.rev X))) with 0 in H. lia.
Qed.
Lemma lsc_acnt_snoc : forall P l a n, acnt P (l ++ [(a, n)]) = (acnt P l + zn (P n))%nat.
Proof.
  intros P l a n. unfold acnt, zn. rewrite map_app, List.filter_app, length_app. cbn [map snd List.filter].
  destruct (P n); cbn [length]; lia.
Qed.
Lemma lsc_cnl_W8 : forall (h h'' : hsrc) (P : Z -> bool),
  hl_recs (hs_expected h) = [] ->
  map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  Z.to_nat (tr_peakP P (cnl_tr (hs_expected h'') (hs_held h''))) =
  ReplyB3TrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P.
Proof.
  intros h h'' P E0 Ex Eh. unfold cnl_tr. exact (lsc_cnl_call 0 (fun _ => RelayRunF.adr0) h h'' P E0 Ex Eh).
Qed.
Lemma lsc_cnl_W8_empty : forall (E H : hlist) (P : Z -> bool), hl_recs E = [] ->
  Z.to_nat (tr_peakP P (cnl_tr E H)) = 0%nat.
Proof. intros E H P E0. unfold cnl_tr. rewrite E0. reflexivity. Qed.
Lemma lsc_gn_cnl_open : forall (p : rentry * (hsrc * nat)) (hx : hsrc) (P : Z -> bool),
  re_eof (fst p) = 0 -> hl_recs (hs_expected (fst (snd p))) = [] ->
  map snd (hl_recs (hs_expected hx)) =
    map snd (hl_recs (hs_expected (fst (snd p)))) ++ map (map (Z_to_bv 8)) (dr_lines (fst (snd p))) ->
  hs_held hx = hs_held (fst (snd p)) ->
  Z.to_nat (tr_peakP P (cnl_tr (hs_expected hx) (hs_held hx))) = gn_cnl P p.
Proof.
  intros p hx P Eo E0 Ex Eh. unfold gn_cnl. rewrite (proj2 (Z.eqb_eq _ _) Eo).
  exact (lsc_cnl_W8 (fst (snd p)) hx P E0 Ex Eh).
Qed.
Lemma lsc_gn_cnl_empty : forall (hx : hsrc) (P : Z -> bool), hl_recs (hs_expected hx) = [] ->
  Z.to_nat (tr_peakP P (cnl_tr (hs_expected hx) (hs_held hx))) = 0%nat.
Proof. intros hx P E0. exact (lsc_cnl_W8_empty _ _ P E0). Qed.

Definition RP_CNT (RP : roomp) : Prop :=
  rp_Psec RP = ReplyCnt.Psec /\ rp_P24 RP = ReplyCnt.P24 /\ rp_Lsec RP = ReplyCnt.Lsec /\
  rp_L24 RP = ReplyCnt.L24 /\ rp_Pcls RP = ReplyCnt.Pcls /\ rp_LPRIM RP = ReplyCnt.LPRIM.

Section rp.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable CALL_ROOM_B : Z.
Variable RP : roomp.
Hypothesis HRP_CNT : RP_CNT RP.

Lemma lsc_rp_of_acnt : forall pk l, lsc_af pk l -> cnt_ok_pk RP pk l.
Proof.
  intros pk l H. destruct HRP_CNT as (E1 & E2 & E3 & E4 & E5 & E6). unfold cnt_ok_pk.
  rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.
Lemma lsc_rp_mono : forall pk pk' l l', lsc_af pk l ->
  (forall P, (acnt P l' + pk' P <= acnt P l + pk P)%nat) -> cnt_ok_pk RP pk' l'.
Proof. intros pk pk' l l' H Hle. apply lsc_rp_of_acnt. exact (lsc_af_mono pk pk' l l' H Hle). Qed.

Lemma lsc_kept_le3 : forall (P : Z -> bool) (p n T cap out : Z),
  (acnt P (xcnt_kept (if (n =? 0)%Z then [] else [(p, n)]) T cap out) <= 3)%nat.
Proof.
  intros P p n T cap out. unfold xcnt_kept, aout_blks. rewrite !acnt_app.
  assert (A1 : forall (b : bool) (x : Z * Z), (acnt P (if b then [] else [x]) <= 1)%nat).
  { intros [|] [a k]; unfold acnt; cbn [map List.filter snd]; [cbn; lia|]. destruct (P k); cbn; lia. }
  pose proof (A1 (n =? 0)%Z (p, n)). pose proof (A1 (T =? 0)%Z (T, ATABLE)). pose proof (A1 (cap =? 0)%Z (out, cap)).
  lia.
Qed.
Lemma rp_cnt_pro : forall (S0 S2 : astate) (ly : alayout) (p n T cap out : Z),
  xcnt_ok B S0 ly (if (n =? 0)%Z then [] else [(p, n)]) T cap out ->
  ablocks B ly S2 = ablocks B ly S0 ->
  cnt_ok_pk RP oa_peak (ablocks B ly S2).
Proof.
  intros S0 S2 ly p n T cap out (X1 & X2) E. apply lsc_rp_of_acnt. unfold lsc_af. rewrite E.
  assert (PO : forall P, (oa_peak P <= 2)%nat) by (intros P; unfold oa_peak; destruct (P ATABLE), (P APARTIAL); lia).
  unfold ReplyCnt.cnt_sec, ReplyCnt.cnt_cls, ReplyCnt.SEC0, ReplyCnt.CLS0 in *.
  split; [|split].
  - pose proof (lsc_kept_le3 Psec p n T cap out). pose proof (PO Psec).
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, lsc_Lsec. lia.
  - pose proof (X2 kBatchClass ltac:(change kBatchClass with 24; lia)) as X.
    pose proof (lsc_kept_le3 P24 p n T cap out). pose proof (PO P24).
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, lsc_L24. unfold P24 in *. lia.
  - intros c Hc. pose proof (X2 c Hc). pose proof (lsc_kept_le3 (Pcls c) p n T cap out). pose proof (PO (Pcls c)).
    pose proof (lsc_RL_pos c Hc).
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, (lsc_LPRIM c Hc).
    change (ReplyB3LS3p.RL_PRIM c) with (ReplyCnt.RL_PRIM c). lia.
Qed.

Lemma rp_cnt_add : forall cx t m ly S,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> ad_at_op cx m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP oa_peak (ablocks B ly S).
Proof.
  intros cx t m ly S HLS HRI Hop Hm Ht. apply lsc_rp_of_acnt.
  exact (fr_LS3cp_cnt_add B CALL_ROOM_B cx t m ly S HLS HRI Hop Hm Ht).
Qed.
Lemma rp_cnt_write : forall cx t m si h n ly S,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> wr_pick cx m si h -> 0 < wr_n cx m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP (lp_peak (hs_pending h) n) (ablocks B ly S).
Proof.
  intros cx t m si h n ly S HLS HRI _ _ Hm Ht. apply lsc_rp_of_acnt. unfold lsc_af.
  apply (lsc_room_const B CALL_ROOM_B cx t m ly S _ 2 HLS HRI Hm Ht); [lia|].
  intros P. unfold lp_peak. destruct (P (lp_vbytes (hs_pending h)) && lp_grow (hs_pending h)); destruct (P (n + 1)); lia.
Qed.

Lemma rp_cnt_drain_dr : forall cx t m ly S si h j,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RP (dr_pk (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    (ablocks B ly S).
Proof.
  intros cx t m ly S si h j HLS HRI Hop Hpick Hj Hfdj Heof Hm Ht HU HXP Hoffs.
  apply (lsc_rp_mono (pk_drain m h j) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_drain B CALL_ROOM_B cx t m ly S si h j HLS HRI Hop Hpick Hj Hfdj Heof Hm Ht HU HXP Hoffs).
  - intros P. unfold dr_pk, pk_drain. lia.
Qed.
Lemma rp_cnt_drain_cnl : forall cx t m ly S si h j (ly1 : alayout) (S1 : astate) (h'' : hsrc),
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (forall P, (acnt P (ablocks B ly1 S1) <= acnt P (ablocks B ly S) +
     Z.to_nat (tr_peakP P (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                 (nth j (lm_es m) dr_e0) h)))%nat) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  cnt_ok_pk RP (cnl_pk (hs_expected h'') (hs_held h'')) (ablocks B ly1 S1).
Proof.
  intros cx t m ly S si h j ly1 S1 h'' HLS HRI Hop Hpick Hj Hfdj Heof Hm Ht HU HXP Hoffs HG Hx Hh.
  destruct (dpre_pair cx t m si h j HRI Hpick Hj Hfdj) as (Hp & _).
  destruct Hp as (_ & _ & _ & _ & _ & _ & HE0 & _).
  apply (lsc_rp_mono (pk_drain m h j) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_drain B CALL_ROOM_B cx t m ly S si h j HLS HRI Hop Hpick Hj Hfdj Heof Hm Ht HU HXP Hoffs).
  - intros P. specialize (HG P). unfold cnl_pk, pk_drain. rewrite (lsc_cnl_W8 h h'' P HE0 Hx Hh). lia.
Qed.

Lemma rp_cnt_rm_rr : forall cx t m ly0 S0 si h j0,
  fr_LS3cp B CALL_ROOM_B cx t m ly0 S0 -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RP (rr_pk (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) (ablocks B ly0 S0).
Proof.
  intros cx t m ly0 S0 si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs.
  apply (lsc_rp_mono (pk_rm m h j0) _ (ablocks B ly0 S0)).
  - exact (fr_LS3cp_cnt_rm B CALL_ROOM_B cx t m ly0 S0 si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs).
  - intros P. unfold rr_pk, pk_rm. lia.
Qed.
Lemma lsc_rm_cnl : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 (P : Z -> bool),
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Z.to_nat (tr_peakP P (cnl_tr (hs_expected h1) (hs_held h1))) =
  (if (re_eof (rm_ent m j0) =? 0)%Z
   then ReplyB3TrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P
   else 0%nat).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 P HRI Hat Hrr.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (Hp & _).
  destruct Hp as (_ & _ & _ & _ & _ & _ & HE0 & _).
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_ok in Hrr. cbv zeta in Hrr. destruct Hrr as (Hd & _).
  revert Hd. destruct (re_eof (rm_ent m j0) =? 0)%Z eqn:Eo; intros Hd; cbv iota in Hd.
  - unfold dr_rel in Hd. cbv zeta in Hd.
    destruct Hd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hx & _ & Hh & _).
    exact (lsc_cnl_W8 h h1 P HE0 Hx Hh).
  - destruct Hd as (_ & ->). exact (lsc_cnl_W8_empty _ _ P HE0).
Qed.
Lemma rp_cnt_rm_cnl : forall cx t m ly0 S0 si h j0 e1 h1 ev LB c2 O2 cap2 (ly1 : alayout) (S1 : astate),
  fr_LS3cp B CALL_ROOM_B cx t m ly0 S0 -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  (forall P, (acnt P (ablocks B ly1 S1) <= acnt P (ablocks B ly0 S0) +
     Z.to_nat (tr_peakP P (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)))%nat) ->
  cnt_ok_pk RP (cnl_pk (hs_expected h1) (hs_held h1)) (ablocks B ly1 S1).
Proof.
  intros cx t m ly0 S0 si h j0 e1 h1 ev LB c2 O2 cap2 ly1 S1 HLS HRI Hat Hm Ht HU Hpos Hoffs Hrr HG.
  apply (lsc_rp_mono (pk_rm m h j0) _ (ablocks B ly0 S0)).
  - exact (fr_LS3cp_cnt_rm B CALL_ROOM_B cx t m ly0 S0 si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs).
  - intros P. specialize (HG P). unfold cnl_pk, pk_rm.
    rewrite (lsc_rm_cnl cx t m si h j0 e1 h1 ev LB c2 O2 cap2 P HRI Hat Hrr). lia.
Qed.
Lemma rp_cnt_rm_later : forall cx t m ly0 S0 si h j0 e1 h1 ev LB c2 O2 cap2 (lyx : alayout) (Sx : astate),
  fr_LS3cp B CALL_ROOM_B cx t m ly0 S0 -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  (forall P, (acnt P (ablocks B lyx Sx) <= acnt P (ablocks B ly0 S0) +
     Z.to_nat (tr_peakP P (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) +
     Z.to_nat (tr_peakP P (cnl_tr (hs_expected h1) (hs_held h1))))%nat) ->
  cnt_ok_pk RP cshe_pk (ablocks B lyx Sx) /\ cnt_ok_pk RP sr_pk (ablocks B lyx Sx).
Proof.
  intros cx t m ly0 S0 si h j0 e1 h1 ev LB c2 O2 cap2 lyx Sx HLS HRI Hat Hm Ht HU Hpos Hoffs Hrr HG.
  pose proof (fr_LS3cp_cnt_rm B CALL_ROOM_B cx t m ly0 S0 si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs) as R.
  assert (L : forall P, (acnt P (ablocks B lyx Sx) + 0 <= acnt P (ablocks B ly0 S0) + pk_rm m h j0 P)%nat).
  { intros P. specialize (HG P). unfold pk_rm.
    rewrite (lsc_rm_cnl cx t m si h j0 e1 h1 ev LB c2 O2 cap2 P HRI Hat Hrr) in HG. lia. }
  split; apply (lsc_rp_mono (pk_rm m h j0) _ (ablocks B ly0 S0) _ R); exact L.
Qed.
Lemma rp_cnt_rm : forall cx t m ly S si h j0,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RP (pk_rm m h j0) (ablocks B ly S).
Proof.
  intros cx t m ly S si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs. apply lsc_rp_of_acnt.
  exact (fr_LS3cp_cnt_rm B CALL_ROOM_B cx t m ly S si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs).
Qed.

Lemma rp_cnt_gone_rig : forall cx t m ly S hs,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall k h, nth k (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RP (rig_pk (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs))
    (ablocks B ly S).
Proof.
  intros cx t m ly S hs HLS HRI Hgp Hm Ht HU Hpos Hoff.
  apply (lsc_rp_mono (pk_gone cx m hs) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_gone B CALL_ROOM_B cx t m ly S hs HLS HRI Hgp Hm Ht HU Hpos Hoff).
  - intros P. unfold rig_pk, pk_gone. lia.
Qed.
Lemma rp_cnt_gone_cnl : forall cx t m ly S hs (lyx : alayout) (Sx : astate) (E H : hlist),
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall k h, nth k (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (forall P, (acnt P (ablocks B lyx Sx) + Z.to_nat (tr_peakP P (cnl_tr E H)) <=
     acnt P (ablocks B ly S) +
     Z.to_nat (tr_peakP P (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m)
                                  (lm_es m) hs)) +
     fold_right Nat.add 0%nat (map (gn_cnl P) (combine (lm_es m) hs)))%nat) ->
  cnt_ok_pk RP (cnl_pk E H) (ablocks B lyx Sx).
Proof.
  intros cx t m ly S hs lyx Sx E H HLS HRI Hgp Hm Ht HU Hpos Hoff HG.
  apply (lsc_rp_mono (pk_gone cx m hs) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_gone B CALL_ROOM_B cx t m ly S hs HLS HRI Hgp Hm Ht HU Hpos Hoff).
  - intros P. specialize (HG P). unfold cnl_pk, pk_gone. lia.
Qed.
Lemma rp_cnt_gone_later : forall cx t m ly S hs (lyx : alayout) (Sx : astate),
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall k h, nth k (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (forall P, (acnt P (ablocks B lyx Sx) <=
     acnt P (ablocks B ly S) +
     Z.to_nat (tr_peakP P (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m)
                                  (lm_es m) hs)) +
     fold_right Nat.add 0%nat (map (gn_cnl P) (combine (lm_es m) hs)))%nat) ->
  cnt_ok_pk RP cshe_pk (ablocks B lyx Sx).
Proof.
  intros cx t m ly S hs lyx Sx HLS HRI Hgp Hm Ht HU Hpos Hoff HG.
  apply (lsc_rp_mono (pk_gone cx m hs) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_gone B CALL_ROOM_B cx t m ly S hs HLS HRI Hgp Hm Ht HU Hpos Hoff).
  - intros P. specialize (HG P). unfold cshe_pk, pk_gone. lia.
Qed.

Lemma rp_cnt_ev_malloc : forall cx t m ly S e,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  cnt_ok RP (ablocks B ly S).
Proof.
  intros cx t m ly S e HLS HRI He Hm Ht. unfold cnt_ok.
  apply (lsc_rp_mono (pk_event e) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_event B CALL_ROOM_B cx t m ly S e HLS HRI He Hm Ht).
  - intros P. cbv beta. unfold pk_event. lia.
Qed.
Lemma rp_cnt_ev_relay : forall cx t m ly S e (ly1 : alayout) (S1 : astate) q,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  cnt_ok_pk RP re_pk (ablocks B ly1 S1).
Proof.
  intros cx t m ly S e ly1 S1 q HLS HRI He Hm Ht E1.
  apply (lsc_rp_mono (pk_event e) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_event B CALL_ROOM_B cx t m ly S e HLS HRI He Hm Ht).
  - intros P. rewrite E1, lsc_acnt_snoc. unfold re_pk, pk_event. lia.
Qed.
Lemma rp_cnt_ev_free : forall cx t m ly S e (ly1 ly2 : alayout) (S1 S2 : astate) q,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (forall P, (acnt P (ablocks B ly2 S2) <= acnt P (ablocks B ly1 S1) + re_pk P)%nat) ->
  cnt_ok RP (ablocks B ly2 S2).
Proof.
  intros cx t m ly S e ly1 ly2 S1 S2 q HLS HRI He Hm Ht E1 HG. unfold cnt_ok.
  apply (lsc_rp_mono (pk_event e) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_event B CALL_ROOM_B cx t m ly S e HLS HRI He Hm Ht).
  - intros P. specialize (HG P). cbv beta. rewrite E1, lsc_acnt_snoc in HG. unfold re_pk, pk_event in *. lia.
Qed.

Lemma rp_cnt_exit_rf : forall cx t m ly S,
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP rf_pk (ablocks B ly S).
Proof.
  intros cx t m ly S HLS HRI Hm Ht. apply lsc_rp_of_acnt.
  exact (fr_LS3cp_cnt_exit B CALL_ROOM_B cx t m ly S HLS HRI Hm Ht).
Qed.
Lemma rp_cnt_exit_later : forall cx t m ly S (lyx : alayout) (Sx : astate),
  fr_LS3cp B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  (forall P, (acnt P (ablocks B lyx Sx) <= acnt P (ablocks B ly S) + rf_pk P)%nat) ->
  cnt_ok_pk RP cshe_pk (ablocks B lyx Sx) /\ cnt_ok_pk RP sr_pk (ablocks B lyx Sx).
Proof.
  intros cx t m ly S lyx Sx HLS HRI Hm Ht HG.
  pose proof (fr_LS3cp_cnt_exit B CALL_ROOM_B cx t m ly S HLS HRI Hm Ht) as R.
  split; apply (lsc_rp_mono pk_exit _ (ablocks B ly S) _ R); intros P; specialize (HG P);
    unfold cshe_pk, sr_pk, rf_pk, pk_exit in *; lia.
Qed.
End rp.

Lemma rp_cnt_cf : RP_CNT CfRBridgeRulesB.RP_cf.
Proof. exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))). Qed.
