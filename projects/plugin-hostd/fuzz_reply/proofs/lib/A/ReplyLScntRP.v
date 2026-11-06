(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_gone_base_x.v, with its module paths and module names changed; 329 of its 401 lines of code are new or changed and 586 lines of the source are left out. *)
(* The LS_cnt rows of ReplyLScnt.v in the arms' room-record form (W8Entry-2's arms-step decision, a Theorem Labs lane 04:21Z):
   every count premise an allocating arm passes to a callee is `cnt_ok_pk RP <the callee's premise peak> (ablocks B ly S)`
   for the arm's `Variable RP : roomp`.  proves no function (kind: invariant lemma).

   THE TEXTS.  roomp, cnt_ok_pk and cnt_ok are W8's lib/A/W_journal_x.v; the premise peaks lp_peak, cshe_pk, sr_pk,
   re_pk, rf_pk, cnl_tr, cnl_pk, dr_pk, rr_pk, rig_pk are lib/A/W_contract_x.v's and oa_peak is lib/A/W_op_add.v's.
   acnt and tr_peakP are ReplyCnt.v's, as in W8's files.  cnl_tr / cnl_pk here are W8's (E H) forms, not
   ReplyTrPeakCnl.v's (H xs) ones, which this file names qualified.

   WHAT RP MUST BE.  RP_NP alone constrains only rp_RM and gives no count fact, so no LS_cnt row may be proved from
   RP_NP; the rows need RP_CNT, which holds at RP_cf by rp_cnt_cf.  RP_CNT RP says RP's count fields are ReplyCnt.v's
   top_x names (Psec, P24, Lsec, L24, Pcls, LPRIM); the lemmas take it as the hypothesis HRP_CNT (a Theorem Labs lane 04:38Z: the
   top discharges them at RP_cf, the arms do not take RP_CNT).  RP_cf is a Theorem Labs lane's lib/A/CfRBridgeRules.v's;
   rp_cnt_cf : RP_CNT CfRBridgeRules.RP_cf is six eq_refl.

   THE BRIDGE.  lsc_rp_of_acnt: ReplyLScnt's acnt form (lsc_af) at RP_CNT is cnt_ok_pk RP; lsc_rp_mono moves it to a
   later state l' and a callee's peak pk' when acnt P l' + pk' P <= acnt P l + PK P for every P.

   THE CALLS (one lemma per allocating call with a count premise; the arm's state names in brackets):
   - SEG_PRO: op_add [S2, the entry's blocks]: rp_cnt_pro (from the entry contract's ReplyCnt.xcnt_ok, the cut's XCNT
     text with inp := if n =? 0 then [] else [(p, n)]).
   - ARM_add: op_add [the cut]: rp_cnt_add.
   - ARM_write: list_push [the cut], for any text length n: rp_cnt_write.
   - ARM_drain: drain [the cut]: rp_cnt_drain_dr; check_no_loss [S1, after the drain]: rp_cnt_drain_cnl, from the
     drain's count growth (acnt S1 <= acnt S + drain's trace peak) and LS_cnl_pre's two premises (the expected list the
     drain appended to, the held list it kept).  check_no_loss_read and check_shape_done have no count premise.
   - ARM_remove: relay_remove [the cut S0]: rp_cnt_rm_rr; check_no_loss [S1]: rp_cnt_rm_cnl, from rm_rr_ok and
     relay_remove's growth; check_shape_ends and source_reset [any later state]: rp_cnt_rm_later, from the growth of
     both earlier calls.
   - ARM_gone: relay_instance_gone [the cut]: rp_cnt_gone_rig; each entry's check_no_loss [its state]: rp_cnt_gone_cnl,
     and each check_shape_ends: rp_cnt_gone_later, from the growth so far against rig's trace peak plus the sum over
     the table of gn_cnl (lsc_gn_cnl_open / lsc_gn_cnl_empty give a call's own check_no_loss peak as its pair's gn_cnl).
   - ARM_event: malloc [the cut]: rp_cnt_ev_malloc; relay_event [S1 = S ++ [(q, re_len e)]]: rp_cnt_ev_relay; free
     [S2]: rp_cnt_ev_free, from relay_event's growth (at most re_pk; W_tr_cnt.v tc_re at the audit).
   - SEG_EXIT: relay_finish [the cut]: rp_cnt_exit_rf; check_shape_ends and source_reset [later]: rp_cnt_exit_later,
     from relay_finish's growth (at most rf_pk; W_tr_cnt.v tc_rf).
   A growth premise in trace-net form follows from lsc_net_le_peak (a trace's net count is at most its peak). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfNames YG00cf YGcfRoomKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CfParamsReply.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyTrPeakCnl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLScnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CfRBridgeRules.
(* gn_pairs / gn_id in the gone rows: lib/A/W_LLVMFuzzerTestOneInput_gone_base.v's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== the acnt form and the trace facts *)
(* ReplyLScnt.v's row form at ReplyCnt.v's top_x names *)
Definition lsc_af (pk : (Z -> bool) -> nat) (l : list (Z * Z)) : Prop :=
  (acnt Psec l + pk Psec <= Lsec)%nat /\ (acnt P24 l + pk P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) l + pk (Pcls c) <= LPRIM c)%nat).
Lemma lsc_af_mono : forall pk pk' l l', lsc_af pk l ->
  (forall P, (acnt P l' + pk' P <= acnt P l + pk P)%nat) -> lsc_af pk' l'.
Proof.
  intros pk pk' l l' (A1 & A2 & A3) H. split; [pose proof (H Psec); lia|].
  split; [pose proof (H P24); lia|]. intros c Hc. pose proof (H (Pcls c)). specialize (A3 c Hc). lia.
Qed.
(* a trace's net count is at most its peak (for a walk that proves the growth in net form) *)
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
(* W8's check_no_loss trace after a drain is the rows' (ReplyTrPeakCnl.v) at the drained lines *)
Lemma lsc_cnl_W8 : forall (h h'' : hsrc) (P : Z -> bool),
  hl_recs (hs_expected h) = [] ->
  map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  Z.to_nat (tr_peakP P (cnl_tr (hs_expected h'') (hs_held h''))) =
  ReplyTrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P.
Proof.
  intros h h'' P E0 Ex Eh. unfold cnl_tr. exact (lsc_cnl_call 0 (fun _ => RelayRunF.adr0) h h'' P E0 Ex Eh).
Qed.
Lemma lsc_cnl_W8_empty : forall (E H : hlist) (P : Z -> bool), hl_recs E = [] ->
  Z.to_nat (tr_peakP P (cnl_tr E H)) = 0%nat.
Proof. intros E H P E0. unfold cnl_tr. rewrite E0. reflexivity. Qed.
(* the gone arm: a check_no_loss call's own peak is its pair's gn_cnl (ReplyLScnt.v) *)
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

(* RP's count fields are ReplyCnt.v's top_x names; RP_NP gives none of this (see the header) *)
Definition RP_CNT (RP : roomp) : Prop :=
  rp_Psec RP = ReplyCnt.Psec /\ rp_P24 RP = ReplyCnt.P24 /\ rp_Lsec RP = ReplyCnt.Lsec /\
  rp_L24 RP = ReplyCnt.L24 /\ rp_Pcls RP = ReplyCnt.Pcls /\ rp_LPRIM RP = ReplyCnt.LPRIM.

Section rp.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable RP : roomp.
Hypothesis HRP_CNT : RP_CNT RP.

(* ================================================================== the bridge *)
Lemma lsc_rp_of_acnt : forall pk l, lsc_af pk l -> cnt_ok_pk RP pk l.
Proof.
  intros pk l H. destruct HRP_CNT as (E1 & E2 & E3 & E4 & E5 & E6). unfold cnt_ok_pk.
  rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.
Lemma lsc_rp_mono : forall pk pk' l l', lsc_af pk l ->
  (forall P, (acnt P l' + pk' P <= acnt P l + pk P)%nat) -> cnt_ok_pk RP pk' l'.
Proof. intros pk pk' l l' H Hle. apply lsc_rp_of_acnt. exact (lsc_af_mono pk pk' l l' H Hle). Qed.

(* ================================================================== SEG_PRO: op_add, from the entry *)
Lemma lsc_kept_le3 : forall (P : Z -> bool) (p n T cap out : Z),
  (acnt P (xcnt_kept (if (n =? 0)%Z then [] else [(p, n)]) T cap out) <= 3)%nat.
Proof.
  intros P p n T cap out. unfold xcnt_kept, aout_blks. rewrite !acnt_app.
  assert (A1 : forall (b : bool) (x : Z * Z), (acnt P (if b then [] else [x]) <= 1)%nat).
  { intros [|] [a k]; unfold acnt; cbn [map List.filter snd]; [cbn; lia|]. destruct (P k); cbn; lia. }
  pose proof (A1 (n =? 0)%Z (p, n)). pose proof (A1 (T =? 0)%Z (T, ATABLE)). pose proof (A1 (cap =? 0)%Z (out, cap)).
  lia.
Qed.
(* op_add's call (_pro_x.v, at S2 after the fake frame, whose blocks are the entry's): the entry contract's XCNT
   (_cut.v:211 at b518e48c550, ReplyCnt.xcnt_ok) *)
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
    change (ReplyLS3p.RL_PRIM c) with (ReplyCnt.RL_PRIM c). lia.
Qed.

(* ================================================================== ARM_add, ARM_write *)
(* op_add's call at the cut (_add_x.v) *)
Lemma rp_cnt_add : forall cx t m ly S,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> ad_at_op cx m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP oa_peak (ablocks B ly S).
Proof.
  intros cx t m ly S HLS HRI Hop Hm Ht. apply lsc_rp_of_acnt. exact (fr_LS3cp_cnt_add B cx t m ly S HLS HRI Hop Hm Ht).
Qed.
(* list_push's call at the cut (_write_x.v), at any text length n (the arm passes |wr_x cx m|) *)
Lemma rp_cnt_write : forall cx t m si h n ly S,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> wr_pick cx m si h -> 0 < wr_n cx m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP (lp_peak (hs_pending h) n) (ablocks B ly S).
Proof.
  intros cx t m si h n ly S HLS HRI _ _ Hm Ht. apply lsc_rp_of_acnt. unfold lsc_af.
  apply (lsc_room_const B cx t m ly S _ 2 HLS HRI Hm Ht); [lia|].
  intros P. unfold lp_peak. destruct (P (lp_vbytes (hs_pending h)) && lp_grow (hs_pending h)); destruct (P (n + 1)); lia.
Qed.

(* ================================================================== ARM_drain *)
(* drain's call at the cut *)
Lemma rp_cnt_drain_dr : forall cx t m ly S si h j,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
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
  - exact (fr_LS3cp_cnt_drain B cx t m ly S si h j HLS HRI Hop Hpick Hj Hfdj Heof Hm Ht HU HXP Hoffs).
  - intros P. unfold dr_pk, pk_drain. lia.
Qed.
(* check_no_loss's call at the state (ly1, S1) after the drain: the drain grew each count by at most its trace peak
   (the walk's block relation), and LS_cnl_pre's premises name the lists check_no_loss runs on *)
Lemma rp_cnt_drain_cnl : forall cx t m ly S si h j (ly1 : alayout) (S1 : astate) (h'' : hsrc),
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
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
  - exact (fr_LS3cp_cnt_drain B cx t m ly S si h j HLS HRI Hop Hpick Hj Hfdj Heof Hm Ht HU HXP Hoffs).
  - intros P. specialize (HG P). unfold cnl_pk, pk_drain. rewrite (lsc_cnl_W8 h h'' P HE0 Hx Hh). lia.
Qed.

(* ================================================================== ARM_remove *)
(* relay_remove's call at the cut *)
Lemma rp_cnt_rm_rr : forall cx t m ly0 S0 si h j0,
  fr_LS3cp B cx t m ly0 S0 -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RP (rr_pk (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) (ablocks B ly0 S0).
Proof.
  intros cx t m ly0 S0 si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs.
  apply (lsc_rp_mono (pk_rm m h j0) _ (ablocks B ly0 S0)).
  - exact (fr_LS3cp_cnt_rm B cx t m ly0 S0 si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs).
  - intros P. unfold rr_pk, pk_rm. lia.
Qed.
(* what relay_remove leaves for check_no_loss: the drained lines when the entry was open, nothing at eof *)
Lemma lsc_rm_cnl : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 (P : Z -> bool),
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Z.to_nat (tr_peakP P (cnl_tr (hs_expected h1) (hs_held h1))) =
  (if (re_eof (rm_ent m j0) =? 0)%Z then ReplyTrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P
   else 0%nat).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 P HRI Hat Hrr.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (Hp & _).
  destruct Hp as (_ & _ & _ & _ & _ & _ & HE0 & _).
  unfold rm_rr_ok in Hrr. cbv zeta in Hrr. destruct Hrr as (Hd & _).
  revert Hd. destruct (re_eof (rm_ent m j0) =? 0)%Z eqn:Eo; intros Hd; cbv iota in Hd.
  - unfold dr_rel in Hd. cbv zeta in Hd.
    destruct Hd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hx & _ & Hh & _).
    exact (lsc_cnl_W8 h h1 P HE0 Hx Hh).
  - destruct Hd as (_ & ->). exact (lsc_cnl_W8_empty _ _ P HE0).
Qed.
(* check_no_loss's call at the state (ly1, S1) after relay_remove *)
Lemma rp_cnt_rm_cnl : forall cx t m ly0 S0 si h j0 e1 h1 ev LB c2 O2 cap2 (ly1 : alayout) (S1 : astate),
  fr_LS3cp B cx t m ly0 S0 -> fr_RINV cx t m -> rm_at cx m si h j0 ->
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
  - exact (fr_LS3cp_cnt_rm B cx t m ly0 S0 si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs).
  - intros P. specialize (HG P). unfold cnl_pk, pk_rm.
    rewrite (lsc_rm_cnl cx t m si h j0 e1 h1 ev LB c2 O2 cap2 P HRI Hat Hrr). lia.
Qed.
(* check_shape_ends' and source_reset's calls at any later state (lyx, Sx): relay_remove and check_no_loss grew each
   count by at most their trace peaks *)
Lemma rp_cnt_rm_later : forall cx t m ly0 S0 si h j0 e1 h1 ev LB c2 O2 cap2 (lyx : alayout) (Sx : astate),
  fr_LS3cp B cx t m ly0 S0 -> fr_RINV cx t m -> rm_at cx m si h j0 ->
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
  pose proof (fr_LS3cp_cnt_rm B cx t m ly0 S0 si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs) as R.
  assert (L : forall P, (acnt P (ablocks B lyx Sx) + 0 <= acnt P (ablocks B ly0 S0) + pk_rm m h j0 P)%nat).
  { intros P. specialize (HG P). unfold pk_rm.
    rewrite (lsc_rm_cnl cx t m si h j0 e1 h1 ev LB c2 O2 cap2 P HRI Hat Hrr) in HG. lia. }
  split; apply (lsc_rp_mono (pk_rm m h j0) _ (ablocks B ly0 S0) _ R); exact L.
Qed.
(* the arm's count row at its start (_remove_x.v:230 LS_cnt's conclusion, at pk_rm; ReplyLScntA.v rp_cnt_rm_A plugs
   the arm's guards) *)
Lemma rp_cnt_rm : forall cx t m ly S si h j0,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RP (pk_rm m h j0) (ablocks B ly S).
Proof.
  intros cx t m ly S si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs. apply lsc_rp_of_acnt.
  exact (fr_LS3cp_cnt_rm B cx t m ly S si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs).
Qed.

(* ================================================================== ARM_gone *)
(* relay_instance_gone's call at the cut *)
Lemma rp_cnt_gone_rig : forall cx t m ly S hs,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
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
  - exact (fr_LS3cp_cnt_gone B cx t m ly S hs HLS HRI Hgp Hm Ht HU Hpos Hoff).
  - intros P. unfold rig_pk, pk_gone. lia.
Qed.
(* a check_no_loss call at (lyx, Sx) on the lists (E, H): the count there plus this call's own trace peak is within the
   cut's count plus rig's trace peak and the sum over the table of gn_cnl (lsc_gn_cnl_open / lsc_gn_cnl_empty give this
   call's peak as its pair's gn_cnl; the earlier calls' growth is at most their peaks) *)
Lemma rp_cnt_gone_cnl : forall cx t m ly S hs (lyx : alayout) (Sx : astate) (E H : hlist),
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
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
  - exact (fr_LS3cp_cnt_gone B cx t m ly S hs HLS HRI Hgp Hm Ht HU Hpos Hoff).
  - intros P. specialize (HG P). unfold cnl_pk, pk_gone. lia.
Qed.
(* a check_shape_ends call at (lyx, Sx) *)
Lemma rp_cnt_gone_later : forall cx t m ly S hs (lyx : alayout) (Sx : astate),
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
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
  - exact (fr_LS3cp_cnt_gone B cx t m ly S hs HLS HRI Hgp Hm Ht HU Hpos Hoff).
  - intros P. specialize (HG P). unfold cshe_pk, pk_gone. lia.
Qed.

(* ================================================================== ARM_event *)
(* the malloc (re_len e) at the cut *)
Lemma rp_cnt_ev_malloc : forall cx t m ly S e,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  cnt_ok RP (ablocks B ly S).
Proof.
  intros cx t m ly S e HLS HRI He Hm Ht. unfold cnt_ok.
  apply (lsc_rp_mono (pk_event e) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_event B cx t m ly S e HLS HRI He Hm Ht).
  - intros P. cbv beta. unfold pk_event. lia.
Qed.
(* relay_event's call at (ly1, S1), the cut's blocks and the event's block (LS_event_relay's premise) *)
Lemma rp_cnt_ev_relay : forall cx t m ly S e (ly1 : alayout) (S1 : astate) q,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  cnt_ok_pk RP re_pk (ablocks B ly1 S1).
Proof.
  intros cx t m ly S e ly1 S1 q HLS HRI He Hm Ht E1.
  apply (lsc_rp_mono (pk_event e) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_event B cx t m ly S e HLS HRI He Hm Ht).
  - intros P. rewrite E1, lsc_acnt_snoc. unfold re_pk, pk_event. lia.
Qed.
(* the free's call at (ly2, S2): relay_event grew each count by at most re_pk *)
Lemma rp_cnt_ev_free : forall cx t m ly S e (ly1 ly2 : alayout) (S1 S2 : astate) q,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (forall P, (acnt P (ablocks B ly2 S2) <= acnt P (ablocks B ly1 S1) + re_pk P)%nat) ->
  cnt_ok RP (ablocks B ly2 S2).
Proof.
  intros cx t m ly S e ly1 ly2 S1 S2 q HLS HRI He Hm Ht E1 HG. unfold cnt_ok.
  apply (lsc_rp_mono (pk_event e) _ (ablocks B ly S)).
  - exact (fr_LS3cp_cnt_event B cx t m ly S e HLS HRI He Hm Ht).
  - intros P. specialize (HG P). cbv beta. rewrite E1, lsc_acnt_snoc in HG. unfold re_pk, pk_event in *. lia.
Qed.

(* ================================================================== SEG_EXIT *)
(* relay_finish's call at the cut *)
Lemma rp_cnt_exit_rf : forall cx t m ly S,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP rf_pk (ablocks B ly S).
Proof.
  intros cx t m ly S HLS HRI Hm Ht. apply lsc_rp_of_acnt. exact (fr_LS3cp_cnt_exit B cx t m ly S HLS HRI Hm Ht).
Qed.
(* check_shape_ends' and source_reset's calls at a later state (lyx, Sx): relay_finish grew each count by at most
   rf_pk *)
Lemma rp_cnt_exit_later : forall cx t m ly S (lyx : alayout) (Sx : astate),
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  (forall P, (acnt P (ablocks B lyx Sx) <= acnt P (ablocks B ly S) + rf_pk P)%nat) ->
  cnt_ok_pk RP cshe_pk (ablocks B lyx Sx) /\ cnt_ok_pk RP sr_pk (ablocks B lyx Sx).
Proof.
  intros cx t m ly S lyx Sx HLS HRI Hm Ht HG.
  pose proof (fr_LS3cp_cnt_exit B cx t m ly S HLS HRI Hm Ht) as R.
  split; apply (lsc_rp_mono pk_exit _ (ablocks B ly S) _ R); intros P; specialize (HG P);
    unfold cshe_pk, sr_pk, rf_pk, pk_exit in *; lia.
Qed.
End rp.

(* RP_CNT at top_x's RP_cf: its count fields are ReplyCnt.v's names *)
Lemma rp_cnt_cf : RP_CNT CfRBridgeRules.RP_cf.
Proof. exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))). Qed.
