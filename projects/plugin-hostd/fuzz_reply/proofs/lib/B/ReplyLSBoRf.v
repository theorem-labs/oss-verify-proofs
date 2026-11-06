(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* B's (5) LS_rf_room: relay_finish's room at LSx := fr_LS B CR /\ fr_OUT (lib/B/ReplyLSBo.v), the port of A's
   lib/A/ReplyLS3oRf.v.  proves no function (kind: invariant lemma).

   THE TEXT LS_rf_room_T CANNOT BE PROVED, AND SHOULD BE CHANGED.  ReplyLSBArms.v:241 states it over
   lx_rf_room_c3 (:185-192), whose threading after an entry is `bb + gse_cap r`: it ADDS the whole g_out capacity
   at every entry of the table instead of the change that entry makes to it.  After k entries the threaded bb is
   blocks_bytes S + sum of the k capacities, at least blocks_bytes S + k * lm_cap m, while the live bytes at that
   point are blocks_bytes S + (the capacity's growth) less what relay_finish freed.  rf_c3_inflates below is that
   gap, Qed-checked: an entry with NO keys asks nothing (gse_room_c3 of [] is True) and leaves the capacity where
   it was, yet the text still threads bb + cap into the next entry.  So a table of k such entries followed by one
   entry with a key demands blocks_bytes S + k * cap + peak <= LIVE_MAX.  At the capacities fr_OUT allows
   (up to 133,953,540) and the table lengths the model allows, that is false well before LIVE_MAX = 2 ^ 34.

   THE TEXT THAT HOLDS is A's (lib/A/ReplyLS3oRf.v, accepted by a Theorem Labs lane at 03:45Z): the same per-entry room
   gse_room_c3, threaded by the capacity's own CHANGE, `bb + gse_cap r - cap`.  That is an upper bound on the live
   bytes at the next entry, because relay_finish frees the entry's buffer and its key array and the only growth is
   g_out's.  lx_rf_room_p below is that text, and LS_rf_room_p_B proves it at LSx := fr_LS B CR /\ fr_OUT OM.

   ONE ADDED PREMISE, as in A: `0 <= t <= OPS_MAX` (the loop's own bound), which turns fr_OUT's MASS m <= 65535 * t
   into a number.  LS_rf_room_T has no t premise; the arm holds this one at every cut. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr RelayRunF send_line_b_c send_line_c gesture_end_b_c gestures_end_b_c relay_remove_b_c
  relay_instance_gone_b_c drain_b_c RelayCap SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBTrPeak ReplyLSBDrainPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBo.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).

(* ================================================================== what relay_finish sends *)
Definition kw5s (xs : list (list byte)) : Z := zsum (map (fun x => Z.of_nat (length x) + 5) xs).
Lemma kw5s_nil : kw5s [] = 0.
Proof. reflexivity. Qed.
Lemma kw5s_cons : forall x xs, kw5s (x :: xs) = Z.of_nat (length x) + 5 + kw5s xs.
Proof. reflexivity. Qed.
Lemma kw5s_nonneg : forall xs, 0 <= kw5s xs.
Proof. intros xs. apply bt_zsum_map_nonneg. intros x. lia. Qed.
Lemma kw5s_keys : forall e, kw5s (gse_keys e) = gestures_end_b_c.keys_total (re_keys e).
Proof.
  intros e. unfold kw5s, gse_keys. induction (re_keys e) as [|k ks IH]; [reflexivity|].
  cbn [map fold_right]. change (gestures_end_b_c.keys_total (k :: ks)) with
    (Z.of_nat (length (gestures_end_b_c.key_text k)) + 5 + gestures_end_b_c.keys_total ks). lia.
Qed.
Definition rf_sum (es : list rentry) : Z := zsum (map (fun e => kw5s (gse_keys e)) es).
Lemma rf_sum_nil : rf_sum [] = 0.
Proof. reflexivity. Qed.
Lemma rf_sum_cons : forall e es, rf_sum (e :: es) = kw5s (gse_keys e) + rf_sum es.
Proof. reflexivity. Qed.
Lemma rf_sum_nonneg : forall es, 0 <= rf_sum es.
Proof. intros es. apply bt_zsum_map_nonneg. intros e. apply kw5s_nonneg. Qed.
Lemma rf_sum_mass : forall es, rf_sum es <= MASSe es.
Proof.
  induction es as [|e es IH]; [cbn [rf_sum MASSe map fold_right]; lia|].
  unfold rf_sum, MASSe in *. cbn [map fold_right].
  pose proof (ou_keys_total_mass e) as H. rewrite (kw5s_keys e). lia.
Qed.
Lemma ou_keys_total_nonneg : forall ks, 0 <= gestures_end_b_c.keys_total ks.
Proof.
  induction ks as [|k ks IH]; [change (gestures_end_b_c.keys_total []) with 0; lia|].
  change (gestures_end_b_c.keys_total (k :: ks)) with
    (Z.of_nat (length (gestures_end_b_c.key_text k)) + 5 + gestures_end_b_c.keys_total ks). lia.
Qed.

(* ================================================================== a send that does not grow the buffer *)
Lemma ou_sl_nogrow : forall f mx no cap rem j o, 0 <= rem -> no + rem <= cap ->
  send_line_b_c.sl_run f mx no cap rem j o = ([], (cap, o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hr Hc; [reflexivity|].
  cbn [send_line_b_c.sl_run]. destruct (Z.leb_spec rem 0); [reflexivity|].
  pose proof (bt_n_le mx rem) as Hn.
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem) in *.
  destruct (Z.ltb_spec cap (no + n)); [lia|].
  apply IH; lia.
Qed.
Lemma ou_sl_tr_nogrow : forall live mx no cap len j o, 0 <= len -> no + len <= cap ->
  send_line_b_c.send_line_tr live mx no cap len j o = [] /\
  send_line_b_c.send_line_cap live mx no cap len = cap.
Proof.
  intros live mx no cap len j o Hl Hc.
  unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap. destruct live; [|split; reflexivity].
  rewrite (ou_sl_nogrow (Z.to_nat len) mx no cap len j o Hl Hc),
          (ou_sl_nogrow (Z.to_nat len) mx no cap len 0 RelayRunF.adr0 Hl Hc).
  split; reflexivity.
Qed.
Lemma ou_ge_nogrow : forall c mx no cap XL, 0 <= no -> 0 <= XL -> no + XL + 5 <= cap ->
  ge_tr c mx no cap XL = [] /\ ge_cap c mx no cap XL = cap.
Proof.
  intros c mx no cap XL Hno HX Hc.
  assert (E1 : send_line_b_c.send_line_cap (sl_live c XL) mx no cap XL = cap)
    by exact (proj2 (ou_sl_tr_nogrow (sl_live c XL) mx no cap XL 0 RelayRunF.adr0 HX ltac:(lia))).
  assert (Hsn : sl_no c no XL <= no + XL) by (unfold sl_no; destruct (sl_live c XL); lia).
  split.
  - unfold ge_tr, gesture_end_b_c.gesture_end_tr. cbv zeta.
    rewrite (proj1 (ou_sl_tr_nogrow (sl_live c XL) mx no cap XL 0 RelayRunF.adr0 HX ltac:(lia))).
    cbn [app RelayRunF.nretF]. rewrite E1.
    apply (proj1 (ou_sl_tr_nogrow (sl_live c XL) mx (no + XL) cap 5 _ _ ltac:(lia) ltac:(lia))).
  - unfold ge_cap, sl_cap. rewrite E1.
    exact (proj2 (ou_sl_tr_nogrow (sl_live (sl_ctl c XL) 5) mx (sl_no c no XL) cap 5 0 RelayRunF.adr0
             ltac:(lia) ltac:(lia))).
Qed.

(* ================================================================== the peak of one send and of gesture_end *)
Lemma ou_tr_net_pos : forall {P : Type} (tr : list (RelayRunT.rev P)), tr_net tr <= tr_pos tr.
Proof.
  intros P tr. induction tr as [|ev tr IH]; [cbn; lia|].
  rewrite tr_net_cons, tr_pos_cons. destruct ev; lia.
Qed.
Lemma ou_sl_peak_cap : forall live mx no cap len j o, 0 <= cap ->
  tr_peak (send_line_b_c.send_line_tr live mx no cap len j o) + cap <=
  2 * send_line_b_c.send_line_cap live mx no cap len.
Proof.
  intros live mx no cap len j o Hc.
  unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap. destruct live.
  - pose proof (tp_sl_peak_cap_run (Z.to_nat len) mx no cap len j o Hc) as H.
    rewrite sl_run_fin in H. rewrite sl_run_fin. exact H.
  - rewrite tr_peak_nil. lia.
Qed.
Lemma ou_two_sends_peak : forall live mx no cap len1 len2 j1 o1 j2 o2, 0 <= cap ->
  tr_peak (send_line_b_c.send_line_tr live mx no cap len1 j1 o1 ++
           send_line_b_c.send_line_tr live mx (no + len1)
             (send_line_b_c.send_line_cap live mx no cap len1) len2 j2 o2) + cap <=
  2 * send_line_b_c.send_line_cap live mx (no + len1)
        (send_line_b_c.send_line_cap live mx no cap len1) len2.
Proof.
  intros live mx no cap len1 len2 j1 o1 j2 o2 Hc.
  pose proof (ou_sl_peak_cap live mx no cap len1 j1 o1 Hc) as P1.
  pose proof (proj1 (tp_send_line live mx no cap len1 j1 o1 Hc)) as N1.
  pose proof (proj2 (tp_send_line live mx no cap len1 j1 o1 Hc)) as G1.
  pose proof (ou_tr_net_pos (send_line_b_c.send_line_tr live mx no cap len1 j1 o1)) as N2.
  pose proof (ou_sl_peak_cap live mx (no + len1) (send_line_b_c.send_line_cap live mx no cap len1) len2 j2 o2
                ltac:(lia)) as P2.
  pose proof (proj2 (tp_send_line live mx (no + len1) (send_line_b_c.send_line_cap live mx no cap len1) len2
                       j2 o2 ltac:(lia))) as G2.
  rewrite tr_peak_app. lia.
Qed.
Lemma ou_two_sends_net : forall live mx no cap len1 len2 j1 o1 j2 o2, 0 <= cap ->
  tr_net (send_line_b_c.send_line_tr live mx no cap len1 j1 o1 ++
          send_line_b_c.send_line_tr live mx (no + len1)
            (send_line_b_c.send_line_cap live mx no cap len1) len2 j2 o2) <=
  send_line_b_c.send_line_cap live mx (no + len1)
    (send_line_b_c.send_line_cap live mx no cap len1) len2 - cap.
Proof.
  intros live mx no cap len1 len2 j1 o1 j2 o2 Hc.
  pose proof (proj1 (tp_send_line live mx no cap len1 j1 o1 Hc)) as N1.
  pose proof (proj2 (tp_send_line live mx no cap len1 j1 o1 Hc)) as G1.
  pose proof (ou_tr_net_pos (send_line_b_c.send_line_tr live mx no cap len1 j1 o1)) as M1.
  pose proof (proj1 (tp_send_line live mx (no + len1) (send_line_b_c.send_line_cap live mx no cap len1) len2
                       j2 o2 ltac:(lia))) as N2.
  pose proof (ou_tr_net_pos (send_line_b_c.send_line_tr live mx (no + len1)
                 (send_line_b_c.send_line_cap live mx no cap len1) len2 j2 o2)) as M2.
  rewrite tr_net_app. lia.
Qed.
Lemma ou_sl_live_ge : forall c XL, sl_live c XL = true -> sl_live (sl_ctl c XL) 5 = true.
Proof.
  intros c XL H.
  unfold sl_live, send_line_c.send_live in H. apply andb_true_iff in H as (H1 & H2).
  apply negb_true_iff in H1. apply Z.eqb_eq in H2.
  unfold send_line_c.send_off in H1.
  apply orb_false_iff in H1 as (H12 & H3). apply orb_false_iff in H12 as (Hcl & Hbr).
  unfold sl_live, sl_ctl, send_line_c.send_live, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  rewrite Hcl, Hbr, H3, H2. reflexivity.
Qed.
Lemma ou_ge_tr_cap : forall c mx no cap XL, 0 <= cap ->
  send_line_b_c.send_line_cap (sl_live c XL) mx (no + XL)
    (send_line_b_c.send_line_cap (sl_live c XL) mx no cap XL) 5 <= ge_cap c mx no cap XL.
Proof.
  intros c mx no cap XL Hc.
  pose proof (proj2 (tp_send_line (sl_live c XL) mx no cap XL 0 RelayRunF.adr0 Hc)) as Hc1.
  unfold ge_cap, sl_cap.
  destruct (sl_live c XL) eqn:EL.
  - rewrite (ou_sl_live_ge c XL EL). unfold sl_no. rewrite EL. lia.
  - cbn [send_line_b_c.send_line_cap] in Hc1 |- *.
    exact (proj2 (tp_send_line (sl_live (sl_ctl c XL) 5) mx (sl_no c no XL) cap 5 0 RelayRunF.adr0 Hc)).
Qed.
Lemma ou_sl_cap_ge : forall c mx no cap len, 0 <= cap -> cap <= sl_cap c mx no cap len.
Proof.
  intros c mx no cap len Hc. unfold sl_cap.
  exact (proj2 (tp_send_line (sl_live c len) mx no cap len 0 RelayRunF.adr0 Hc)).
Qed.
Lemma ou_ge_cap_ge : forall c mx no cap XL, 0 <= cap -> cap <= ge_cap c mx no cap XL.
Proof.
  intros c mx no cap XL Hc. unfold ge_cap.
  pose proof (ou_sl_cap_ge c mx no cap XL Hc) as H1.
  pose proof (ou_sl_cap_ge (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5 ltac:(lia)) as H2. lia.
Qed.
Lemma ou_ge_cap_le : forall c mx no cap XL, 0 <= cap -> 0 <= XL ->
  ge_cap c mx no cap XL <= Z.max cap (2 * (no + (XL + 5))).
Proof.
  intros c mx no cap XL Hc HX. unfold ge_cap.
  pose proof (bt_cap_le c mx no cap XL) as H1.
  pose proof (bt_cap_le (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5) as H2.
  assert (Hn : sl_no c no XL <= no + XL) by (unfold sl_no; destruct (sl_live c XL); lia). lia.
Qed.
Lemma ou_ge_no : forall c no XL, 0 <= XL -> no <= ge_no c no XL <= no + (XL + 5).
Proof.
  intros c no XL HX. unfold ge_no, sl_no.
  destruct (sl_live c XL), (sl_live (sl_ctl c XL) 5); cbv beta iota; lia.
Qed.
Lemma ou_ge_peak : forall c mx no cap XL, 0 <= cap ->
  tr_peak (ge_tr c mx no cap XL) + cap <= 2 * ge_cap c mx no cap XL.
Proof.
  intros c mx no cap XL Hc.
  pose proof (ou_ge_tr_cap c mx no cap XL Hc) as HG.
  unfold ge_tr, gesture_end_b_c.gesture_end_tr. cbv zeta.
  pose proof (ou_two_sends_peak (sl_live c XL) mx no cap XL 5 0 RelayRunF.adr0
    (0 + RelayRunF.nretF (send_line_b_c.send_line_tr (sl_live c XL) mx no cap XL 0 RelayRunF.adr0))
    (send_line_b_c.send_line_out (sl_live c XL) mx no cap XL 0 RelayRunF.adr0) Hc) as H. lia.
Qed.
Lemma ou_ge_net : forall c mx no cap XL, 0 <= cap ->
  tr_net (ge_tr c mx no cap XL) <= ge_cap c mx no cap XL - cap.
Proof.
  intros c mx no cap XL Hc.
  pose proof (ou_ge_tr_cap c mx no cap XL Hc) as HG.
  unfold ge_tr, gesture_end_b_c.gesture_end_tr. cbv zeta.
  pose proof (ou_two_sends_net (sl_live c XL) mx no cap XL 5 0 RelayRunF.adr0
    (0 + RelayRunF.nretF (send_line_b_c.send_line_tr (sl_live c XL) mx no cap XL 0 RelayRunF.adr0))
    (send_line_b_c.send_line_out (sl_live c XL) mx no cap XL 0 RelayRunF.adr0) Hc) as H. lia.
Qed.
Lemma ou_ge_max : forall c mx no cap XL M, 0 <= no -> 0 <= XL -> 2 * (no + XL + 5) <= M ->
  tr_max (ge_tr c mx no cap XL) <= M.
Proof.
  intros c mx no cap XL M Hno HX HM.
  assert (M0 : 0 <= M) by lia.
  unfold ge_tr, gesture_end_b_c.gesture_end_tr. cbv zeta. rewrite tr_max_app'.
  apply Z.max_lub.
  - apply (dpre_tr_max _ M M0). apply dpre_send_line. lia.
  - apply (dpre_tr_max _ M M0). apply dpre_send_line. lia.
Qed.

(* ================================================================== gestures_end and relay_finish, by capacity *)
Lemma ou_gse_cap : forall xs c O mx no cap, 0 <= cap ->
  cap <= gse_cap (gse_run c O mx no cap xs) /\
  gse_cap (gse_run c O mx no cap xs) <= Z.max cap (2 * (no + kw5s xs)) /\
  no <= gse_no (gse_run c O mx no cap xs) <= no + kw5s xs.
Proof.
  induction xs as [|x xs IH]; intros c O mx no cap Hc.
  - cbn [gse_run gse_cap gse_no snd fst]. rewrite kw5s_nil. repeat split; lia.
  - cbn [gse_run]. rewrite kw5s_cons.
    set (XL := Z.of_nat (length x)) in *.
    assert (HX : 0 <= XL) by (unfold XL; lia).
    pose proof (ou_ge_cap_ge c mx no cap XL Hc) as G1.
    pose proof (ou_ge_cap_le c mx no cap XL Hc HX) as G2.
    pose proof (ou_ge_no c no XL HX) as G3.
    destruct (IH (ge_ctl c XL) (ge_O c O x) mx (ge_no c no XL) (ge_cap c mx no cap XL) ltac:(lia))
      as (I1 & I2 & I3).
    pose proof (kw5s_nonneg xs). repeat split; lia.
Qed.
Lemma ou_gse_nogrow : forall xs c O mx no cap, 0 <= no -> 2 * (no + kw5s xs) <= cap ->
  gse_cap (gse_run c O mx no cap xs) = cap.
Proof.
  induction xs as [|x xs IH]; intros c O mx no cap Hno Hc; [reflexivity|].
  rewrite kw5s_cons in Hc. cbn [gse_run].
  set (XL := Z.of_nat (length x)) in *.
  assert (HX : 0 <= XL) by (unfold XL; lia).
  pose proof (kw5s_nonneg xs) as Hk.
  pose proof (ou_ge_no c no XL HX) as G3.
  destruct (ou_ge_nogrow c mx no cap XL Hno HX ltac:(lia)) as (_ & EC).
  rewrite IH; [exact EC | lia | rewrite EC; lia].
Qed.

(* ================================================================== relay_finish's room, in the text that holds *)
(* ReplyLSBArms.v:185-192 lx_rf_room_c3 with the threading at the capacity's own change *)
Fixpoint lx_rf_room_p (MX bb : Z) (c : ctl) (O : list byte) (mx no cap : Z) (es : list rentry) : Prop :=
  match es with
  | [] => True
  | e :: es' => let r := gse_run c O mx no cap (gse_keys e) in
      gse_room_c3 MX bb c mx no cap (gse_keys e) /\
      lx_rf_room_p MX (bb + gse_cap r - cap) (gse_c r) (gse_O r) mx (gse_no r) (gse_cap r) es'
  end.

(* THE GAP, Qed-checked: an entry with no keys asks nothing and leaves the capacity where it was, yet
   lx_rf_room_c3 threads bb + cap into the rest of the table *)
Lemma rf_c3_inflates : forall MX bb c O mx no cap e es, gse_keys e = [] ->
  (lx_rf_room_c3 MX bb c O mx no cap (e :: es) <-> lx_rf_room_c3 MX (bb + cap) c O mx no cap es) /\
  (lx_rf_room_p MX bb c O mx no cap (e :: es) <-> lx_rf_room_p MX bb c O mx no cap es).
Proof.
  intros MX bb c O mx no cap e es HK.
  assert (Er : gse_run c O mx no cap (gse_keys e) = (c, O, no, cap)) by (rewrite HK; reflexivity).
  split; cbn [lx_rf_room_c3 lx_rf_room_p]; cbv zeta; rewrite Er, HK;
    cbn [gse_room_c3 gse_c gse_O gse_no gse_cap fst snd].
  - split; [intros (_ & H); exact H | intros H; split; [exact I | exact H]].
  - replace (bb + cap - cap) with bb by lia.
    split; [intros (_ & H); exact H | intros H; split; [exact I | exact H]].
Qed.

(* the induction's invariant (A ReplyLS3oRf.v): either the buffer already holds everything the run can send, or
   the live bytes plus twice the largest capacity the run can reach are within LIVE_MAX *)
Definition ou_inv (M Mx bb cap : Z) : Prop :=
  (M <= cap /\ bb <= LIVE_MAX) \/ (cap <= Mx /\ bb + 2 * Mx - cap <= LIVE_MAX).

Lemma ou_gse_room_p : forall xs MX M Mx c mx no cap bb,
  0 <= cap -> 0 <= no -> 0 <= M -> M <= Mx -> M < MX ->
  2 * (no + kw5s xs) <= M -> ou_inv M Mx bb cap ->
  gse_room_c3 MX bb c mx no cap xs.
Proof.
  induction xs as [|x xs IH]; intros MX M Mx c mx no cap bb Hc Hno HM0 HMx HMX HS HI; [exact I|].
  rewrite kw5s_cons in HS.
  set (XL := Z.of_nat (length x)) in *.
  assert (HX : 0 <= XL) by (unfold XL; lia).
  pose proof (kw5s_nonneg xs) as Hk.
  pose proof (ou_ge_cap_ge c mx no cap XL Hc) as G1.
  pose proof (ou_ge_cap_le c mx no cap XL Hc HX) as G2.
  pose proof (ou_ge_no c no XL HX) as G3.
  cbn [gse_room_c3]. fold XL. split.
  - unfold ge_room_c3. split.
    + pose proof (ou_ge_max c mx no cap XL M Hno HX ltac:(lia)). lia.
    + destruct HI as [(HA1 & HA2) | (HB1 & HB2)].
      * destruct (ou_ge_nogrow c mx no cap XL Hno HX ltac:(lia)) as (ET & _).
        rewrite ET, tr_peak_nil. lia.
      * pose proof (ou_ge_peak c mx no cap XL Hc). lia.
  - apply (IH MX M Mx (ge_ctl c XL) mx (ge_no c no XL) (ge_cap c mx no cap XL)); try lia.
    destruct HI as [(HA1 & HA2) | (HB1 & HB2)].
    + destruct (ou_ge_nogrow c mx no cap XL Hno HX ltac:(lia)) as (ET & EC).
      left. rewrite EC. split; [lia|]. rewrite ET. cbn [tr_net fold_right]. lia.
    + right. pose proof (ou_ge_net c mx no cap XL Hc). lia.
Qed.

Lemma ou_lx_rf_room_p : forall es MX M Mx c O mx no cap bb,
  0 <= cap -> 0 <= no -> 0 <= M -> M <= Mx -> M < MX ->
  2 * (no + rf_sum es) <= M -> ou_inv M Mx bb cap ->
  lx_rf_room_p MX bb c O mx no cap es.
Proof.
  induction es as [|e es IH]; intros MX M Mx c O mx no cap bb Hc Hno HM0 HMx HMX HS HI; [exact I|].
  rewrite rf_sum_cons in HS.
  pose proof (rf_sum_nonneg es) as Hr.
  pose proof (kw5s_nonneg (gse_keys e)) as Hk.
  destruct (ou_gse_cap (gse_keys e) c O mx no cap Hc) as (C1 & C2 & C3).
  cbn [lx_rf_room_p]. cbv zeta. split.
  - apply (ou_gse_room_p (gse_keys e) MX M Mx c mx no cap bb); try lia. exact HI.
  - apply (IH MX M Mx (gse_c (gse_run c O mx no cap (gse_keys e))) (gse_O (gse_run c O mx no cap (gse_keys e)))
             mx (gse_no (gse_run c O mx no cap (gse_keys e))) (gse_cap (gse_run c O mx no cap (gse_keys e))));
      try lia.
    destruct HI as [(HA1 & HA2) | (HB1 & HB2)].
    + left. rewrite (ou_gse_nogrow (gse_keys e) c O mx no cap Hno ltac:(lia)). lia.
    + right. lia.
Qed.

(* ================================================================== (5) at LSx := fr_LS B CR /\ fr_OUT OM *)
(* the room relay_finish needs above LS_OVER, in B's own form (ReplyLSBArms.v:415, :556): twice the bytes one call
   can send, 4 * 65,535 * OPS_MAX *)
Definition R_rf : Z := 134215680.
Lemma R_rf_val : R_rf = 4 * WMAX * OPS_MAX.
Proof. reflexivity. Qed.
Lemma R_rf_fits : LS_OVER + R_rf <= YCfn_cf.CALL_ROOM_B.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Section brf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* at any room `blocks_bytes S + CR <= LIVE_MAX + OVER` with OVER + R_rf <= CR: fr_LS (v2) gives it at
   OVER := LS_OVER (bt_LS_room), fr_LS3 (v3) at OVER := LS3_OVER (lib/B/ReplyB3LS3.v fr_LS3_room_rel) *)
Lemma LS_rf_room_p_room : forall OVER CR OM, OVER + R_rf <= CR -> forall cx t m ly S,
  blocks_bytes S + CR <= LIVE_MAX + OVER -> fr_OUT OM cx t m ly S -> 0 <= t <= OPS_MAX ->
  lx_rf_room_p fr_MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).
Proof.
  intros OVER CR OM HCR cx t m ly S Hroom (U1 & U2 & U3 & U4) Ht.
  pose proof (rf_sum_mass (lm_es m)) as Hrf.
  assert (Hmass : MASSe (lm_es m) <= MASS m).
  { unfold MASS. assert (0 <= pend_bytes m) by (apply bt_zsum_map_nonneg; exact bt_slot_pend_nonneg). lia. }
  assert (HM : fr_MMAX = 1072693248) by (vm_compute; reflexivity).
  assert (HL : LIVE_MAX = 17179869184) by (vm_compute; reflexivity).
  apply (ou_lx_rf_room_p (lm_es m) fr_MMAX (2 * (WMAX * OPS_MAX)) (Z.max (lm_cap m) (2 * (WMAX * OPS_MAX)))
          (lm_c m) [] (lm_mx m) 0 (lm_cap m) (blocks_bytes S));
    unfold WMAX, OPS_MAX, R_rf in *; try lia.
  unfold ou_inv. destruct (Z_le_gt_dec (2 * (65535 * 512)) (lm_cap m)); [left | right]; lia.
Qed.
Lemma LS_rf_room_p_CR : forall CR OM, LS_OVER + R_rf <= CR -> forall cx t m ly S,
  fr_LS B CR cx t m ly S -> fr_OUT OM cx t m ly S -> 0 <= t <= OPS_MAX ->
  lx_rf_room_p fr_MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).
Proof.
  intros CR OM HCR cx t m ly S HLS.
  exact (LS_rf_room_p_room LS_OVER CR OM HCR cx t m ly S (bt_LS_room B CR cx t m ly S HLS)).
Qed.

(* the B instance, at the driver's call room *)
Lemma LS_rf_room_p_B : forall OM cx t m ly S,
  fr_LS B YCfn_cf.CALL_ROOM_B cx t m ly S -> fr_OUT OM cx t m ly S -> 0 <= t <= OPS_MAX ->
  lx_rf_room_p fr_MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).
Proof. intros OM. exact (LS_rf_room_p_CR YCfn_cf.CALL_ROOM_B OM R_rf_fits). Qed.
End brf.
