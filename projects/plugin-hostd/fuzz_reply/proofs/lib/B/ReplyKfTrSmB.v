(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the secondary-request counts of fuzz_reply's small request traces and meter charges. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyKfTrSm.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyKfTrSm.v, with its module paths and module names changed. *)
(* The small traces: for list_push, send_line, relay_event (its send and the event arm's own copy), gesture_end,
   gestures_end, relay_finish, relay_add, op_add and list_drop, the count nsec_tr (ReplyKfNsecB.v) of the trace's
   secondary requests is at most a named constant KC_x (lemma kf_x); each spec's meter charge at a KF meter
   (mo_malloc n = if 64512 <? n then 1 else 0, mo_free = 0, as ReplyKfMeterB.MT_sec) is at most the same constant
   (lemma kf_x_cost).  Image B's twin of lib/A/ReplyKfTrSm.v: the same names and statements over lib/B's modules (each
   lib/B definition used here is text-identical to lib/A's), the same proofs.  proves no function (kind: segment lemma).
   - The g_out chain (send_line, gesture_end, gestures_end, relay_finish): ReplyKfChainB.v's growth potential kf_lg and
     chain kf_ch (kf_send, kf_gend, kf_ker), extended here to gestures_end's key run in W_contract's threading
     (kf_gse_ch, W_tr_peak.gse_tr: keys not empty, as W_tr_cnt.tc_gse) and to relay_finish's entry run (kf_eer_ch).
     A chain whose requests are below 2 ^ 30 counts at most 15 (kf_ch_15): the specs' request bound is below MMAX
     (sl_maxr, ge_room, gse_room, rf_room) and CfParamsReplyB.reply_HMMAX gives fr_MMAX <= 2 ^ 30.  No cap premise.
   - list_push: one vector growth and one text copy (2); relay_event's own copy malloc (re_len e) (1).
   - relay_add / op_add under ra_spec's table premise (0 <= fd -> T = 0 \/ N <> C: only the 896-byte table), and
     list_drop (one free): 0.
   - The charges: lp_cost, sl_cost (relay_event's too), ge_cost, gse_cost are the counts of their traces (sl_cost_nsec,
     ge_cost_nsec, gse_cost_nsec); rf_cost is one chain over the entries' gestures_end runs (rf_cost_ch); ra_cost is
     0 (ATABLE = 896 is primary). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_kit W_journal W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YI00 YN0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr RelayRunF send_line_c send_line_b_c gesture_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  gestures_end_b_c relay_finish_b_c relay_add_b_c HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_tr_cnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyKfNsecB ReplyKfChainB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== the constants *)
Definition KC_lp : Z := 2.
Definition KC_sl : Z := 15.
Definition KC_re : Z := 15.
Definition KC_ev : Z := 1.
Definition KC_ge : Z := 15.
Definition KC_gse : Z := 15.
Definition KC_rf : Z := 15.
Definition KC_ra : Z := 0.
Definition KC_oa : Z := 0.
Definition KC_ldrop : Z := 0.

(* ================================================================== helpers *)
Lemma kf_nsec_free : forall (P : Type) k (a : RelayRunT.addr P) (r : list (RelayRunT.rev P)),
  nsec_tr (RelayRunT.RFree k a :: r) = nsec_tr r.
Proof. reflexivity. Qed.
Lemma kf_nsec_mcons : forall (P : Type) n (r : list (RelayRunT.rev P)),
  nsec_tr (RelayRunT.RMalloc n :: r) = (if 64512 <? n then 1 else 0) + nsec_tr r.
Proof. reflexivity. Qed.
Lemma kf_nsec_rcons : forall (P : Type) k n (a : RelayRunT.addr P) (r : list (RelayRunT.rev P)),
  nsec_tr (RelayRunT.RRealloc k n a :: r) = (if 64512 <? n then 1 else 0) + nsec_tr r.
Proof. reflexivity. Qed.
(* a primary malloc counts nothing *)
Lemma kf_nsec_prim1 : forall (P : Type) n, n <= 64512 -> nsec_tr [@RelayRunT.RMalloc P n] = 0.
Proof.
  intros P n H. rewrite kf_nsec_mcons, nsec_tr_nil, (proj2 (Z.ltb_ge 64512 n) H). reflexivity.
Qed.

Lemma kf_tm_free : forall (P : Type) k (a : RelayRunT.addr P) (r : list (RelayRunT.rev P)),
  tr_max (RelayRunT.RFree k a :: r) = tr_max r.
Proof. reflexivity. Qed.

Lemma kf_nsec_len : forall (P : Type) (t : list (RelayRunT.rev P)), nsec_tr t <= Z.of_nat (length t).
Proof.
  intros P t. induction t as [|[n|k a|k n a] r IH]; cbn [length].
  - rewrite nsec_tr_nil. lia.
  - rewrite kf_nsec_mcons. destruct (64512 <? n); cbv beta iota; lia.
  - rewrite kf_nsec_free. lia.
  - rewrite kf_nsec_rcons. destruct (64512 <? n); cbv beta iota; lia.
Qed.

(* ================================================================== the g_out chains (ReplyKfChainB.v's kf_ch) *)
(* gestures_end's key run in W_contract's threading (each key's ge_tr, then free (key)); the keys are not empty, so
   ge_cap is the key's own final cap (W_tr_cnt.ge_cap_tr) *)
Lemma kf_gse_ch : forall xs c O mx no cap, Forall (fun x : list byte => x <> []) xs ->
  kf_ch cap (gse_tr c mx no cap xs) (gse_cap (gse_run c O mx no cap xs)).
Proof.
  intros xs. induction xs as [|x xs IH]; intros c O mx no cap HF.
  - cbn [gse_tr gse_run gse_cap snd]. apply kf_ch_nil.
  - apply Forall_cons_iff in HF as [Hx HF].
    assert (HXL : Z.of_nat (length x) <> 0) by (destruct x as [|b x]; [congruence | cbn [length]; lia]).
    assert (H1 : kf_ch cap (ge_tr c mx no cap (Z.of_nat (length x))) (ge_cap c mx no cap (Z.of_nat (length x)))).
    { rewrite (W_tr_cnt.ge_cap_tr c mx no cap _ HXL). unfold ge_tr. apply kf_gend. }
    cbn [gse_tr gse_run]. eapply kf_ch_app; [exact H1|]. apply kf_ch_free_cons. apply IH. exact HF.
Qed.

(* gestures_end (s): the key run, then free (s->held) *)
Lemma kf_gsend_ch : forall live mx no cap xks HP KH j o ha,
  kf_ch cap (gestures_end_b_c.gestures_end_tr live mx no cap xks HP KH j o ha)
    (fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks j o))).
Proof.
  intros live mx no cap xks HP KH j o ha. unfold gestures_end_b_c.gestures_end_tr.
  eapply kf_ch_app; [apply kf_ker|]. destruct (HP =? 0); [apply kf_ch_nil | apply kf_ch_free_cons, kf_ch_nil].
Qed.

(* relay_finish's entry run: per entry the free of s->buf, then gestures_end on the one g_out chain *)
Lemma kf_eer_ch : forall nm live mx es no cap j o,
  kf_ch cap (fst (relay_finish_b_c.entries_end_run nm live mx no cap es j o))
    (fst (snd (relay_finish_b_c.entries_end_run nm live mx no cap es j o))).
Proof.
  intros nm live mx es. induction es as [|e r IH]; intros no cap j o;
    cbn [relay_finish_b_c.entries_end_run fst snd]; [apply kf_ch_nil|].
  apply (kf_ch_app _ cap cap); [destruct (re_cap e =? 0); [apply kf_ch_nil | apply kf_ch_free_cons, kf_ch_nil]|].
  match goal with |- kf_ch _ (gestures_end_b_c.gestures_end_tr _ _ _ _ _ _ _ ?J _ _ ++ _) _ =>
    rewrite (W_tr_cnt.ge_cap_of_keys nm live mx no cap (re_keys e) J o);
    pose proof (kf_gsend_ch live mx no cap (gestures_end_b_c.key_runs nm (re_keys e)) (re_hp e) (re_kh e) J o
      (nm (re_hp e))) as H1
  end.
  eapply kf_ch_app; [exact H1|]. apply IH.
Qed.

(* ================================================================== the per-trace counts *)
(* list_push (lp_tr, W_contract.v): the vector's growth, then strndup's malloc (n + 1) *)
Lemma kf_lp : forall l n, nsec_tr (lp_tr l n) <= KC_lp.
Proof.
  intros l n. eapply Z.le_trans; [apply kf_nsec_len|]. unfold KC_lp, lp_tr, ListTr.list_push_tra.
  destruct (hl_n l =? hl_cap l); [destruct (hl_cap l =? 0)|]; cbn [app length]; lia.
Qed.

(* send_line: its largest request is sl_maxr (sl_spec's pre bounds it by MMAX) *)
Lemma kf_sl_max_run : forall f mx no cap rem j o,
  tr_max (fst (send_line_b_c.sl_run f mx no cap rem j o)) = sl_max_run f mx no cap rem.
Proof.
  intros f. induction f as [|f IH]; intros mx no cap rem j o; cbn [send_line_b_c.sl_run sl_max_run];
    [reflexivity|].
  destruct (rem <=? 0); [reflexivity|].
  match goal with |- context [if ?b then mx else rem] => generalize (if b then mx else rem); intros n end.
  destruct (cap <? no + n); cbv beta iota; [|apply IH].
  cbn [fst]. rewrite <- (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j)).
  destruct (cap =? 0); reflexivity.
Qed.
Lemma kf_sl_maxr : forall c mx no cap len, tr_max (sl_tr c mx no cap len) = sl_maxr c mx no cap len.
Proof.
  intros c mx no cap len. unfold sl_tr, sl_maxr, send_line_b_c.send_line_tr.
  destruct (sl_live c len); [apply kf_sl_max_run | reflexivity].
Qed.

Lemma kf_sl : forall c mx no cap len, sl_maxr c mx no cap len < 2 ^ 30 -> nsec_tr (sl_tr c mx no cap len) <= KC_sl.
Proof.
  intros c mx no cap len H. rewrite <- kf_sl_maxr in H. unfold KC_sl.
  exact (kf_ch_15 _ _ _ _ (kf_send (sl_live c len) mx no cap len 0 RelayRunF.adr0) H).
Qed.

(* relay_event: send_line (line, re_len e) (re_spec's trace and request bound) *)
Lemma kf_re : forall c mx no cap (e : list byte), sl_maxr c mx no cap (re_len e) < 2 ^ 30 ->
  nsec_tr (sl_tr c mx no cap (re_len e)) <= KC_re.
Proof. intros c mx no cap e H. exact (kf_sl c mx no cap (re_len e) H). Qed.

(* the event arm's own copy of the line, malloc (slen + 1) (one request) *)
Lemma kf_ev : forall (P : Type) (n : Z), nsec_tr [@RelayRunT.RMalloc P n] <= KC_ev.
Proof. intros P n. rewrite kf_nsec_mcons, nsec_tr_nil. unfold KC_ev. destruct (64512 <? n); cbv beta iota; lia. Qed.

(* gesture_end: ge_room's request bound *)
Lemma kf_ge : forall c mx no cap XL, tr_max (ge_tr c mx no cap XL) < 2 ^ 30 -> nsec_tr (ge_tr c mx no cap XL) <= KC_ge.
Proof.
  intros c mx no cap XL H. unfold KC_ge.
  exact (kf_ch_15 _ _ _ _ (kf_gend (sl_live c XL) mx no cap XL 0 RelayRunF.adr0) H).
Qed.

(* gestures_end: the key run of W_tr_peak.gse_tr; gse_room gives its request bound (gse_room_tr_max) *)
Lemma gse_room_tr_max : forall MMAX xs bb c mx no cap, 0 < MMAX ->
  gse_room MMAX bb c mx no cap xs -> tr_max (gse_tr c mx no cap xs) < MMAX.
Proof.
  intros MMAX xs. induction xs as [|x xs IH]; intros bb c mx no cap HM HR; cbn [gse_tr].
  - unfold tr_max. cbn [fold_right]. exact HM.
  - cbn [gse_room] in HR. unfold ge_room in HR. destruct HR as [[H1 _] H2].
    rewrite kf_tm_app, kf_tm_free. pose proof (IH _ _ _ _ _ HM H2). lia.
Qed.

Lemma kf_gse : forall c mx no cap xs, Forall (fun x : list byte => x <> []) xs ->
  tr_max (gse_tr c mx no cap xs) < 2 ^ 30 -> nsec_tr (gse_tr c mx no cap xs) <= KC_gse.
Proof.
  intros c mx no cap xs HF H. unfold KC_gse.
  exact (kf_ch_15 _ _ _ _ (kf_gse_ch xs c [] mx no cap HF) H).
Qed.

(* relay_finish: the plain model's trace (Prog/relay_finish_b_c.v) *)
Lemma kf_rf : forall nm live mx no cap es j o,
  tr_max (relay_finish_b_c.relay_finish_tr nm live mx no cap es j o) < 2 ^ 30 ->
  nsec_tr (relay_finish_b_c.relay_finish_tr nm live mx no cap es j o) <= KC_rf.
Proof.
  intros nm live mx no cap es j o H. unfold KC_rf. unfold relay_finish_b_c.relay_finish_tr in *.
  exact (kf_ch_15 _ _ _ _ (kf_eer_ch nm live mx es no cap j o) H).
Qed.

(* relay_add: under ra_spec's table premise the only request is the 896-byte table *)
Lemma kf_ra : forall FD N C g, (0 <= FD -> C = 0 \/ N <> C) ->
  nsec_tr (relay_add_b_c.relay_add_tr FD N C g) <= KC_ra.
Proof.
  intros FD N C g H.
  assert (E : relay_add_b_c.relay_add_tr FD N C g = [] \/
              relay_add_b_c.relay_add_tr FD N C g = [RelayRunT.RMalloc 896]).
  { unfold relay_add_b_c.relay_add_tr.
    destruct (Z.ltb_spec FD 0) as [HF|HF]; [left; reflexivity|].
    destruct (Z.eqb_spec N C) as [E|E]; [|left; reflexivity].
    destruct (H HF) as [->|H']; [|contradiction]. right; reflexivity. }
  unfold KC_ra. destruct E as [E|E]; rewrite E; [rewrite nsec_tr_nil | rewrite kf_nsec_prim1 by lia]; lia.
Qed.

(* op_add: the 6000-byte buffer, then relay_add *)
Lemma kf_oa : forall i FD N C g, (0 <= FD -> C = 0 \/ N <> C) ->
  nsec_tr (HarnessTr.op_add_tr i FD N C g) <= KC_oa.
Proof.
  intros i FD N C g H. unfold HarnessTr.op_add_tr. destruct i as [i|]; [|rewrite nsec_tr_nil; unfold KC_oa; lia].
  rewrite kf_nsec_mcons. pose proof (kf_ra FD N C g H) as R. unfold KC_ra, KC_oa in *.
  replace (64512 <? 6000) with false by reflexivity. cbv beta iota. lia.
Qed.

(* list_drop: one free *)
Lemma kf_ldrop : forall a n, nsec_tr (ListTr.list_drop_tra a n) <= KC_ldrop.
Proof. intros a n. unfold ListTr.list_drop_tra, KC_ldrop. rewrite kf_nsec_free, nsec_tr_nil. lia. Qed.

(* ================================================================== the specs' meter charges at a KF meter *)
Section sec.
Variable MT : ameter_ops.
Hypothesis HMs : forall n, mo_malloc MT n = if 64512 <? n then 1 else 0.
Hypothesis HFs : mo_free MT = 0.

Lemma kf_lp_cost : forall l n, lp_cost MT l n <= KC_lp.
Proof.
  intros l n. unfold lp_cost, KC_lp. rewrite !HMs, HFs. destruct (lp_grow l);
    repeat match goal with |- context [64512 <? ?x] => destruct (64512 <? x) end; cbv beta iota; lia.
Qed.

Lemma kf_sl_cost_run : forall f mx no cap rem j o,
  sl_cost_run MT f mx no cap rem = nsec_tr (fst (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
  intros f. induction f as [|f IH]; intros mx no cap rem j o; cbn [sl_cost_run send_line_b_c.sl_run];
    [reflexivity|].
  destruct (rem <=? 0); [reflexivity|].
  match goal with |- context [if ?b then mx else rem] => generalize (if b then mx else rem); intros n end.
  destruct (cap <? no + n); cbv beta iota; [|apply IH].
  cbn [fst]. rewrite (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j)), HMs, HFs.
  destruct (cap =? 0); [rewrite kf_nsec_mcons | rewrite kf_nsec_rcons]; lia.
Qed.
Lemma kf_nsec_send : forall live mx no cap len j o,
  nsec_tr (send_line_b_c.send_line_tr live mx no cap len j o) =
  if live then sl_cost_run MT (Z.to_nat len) mx no cap len else 0.
Proof.
  intros live mx no cap len j o. unfold send_line_b_c.send_line_tr.
  destruct live; [symmetry; apply kf_sl_cost_run | reflexivity].
Qed.
Lemma sl_cost_nsec : forall c mx no cap len, sl_cost MT c mx no cap len = nsec_tr (sl_tr c mx no cap len).
Proof. intros c mx no cap len. unfold sl_tr, sl_cost. rewrite kf_nsec_send. reflexivity. Qed.

Lemma kf_sl_cost : forall c mx no cap len, sl_maxr c mx no cap len < 2 ^ 30 -> sl_cost MT c mx no cap len <= KC_sl.
Proof. intros c mx no cap len H. rewrite sl_cost_nsec. exact (kf_sl c mx no cap len H). Qed.

Lemma kf_re_cost : forall c mx no cap (e : list byte), sl_maxr c mx no cap (re_len e) < 2 ^ 30 ->
  sl_cost MT c mx no cap (re_len e) <= KC_re.
Proof. intros c mx no cap e H. rewrite sl_cost_nsec. exact (kf_re c mx no cap e H). Qed.

Lemma kf_ev_cost : forall n, mo_malloc MT n <= KC_ev.
Proof. intros n. rewrite HMs. unfold KC_ev. destruct (64512 <? n); cbv beta iota; lia. Qed.

(* gesture_end's charge is its trace's count when the key is not empty (both sends live together, ge_live5) *)
Lemma ge_cost_nsec : forall c mx no cap XL, XL <> 0 -> ge_cost MT c mx no cap XL = nsec_tr (ge_tr c mx no cap XL).
Proof.
  intros c mx no cap XL HXL. unfold ge_cost, ge_tr, gesture_end_b_c.gesture_end_tr. cbv zeta.
  rewrite nsec_tr_app, !kf_nsec_send. unfold sl_cost, sl_no, sl_cap. rewrite (ge_live5 c XL HXL).
  destruct (sl_live c XL); reflexivity.
Qed.

Lemma kf_ge_cost : forall MMAX bb c mx no cap XL, MMAX <= 2 ^ 30 -> XL <> 0 ->
  ge_room MMAX bb c mx no cap XL -> ge_cost MT c mx no cap XL <= KC_ge.
Proof.
  intros MMAX bb c mx no cap XL HM HXL [HR _]. rewrite (ge_cost_nsec c mx no cap XL HXL).
  apply kf_ge. lia.
Qed.

Lemma gse_cost_nsec : forall xs c mx no cap, Forall (fun x : list byte => x <> []) xs ->
  gse_cost MT c mx no cap xs = nsec_tr (gse_tr c mx no cap xs).
Proof.
  intros xs. induction xs as [|x xs IH]; intros c mx no cap HF; cbn [gse_cost gse_tr].
  - rewrite HFs, nsec_tr_nil. reflexivity.
  - apply Forall_cons_iff in HF as [Hx HF].
    assert (HXL : Z.of_nat (length x) <> 0) by (destruct x as [|b x]; [congruence | cbn [length]; lia]).
    rewrite nsec_tr_app, kf_nsec_free, (ge_cost_nsec c mx no cap _ HXL), HFs, IH by exact HF. lia.
Qed.

Lemma kf_gse_cost : forall MMAX bb c mx no cap xs, 0 < MMAX <= 2 ^ 30 -> Forall (fun x : list byte => x <> []) xs ->
  gse_room MMAX bb c mx no cap xs -> gse_cost MT c mx no cap xs <= KC_gse.
Proof.
  intros MMAX bb c mx no cap xs HM HF HR. rewrite (gse_cost_nsec xs c mx no cap HF).
  pose proof (gse_room_tr_max MMAX xs bb c mx no cap ltac:(lia) HR). apply kf_gse; [exact HF | lia].
Qed.

(* relay_finish's charge: one chain over the entries' gestures_end runs (rf_run threads g_out's cap) *)
Lemma rf_cost_ch : forall MMAX es bb c O mx no cap, 0 < MMAX ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) es ->
  rf_room MMAX bb c O mx no cap es ->
  rf_cost MT c O mx no cap es + kf_lg cap <= kf_lg (gse_cap (rf_run c O mx no cap es)) /\
  gse_cap (rf_run c O mx no cap es) <= Z.max cap MMAX.
Proof.
  intros MMAX es. induction es as [|e es IH]; intros bb c O mx no cap HM HF HR.
  - cbn [rf_cost rf_run gse_cap snd]. split; lia.
  - apply Forall_cons_iff in HF as [He HF]. cbn [rf_room] in HR. destruct HR as [HR1 HR2].
    cbn [rf_cost rf_run].
    destruct (kf_gse_ch (gse_keys e) c O mx no cap He) as [G1 G2].
    pose proof (gse_room_tr_max MMAX (gse_keys e) bb c mx no cap HM HR1) as GM.
    rewrite (gse_cost_nsec (gse_keys e) c mx no cap He), HFs.
    destruct (IH _ _ _ _ _ _ HM HF HR2) as [I1 I2].
    split; lia.
Qed.

Lemma kf_rf_cost : forall MMAX bb c O mx no cap es, 0 < MMAX <= 2 ^ 30 ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) es ->
  rf_room MMAX bb c O mx no cap es -> rf_cost MT c O mx no cap es <= KC_rf.
Proof.
  intros MMAX bb c O mx no cap es HM HF HR.
  destruct (rf_cost_ch MMAX es bb c O mx no cap ltac:(lia) HF HR) as [R1 R2].
  pose proof (kf_lg_mono _ _ R2) as L. pose proof (kf_lg_mono MMAX (2 ^ 30) ltac:(lia)) as L2.
  rewrite kf_lg_2_30 in L2. pose proof (kf_lg_nonneg cap). unfold KC_rf.
  destruct (Z.le_gt_cases cap MMAX) as [Hc|Hc];
    [rewrite (Z.max_r cap MMAX Hc) in L | rewrite (Z.max_l cap MMAX ltac:(lia)) in L]; lia.
Qed.

(* relay_add's charge: the table malloc (ATABLE = 896, primary) when there was none *)
Lemma kf_ra_cost : forall T, ra_cost MT T <= KC_ra.
Proof.
  intros T. unfold ra_cost, KC_ra. destruct (T =? 0); [|lia].
  rewrite HMs, HFs. replace (64512 <? ATABLE) with false by reflexivity. cbv beta iota. lia.
Qed.

(* list_drop's charge: one free *)
Lemma kf_ldrop_cost : mo_free MT <= KC_ldrop.
Proof. rewrite HFs. unfold KC_ldrop. lia. Qed.
End sec.
