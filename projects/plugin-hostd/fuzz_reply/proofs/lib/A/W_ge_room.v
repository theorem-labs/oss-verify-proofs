(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the arithmetic of gesture_end's room (lane W4), apart from the walk so that the
   gestures_end loop pieces can use it without the walk of W_gesture_end.v.  No Section hypotheses. *)
(* W_contract.v ge_room states gesture_end's room over the plain model's request trace ge_tr (lib/Prog/
   gesture_end_b_c.v gesture_end_tr: the first send's trace, then the second's).  Here: the trace's sum (tr_alloc)
   and largest request (tr_max) in send_line's terms (sl_alloc / sl_maxr, W_contract.v Section s7), hence the two
   room premises of each of the two send_line calls (ge_room_sends) and the capacity's growth bounded by the sum
   (ge_cap_grow_le_tr). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c gesture_end_b_c RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
(* C3: ge_room is the peak of gesture_end's trace; the kit gives each send's peak premise *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_tr_peak.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---- the trace's sum and largest request *)
Lemma tr_alloc_cons : forall (P : Type) (ev : RelayRunT.rev P) tr,
tr_alloc (ev :: tr) =
  match ev with RelayRunT.RMalloc n => n | RelayRunT.RFree _ _ => 0 | RelayRunT.RRealloc _ n _ => n end + tr_alloc tr.
Proof. reflexivity. Qed.
Lemma tr_max_cons : forall (P : Type) (ev : RelayRunT.rev P) tr,
tr_max (ev :: tr) =
  match ev with
  | RelayRunT.RMalloc n => Z.max n (tr_max tr)
  | RelayRunT.RFree _ _ => tr_max tr
  | RelayRunT.RRealloc _ n _ => Z.max n (tr_max tr)
  end.
Proof. reflexivity. Qed.
Lemma tr_max_nonneg : forall (P : Type) (tr : list (RelayRunT.rev P)), 0 <= tr_max tr.
Proof.
intros P tr. induction tr as [|ev tr IH]; [change (tr_max (@nil (RelayRunT.rev P))) with 0; lia|].
rewrite tr_max_cons. destruct ev; cbv beta iota; lia.
Qed.
Lemma tr_alloc_app : forall (P : Type) (l1 l2 : list (RelayRunT.rev P)), tr_alloc (l1 ++ l2) = tr_alloc l1 + tr_alloc l2.
Proof.
intros P l1 l2. induction l1 as [|ev l1 IH]; [reflexivity|].
rewrite <- app_comm_cons, !tr_alloc_cons, IH. lia.
Qed.
Lemma tr_max_app : forall (P : Type) (l1 l2 : list (RelayRunT.rev P)), tr_max (l1 ++ l2) = Z.max (tr_max l1) (tr_max l2).
Proof.
intros P l1 l2. pose proof (tr_max_nonneg P l2) as H2. induction l1 as [|ev l1 IH].
- cbn [app]. change (tr_max (@nil (RelayRunT.rev P))) with 0. lia.
- rewrite <- app_comm_cons, !tr_max_cons. destruct ev; cbv beta iota; lia.
Qed.

(* ---- one send: its trace in send_line's terms *)
Lemma sl_run_alloc : forall fuel mx no cap rem j o,
tr_alloc (fst (send_line_b_c.sl_run fuel mx no cap rem j o)) = sl_alloc_run fuel mx no cap rem.
Proof.
induction fuel as [|f IH]; intros mx no cap rem j o; cbn [send_line_b_c.sl_run sl_alloc_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|].
destruct (cap <? no + _); [|apply IH].
cbn [fst]. rewrite tr_alloc_cons, IH. destruct (cap =? 0); reflexivity.
Qed.
Lemma sl_run_max : forall fuel mx no cap rem j o,
tr_max (fst (send_line_b_c.sl_run fuel mx no cap rem j o)) = sl_max_run fuel mx no cap rem.
Proof.
induction fuel as [|f IH]; intros mx no cap rem j o; cbn [send_line_b_c.sl_run sl_max_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|].
destruct (cap <? no + _); [|apply IH].
cbn [fst]. rewrite tr_max_cons, IH. destruct (cap =? 0); reflexivity.
Qed.
Lemma sl_tr_alloc : forall live mx no cap len j o,
tr_alloc (send_line_b_c.send_line_tr live mx no cap len j o) =
  if live then sl_alloc_run (Z.to_nat len) mx no cap len else 0.
Proof. intros live mx no cap len j o. unfold send_line_b_c.send_line_tr. destruct live; [apply sl_run_alloc | reflexivity]. Qed.
Lemma sl_tr_max : forall live mx no cap len j o,
tr_max (send_line_b_c.send_line_tr live mx no cap len j o) =
  if live then sl_max_run (Z.to_nat len) mx no cap len else 0.
Proof. intros live mx no cap len j o. unfold send_line_b_c.send_line_tr. destruct live; [apply sl_run_max | reflexivity]. Qed.

(* send_line's model never makes a capacity or a count negative. *)
Lemma sl_run_cap_nonneg : forall f mx no cap rem j o, 0 <= mx -> 0 <= no -> 0 <= cap ->
0 <= fst (snd (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
induction f as [|f IH]; intros mx no cap rem j o Hmx Hno Hcap; cbn [send_line_b_c.sl_run]; [cbn; lia|].
destruct (rem <=? 0) eqn:Er; [cbn; lia|]. apply Z.leb_gt in Er.
assert (Hn : 0 <= (if negb (mx =? 0) && (mx <? rem) then mx else rem)) by (destruct (negb (mx =? 0) && (mx <? rem)); lia).
destruct (cap <? no + _); cbn [fst snd]; apply IH; lia.
Qed.
Lemma sl_cap_nonneg : forall c mx no cap len, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= sl_cap c mx no cap len.
Proof.
intros c mx no cap len Hmx Hno Hcap. unfold sl_cap, send_line_b_c.send_line_cap.
destruct (sl_live c len); [apply sl_run_cap_nonneg; lia | lia].
Qed.
Lemma sl_no_nonneg : forall c no len, 0 <= no -> 0 <= len -> 0 <= sl_no c no len.
Proof. intros c no len H1 H2. unfold sl_no. destruct (sl_live c len); lia. Qed.

(* A growth round's new capacity is a term of the sum: the capacity grows by at most what the rounds request. *)
Lemma sl_fin_le_alloc : forall fuel mx no cap rem, 0 <= cap ->
sl_fin_run fuel mx no cap rem - cap <= sl_alloc_run fuel mx no cap rem.
Proof.
induction fuel as [|f IH]; intros mx no cap rem Hc; cbn [sl_fin_run sl_alloc_run]; [lia|].
destruct (rem <=? 0); [lia|].
set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
destruct (cap <? no + n) eqn:E; [apply Z.ltb_lt in E|].
- pose proof (IH mx (no + n) ((no + n) * 2) (rem - n) ltac:(lia)). lia.
- apply IH. exact Hc.
Qed.
Lemma sl_cap_grow_le_alloc : forall c mx no cap len, 0 <= cap -> sl_cap c mx no cap len - cap <= sl_alloc c mx no cap len.
Proof.
intros c mx no cap len Hc. rewrite sl_cap_fin. unfold sl_alloc.
destruct (sl_live c len); [apply sl_fin_le_alloc; exact Hc | lia].
Qed.
Lemma sl_alloc_nonneg : forall c mx no cap len, 0 <= cap -> 0 <= sl_alloc c mx no cap len.
Proof.
intros c mx no cap len Hc. unfold sl_alloc. destruct (sl_live c len); [|lia].
pose proof (sl_fin_le_alloc (Z.to_nat len) mx no cap len Hc).
pose proof (sl_fin_ge (Z.to_nat len) mx no cap len Hc). lia.
Qed.

(* ---- the two sends *)
(* After a send of len <> 0 bytes, " end\0" is live exactly when that send was: an off send (client closed or
   broken) leaves the second off, a live one leaves g_client_broken = g_send_dead = 0, a dead one sets broken. *)
Lemma sl_live_ctl5 : forall c XL, XL <> 0 -> sl_live (sl_ctl c XL) 5 = sl_live c XL.
Proof.
intros [cl br dd ei ev] XL HXL. unfold sl_live, sl_ctl, send_line_c.send_live, send_line_c.send_off.
cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
replace (XL =? 0) with false by (symmetry; apply Z.eqb_neq; exact HXL).
destruct (cl <? 0); [reflexivity|].
destruct (Z.eqb_spec br 1) as [-> | Hb]; [reflexivity|].
destruct (Z.eqb_spec dd 0) as [-> | Hd]; [reflexivity|].
cbn [orb negb andb]. destruct (dd =? 1); reflexivity.
Qed.
Lemma sl_live_len0 : forall c, sl_live c 0 = false.
Proof.
intros c. unfold sl_live, send_line_c.send_live, send_line_c.send_off.
destruct (ct_cl c <? 0), (ct_br c =? 1); reflexivity.
Qed.
Lemma ge_tr_alloc : forall c mx no cap XL, XL <> 0 ->
tr_alloc (ge_tr c mx no cap XL) =
  sl_alloc c mx no cap XL + sl_alloc (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5.
Proof.
intros c mx no cap XL HXL. unfold ge_tr, gesture_end_b_c.gesture_end_tr. cbv beta zeta.
rewrite tr_alloc_app, !sl_tr_alloc. unfold sl_alloc, sl_no, sl_cap. rewrite (sl_live_ctl5 c XL HXL).
destruct (sl_live c XL); reflexivity.
Qed.
Lemma ge_tr_max : forall c mx no cap XL, XL <> 0 ->
tr_max (ge_tr c mx no cap XL) =
  Z.max (sl_maxr c mx no cap XL) (sl_maxr (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5).
Proof.
intros c mx no cap XL HXL. unfold ge_tr, gesture_end_b_c.gesture_end_tr. cbv beta zeta.
rewrite tr_max_app, !sl_tr_max. unfold sl_maxr, sl_no, sl_cap. rewrite (sl_live_ctl5 c XL HXL).
destruct (sl_live c XL); reflexivity.
Qed.
Lemma ge_tr_dead : forall c mx no cap XL, sl_live c XL = false ->
tr_max (ge_tr c mx no cap XL) = 0 /\ tr_alloc (ge_tr c mx no cap XL) = 0.
Proof.
intros c mx no cap XL H. unfold ge_tr, gesture_end_b_c.gesture_end_tr. cbv beta zeta.
rewrite tr_max_app, tr_alloc_app, !sl_tr_max, !sl_tr_alloc, H. split; reflexivity.
Qed.

(* ---- the room *)
(* From ge_room (C3's peak form): send_line's two room premises, in sl_spec's own terms, at the first send (bb bounding
   its blocks_bytes) and at the second (whose blocks_bytes the first moved by sl_cap - cap): the request bounds from
   the trace's largest request, the rooms from W_tr_peak.v's ge_room_first / ge_room_second_sl. *)
Lemma ge_room_sends : forall MMAX bb c mx no cap XL, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 < XL ->
ge_room MMAX bb c mx no cap XL ->
sl_maxr c mx no cap XL < MMAX /\ bb + tr_peak (sl_tr c mx no cap XL) <= LIVE_MAX /\
sl_maxr (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5 < MMAX /\
bb + (sl_cap c mx no cap XL - cap) + tr_peak (sl_tr (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5)
  <= LIVE_MAX.
Proof.
intros MMAX bb c mx no cap XL Hm Hn Hc HXL HR.
pose proof (ge_room_first MMAX bb c mx no cap XL HR) as P1.
pose proof (ge_room_second_sl MMAX bb c mx no cap XL ltac:(lia) HR) as P2.
destruct HR as (R1 & _). rewrite ge_tr_max in R1 by lia.
split; [lia|]. split; [exact P1|]. split; lia.
Qed.
(* gesture_end's g_capout grows by at most what its trace requests. *)
Lemma ge_cap_grow_le_tr : forall c mx no cap XL, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 < XL ->
ge_cap c mx no cap XL - cap <= tr_alloc (ge_tr c mx no cap XL).
Proof.
intros c mx no cap XL Hm Hn Hc HXL. unfold ge_cap. rewrite ge_tr_alloc by lia.
pose proof (sl_cap_nonneg c mx no cap XL Hm Hn Hc) as C1.
pose proof (sl_cap_grow_le_alloc c mx no cap XL Hc) as G1.
pose proof (sl_cap_grow_le_alloc (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5 C1) as G2.
lia.
Qed.
