(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac simp_st := cbn [s_stk s_pos s_more s_done s_halt s_depth s_ec s_estk s_edepth s_lo s_hi s_bad
                     w_stk w_pos w_more w_done w_halt w_depth w_ec w_estk w_edepth w_out w_bad] in *.

Lemma eev_fields s : s_more (e_end_value s) = s_more s /\ s_ec (e_end_value s) = s_ec s.
Proof. split; [apply eev_more | apply eev_ec]. Qed.

Lemma r_fail_ec s : s_ec (r_fail s) = true. Proof. reflexivity. Qed.

Lemma e_begin_indef_more k s : s_more (e_begin_indef k s) = s_more s.
Proof. unfold e_begin_indef. simp_st. destruct (MAX_DEPTH <? s_edepth s + 1); reflexivity. Qed.
Lemma e_put_length_more n s : s_more (e_put_length n s) = s_more s.
Proof. unfold e_put_length. destruct (INT64_MAX <? n); reflexivity. Qed.
Lemma e_put_length_stk n s : s_stk (e_put_length n s) = s_stk s.
Proof. unfold e_put_length. destruct (INT64_MAX <? n); reflexivity. Qed.
Lemma e_put_length_ec n s : s_ec (e_put_length n s) = s_ec s.
Proof. unfold e_put_length. destruct (INT64_MAX <? n); reflexivity. Qed.
Lemma e_begin_len_more k n s : s_more (e_begin_len k n s) = s_more s.
Proof. unfold e_begin_len. simp_st. destruct (MAX_DEPTH <? s_edepth s + 1); [reflexivity|]. rewrite e_put_length_more. reflexivity. Qed.

Lemma r_counted_more p m ty k s : s_ec (r_counted p m ty k s) = false -> s_more (r_counted p m ty k s) = true.
Proof.
  unfold r_counted. destruct (get_length p (s_pos s)) as [[n pos1]|]; [|unfold r_fail; simp_st; discriminate].
  destruct (s_ec s) eqn:E; [simp_st; rewrite E; discriminate|].
  destruct (MAX_ITEMS <? n); [unfold r_fail; simp_st; discriminate|]. simp_st. reflexivity.
Qed.

Lemma r_begin_more p obj s : s_ec (r_begin p obj s) = false -> s_more (r_begin p obj s) = true.
Proof.
  unfold r_begin. simp_st.
  destruct (MAX_DEPTH <? s_depth s + 1); [unfold r_fail; simp_st; discriminate|].
  destruct (blen p <=? s_pos s); [unfold r_fail; simp_st; discriminate|].
  destruct (bat p (s_pos s) =? 36).
  - destruct (blen p <=? s_pos s + 1); [unfold r_fail; simp_st; discriminate|].
    destruct (blen p <=? s_pos s + 2); [unfold r_fail; simp_st; discriminate|].
    destruct (bat p (s_pos s + 2) =? 35); [apply r_counted_more | unfold r_fail; simp_st; discriminate].
  - destruct (bat p (s_pos s) =? 35); [apply r_counted_more |]. simp_st. reflexivity.
Qed.

Lemma r_num_more p k lo hi s : s_ec (r_num p k lo hi s) = false -> s_more (r_num p k lo hi s) = true.
Proof. unfold r_num. destruct (blen p <? s_pos s + k); [unfold r_fail; simp_st; discriminate|]. simp_st. reflexivity. Qed.

Local Lemma fin_more (Y : st) : (s_ec Y = false -> s_more Y = true) ->
  s_ec (if s_ec Y then w_more false Y else Y) = false -> s_more (if s_ec Y then w_more false Y else Y) = true.
Proof. intros H. destruct (s_ec Y) eqn:E; [simp_st; rewrite E; discriminate | intros _; exact (H eq_refl)]. Qed.

Local Lemma num_more p k lo hi s :
  let s' := r_num p k lo hi s in
  s_ec (if s_more s' then (if s_ec s' then w_more false s' else s') else s') = false ->
  s_more (if s_more s' then (if s_ec s' then w_more false s' else s') else s') = true.
Proof.
  cbv zeta. destruct (s_more (r_num p k lo hi s)) eqn:M.
  - apply fin_more. intros _. exact M.
  - intros E. pose proof (r_num_more p k lo hi s E). congruence.
Qed.

Lemma r_value_more p t s : s_more s = true -> s_ec (r_value p t s) = false -> s_more (r_value p t s) = true.
Proof.
  intros HM. unfold r_value.
  destruct ((t =? 90) || (t =? 84) || (t =? 70)); [apply fin_more; intros _; reflexivity|].
  destruct (t =? 78); [apply fin_more; intros _; exact HM|].
  destruct (t =? 105); [apply num_more|]. destruct (t =? 85); [apply num_more|]. destruct (t =? 73); [apply num_more|].
  destruct (t =? 108); [apply num_more|]. destruct (t =? 76); [apply num_more|]. destruct (t =? 100); [apply num_more|].
  destruct (t =? 68); [apply num_more|].
  destruct (t =? 67).
  { destruct (blen p <? s_pos s + 1); [unfold r_fail; simp_st; discriminate|].
    destruct (utf8_valid (slice p (s_pos s) 1)); [| unfold r_fail; simp_st; discriminate].
    apply fin_more. intros _. reflexivity. }
  destruct ((t =? 83) || (t =? 72)).
  { destruct (get_length p (s_pos s)) as [[n pos1]|]; [| unfold r_fail; simp_st; discriminate].
    destruct (s_ec s) eqn:E; [simp_st; rewrite E; discriminate|].
    destruct (blen p <? pos1 + n); [unfold r_fail; simp_st; discriminate|].
    destruct ((t =? 83) && negb (utf8_valid (slice p pos1 n))); [unfold r_fail; simp_st; discriminate|].
    apply fin_more. intros _. reflexivity. }
  destruct (t =? 91); [apply fin_more; apply r_begin_more|].
  destruct (t =? 123); [apply fin_more; apply r_begin_more|].
  apply fin_more. simp_st. discriminate.
Qed.

Lemma r_tv_more p s : s_more s = true -> s_ec (r_tv p s) = false -> s_more (r_tv p s) = true.
Proof.
  intros HM. unfold r_tv. destruct (blen p <=? s_pos s); [unfold r_fail; simp_st; discriminate|]. apply r_value_more. exact HM.
Qed.

Lemma r_key_more p s : s_ec (r_key p s) = false -> s_more (r_key p s) = true.
Proof.
  unfold r_key. destruct (get_length p (s_pos s)) as [[n pos1]|]; [| unfold r_fail; simp_st; discriminate].
  destruct (s_ec s); [unfold r_fail; simp_st; discriminate|].
  destruct (blen p <? pos1 + n); [unfold r_fail; simp_st; discriminate|].
  destruct (utf8_valid (slice p pos1 n)); [| unfold r_fail; simp_st; discriminate]. simp_st. reflexivity.
Qed.

Lemma r_key_stk p s : s_stk (r_key p s) = s_stk s.
Proof.
  unfold r_key. destruct (get_length p (s_pos s)) as [[n pos1]|]; [| reflexivity].
  destruct (s_ec s); [reflexivity|]. destruct (blen p <? pos1 + n); [reflexivity|].
  destruct (utf8_valid (slice p pos1 n)); [| reflexivity]. unfold e_key. simp_st. rewrite e_put_length_stk. reflexivity.
Qed.

Lemma r_end_more s : s_more (r_end s) = true.
Proof. unfold r_end. reflexivity. Qed.
Lemma r_end_done s : s_done (r_end s) = s_done s.
Proof. unfold r_end, e_end. simp_st. destruct (s_estk s) as [|e r]; simp_st; [reflexivity|].
  destruct (ei_indef e); [rewrite eev_done; reflexivity|]. destruct (ei_cnt e <? ei_len e); [reflexivity|]. destruct (ei_len e <? ei_cnt e); [reflexivity|].
  rewrite eev_done; reflexivity. Qed.
Lemma r_end_halt s : s_halt (r_end s) = s_halt s.
Proof. unfold r_end, e_end. simp_st. destruct (s_estk s) as [|e r]; simp_st; [reflexivity|].
  destruct (ei_indef e); [rewrite eev_halt; reflexivity|]. destruct (ei_cnt e <? ei_len e); [reflexivity|]. destruct (ei_len e <? ei_cnt e); [reflexivity|].
  rewrite eev_halt; reflexivity. Qed.
Lemma e_end_stk x : s_stk (e_end x) = s_stk x.
Proof. unfold e_end. destruct (s_estk x) as [|e r]; simp_st; [reflexivity|].
  destruct (ei_indef e); [rewrite eev_stk; reflexivity|]. destruct (ei_cnt e <? ei_len e); [reflexivity|]. destruct (ei_len e <? ei_cnt e); [reflexivity|].
  rewrite eev_stk; reflexivity. Qed.
Lemma r_end_stk s : s_stk (r_end s) = tl (s_stk s).
Proof. unfold r_end. simp_st. rewrite e_end_stk. reflexivity. Qed.
Lemma r_end_halted s : s_halt s = false -> s_done s = false -> halted (r_end s) = false.
Proof. intros A B. apply halted_intro; [rewrite r_end_halt; exact A | rewrite r_end_done; exact B | apply r_end_more]. Qed.

Lemma ret_if_ec_false Y : s_ec Y = false -> ret_if_ec Y = Y.
Proof. intros E. unfold ret_if_ec. rewrite E. reflexivity. Qed.
Lemma ret_if_ec_true Y : s_ec Y = true -> ret_if_ec Y = w_halt true Y.
Proof. intros E. unfold ret_if_ec. rewrite E. reflexivity. Qed.
Lemma ret_if_ec_bad Y : s_bad (ret_if_ec Y) = s_bad Y.
Proof. unfold ret_if_ec. destruct (s_ec Y); reflexivity. Qed.
Lemma ret_if_ec_hi Y : s_hi (ret_if_ec Y) = s_hi Y.
Proof. unfold ret_if_ec. destruct (s_ec Y); reflexivity. Qed.
Lemma ret_if_ec_lo Y : s_lo (ret_if_ec Y) = s_lo Y.
Proof. unfold ret_if_ec. destruct (s_ec Y); reflexivity. Qed.
Lemma halted_w_halt Y : halted (w_halt true Y) = true.
Proof. reflexivity. Qed.

Lemma head_call_facts p s t r t' :
  bytes_ok p -> ginv p s -> halted s = false -> s_stk s = t :: r ->
  container_mode (ps_mode t') = container_mode (ps_mode t) -> ps_ok t' ->
  let s0 := w_stk (t' :: r) s in
  pre_run p s0 /\ s_done s0 = false /\ s_halt s0 = false /\ 0 <= s_depth s0 <= MAX_DEPTH
  /\ Z.of_nat (length (s_estk s0)) <= MAX_DEPTH /\ Z.of_nat (length (s_stk s0)) <= s_depth s0 + 1
  /\ ginv p s0 /\ halted s0 = false.
Proof.
  intros Hp G HH HS HC HT. cbv zeta.
  destruct (ginv_upd p s t r t' HS HC HT HH G) as (G0 & HH0 & R0).
  destruct (halted_false _ HH0) as (A & B & C).
  split; [exact (pre_of_ginv p _ Hp G0 HH0)|]. split; [exact B|]. split; [exact A|].
  pose proof (ri_depth _ R0) as D. pose proof (ri_dmax _ R0) as DM. pose proof (ri_estk_max _ R0) as EM.
  simp_st. cbn [length] in D. split; [lia|]. split; [exact EM|]. split; [cbn [length]; lia|]. split; [exact G0| exact HH0].
Qed.

Lemma head_end_facts p s t r :
  bytes_ok p -> ginv p s -> halted s = false -> s_stk s = t :: r -> container_mode (ps_mode t) = true ->
  pre p s /\ s_more s = true /\ s_done s = false /\ s_halt s = false /\ rinv s
  /\ (exists t0 r0, s_stk s = t0 :: r0 /\ container_mode (ps_mode t0) = true /\ r0 <> [] /\ s_estk s <> []).
Proof.
  intros Hp G HH HS HC. destruct (halted_false _ HH) as (A & B & C). pose proof (gi_run p s G HH) as R.
  destruct (pre_of_ginv p s Hp G HH) as (P & _).
  split; [exact P|]. split; [exact C|]. split; [exact B|]. split; [exact A|]. split; [exact R|].
  exists t, r. split; [exact HS|]. split; [exact HC|].
  pose proof (ri_shape s R) as SH. pose proof (ri_estk s R) as ES. rewrite HS in SH, ES. cbn [stk_shape length] in SH, ES.
  destruct r as [|t2 r2]; [rewrite HC in SH; discriminate|]. split; [discriminate|].
  destruct (s_estk s); [cbn [length] in ES; lia | discriminate].
Qed.

Lemma next_head p i s Y :
  bytes_ok p -> s = run i p init -> halted s = false -> step p s = ret_if_ec Y ->
  s_done Y = s_done s -> s_halt Y = s_halt s -> (s_ec Y = false -> s_more Y = true) ->
  (s_ec Y = false -> Y = run (S i) p init /\ halted Y = false /\ mu p Y < mu p s)
  /\ (s_ec Y = true -> w_halt true Y = run (S i) p init /\ halted (w_halt true Y) = true)
  /\ s_bad Y = false.
Proof.
  intros Hp HX HH ST HD HL HM.
  assert (RS : run (S i) p init = step p s) by (rewrite HX; rewrite <- (Nat.add_1_r i), run_add; reflexivity).
  pose proof (run_ginv p Hp i init (ginv_init p)) as G. rewrite <- HX in G.
  destruct (step_ok p s Hp G) as (G' & _ & MU).
  destruct (halted_false _ HH) as (A & B & C).
  split; [|split].
  - intros E. rewrite (ret_if_ec_false Y E) in ST. split; [congruence|]. split.
    + apply halted_intro; [congruence|congruence| exact (HM E)].
    + rewrite <- ST. exact (MU HH).
  - intros E. rewrite (ret_if_ec_true Y E) in ST. split; [congruence| apply halted_w_halt].
  - pose proof (run_not_bad p (S i) Hp) as NB. rewrite RS, ST, ret_if_ec_bad in NB. exact NB.
Qed.

Lemma next_head_hi p i s Y (HBP : Z -> Prop) :
  s = run i p init -> step p s = ret_if_ec Y -> (forall n, HBP (s_hi (run n p init))) -> HBP (s_hi Y).
Proof.
  intros HX ST HB. specialize (HB (S i)). rewrite <- (Nat.add_1_r i), run_add, <- HX in HB. cbn [run] in HB. rewrite ST, ret_if_ec_hi in HB. exact HB.
Qed.

Lemma next_head_end p i s :
  bytes_ok p -> s = run i p init -> halted s = false -> step p s = r_end s ->
  r_end s = run (S i) p init /\ halted (r_end s) = false /\ mu p (r_end s) < mu p s /\ s_bad (r_end s) = false.
Proof.
  intros Hp HX HH ST.
  assert (RS : run (S i) p init = step p s) by (rewrite HX; rewrite <- (Nat.add_1_r i), run_add; reflexivity).
  pose proof (run_ginv p Hp i init (ginv_init p)) as G. rewrite <- HX in G.
  destruct (step_ok p s Hp G) as (G' & _ & MU). destruct (halted_false _ HH) as (A & B & C).
  split; [congruence|]. split; [apply r_end_halted; assumption|]. split; [rewrite <- ST; exact (MU HH)|].
  pose proof (run_not_bad p (S i) Hp) as NB. rewrite RS, ST in NB. exact NB.
Qed.
Lemma next_head_end_hi p i s (HBP : Z -> Prop) :
  s = run i p init -> step p s = r_end s -> (forall n, HBP (s_hi (run n p init))) -> HBP (s_hi (r_end s)).
Proof.
  intros HX ST HB. specialize (HB (S i)). rewrite <- (Nat.add_1_r i), run_add, <- HX in HB. cbn [run] in HB. rewrite ST in HB. exact HB.
Qed.

Lemma next_head_key p i s Y M :
  bytes_ok p -> s = run i p init -> halted s = false ->
  step p s = (if s_ec Y then w_halt true Y else top_upd (ps_mode_set M) Y) ->
  s_done Y = s_done s -> s_halt Y = s_halt s -> (s_ec Y = false -> s_more Y = true) ->
  (s_ec Y = false -> top_upd (ps_mode_set M) Y = run (S i) p init /\ halted (top_upd (ps_mode_set M) Y) = false
                     /\ mu p (top_upd (ps_mode_set M) Y) < mu p s /\ s_bad (top_upd (ps_mode_set M) Y) = false)
  /\ (s_ec Y = true -> w_halt true Y = run (S i) p init /\ halted (w_halt true Y) = true)
  /\ s_bad Y = false.
Proof.
  intros Hp HX HH ST HD HL HM.
  assert (RS : run (S i) p init = step p s) by (rewrite HX; rewrite <- (Nat.add_1_r i), run_add; reflexivity).
  pose proof (run_ginv p Hp i init (ginv_init p)) as G. rewrite <- HX in G.
  destruct (step_ok p s Hp G) as (G' & _ & MU). destruct (halted_false _ HH) as (A & B & C).
  pose proof (run_not_bad p (S i) Hp) as NB. rewrite RS, ST in NB.
  assert (TU : forall f x, halted (top_upd f x) = halted x /\ s_bad (top_upd f x) = s_bad x).
  { intros f x. unfold top_upd. destruct (s_stk x); split; reflexivity. }
  split; [|split].
  - intros E. rewrite E in ST, NB. split; [congruence|]. destruct (TU (ps_mode_set M) Y) as (T1 & T2). split; [|split].
    + rewrite T1. apply halted_intro; [congruence|congruence| exact (HM E)].
    + rewrite <- ST. exact (MU HH).
    + exact NB.
  - intros E. rewrite E in ST. split; [congruence| apply halted_w_halt].
  - destruct (s_ec Y) eqn:E; [exact NB|]. destruct (TU (ps_mode_set M) Y) as (_ & T2). rewrite T2 in NB. exact NB.
Qed.

Lemma next_head_key_hi p i s Y M (HBP : Z -> Prop) :
  s = run i p init -> step p s = (if s_ec Y then w_halt true Y else top_upd (ps_mode_set M) Y) ->
  (forall n, HBP (s_hi (run n p init))) -> HBP (s_hi Y).
Proof.
  intros HX ST HB. specialize (HB (S i)). rewrite <- (Nat.add_1_r i), run_add, <- HX in HB. cbn [run] in HB. rewrite ST in HB.
  destruct (s_ec Y); [exact HB|]. unfold top_upd in HB. destruct (s_stk Y); exact HB.
Qed.

Lemma head_end_facts_w p s t r q :
  bytes_ok p -> ginv p s -> halted s = false -> s_stk s = t :: r -> container_mode (ps_mode t) = true -> s_pos s <= q <= blen p ->
  let s0 := w_pos q s in
  pre p s0 /\ s_more s0 = true /\ s_done s0 = false /\ s_halt s0 = false /\ rinv s0
  /\ (exists t0 r0, s_stk s0 = t0 :: r0 /\ container_mode (ps_mode t0) = true /\ r0 <> [] /\ s_estk s0 <> []).
Proof.
  intros Hp G HH HS HC HQ. cbv zeta.
  destruct (head_end_facts p s t r Hp G HH HS HC) as (P0 & A & B & C & R & EX).
  destruct P0 as (P1 & P2 & P3 & P4 & P5 & P6). pose proof (gi_pos p s G) as GP.
  split; [unfold pre; simp_st; repeat split; try assumption; lia|].
  split; [exact A|]. split; [exact B|]. split; [exact C|].
  split; [destruct R; constructor; simp_st; assumption|].
  simp_st. exact EX.
Qed.
