(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition ll_s (s : inflate_state) (h : Z) : inflate_state :=
  iset_have (iset_lens s (arr_set (is_lens s) (arr_get order_a (is_have s)) (wrap16 (BITSv h 3)))) (wrap32 (is_have s + 1)).
Definition ll_r (r : iregs) : iregs := irset_bits (irset_hold r (Z.shiftr (ir_hold r) 3)) (wrap32 (ir_bits r - 3)).

Lemma lenlens_while1_S : forall k s c r,
  lenlens_while1 (S k) (mkW s c r) =
    if is_have s <? is_ncode s then
      match NEEDBITS 3 (mkW s c r) with
      | ARun _ (mkW s1 c1 r1) => lenlens_while1 k (mkW (ll_s s1 (ir_hold r1)) c1 (ll_r r1))
      | ALeave w => ALeave w
      | ARet rc w => ARet rc w
      end
    else ARun tt (mkW s c r).
Proof.
  intros k s c r. cbn [lenlens_while1]. rewrite abind_run, gs_eq.
  destruct (is_have s <? is_ncode s); [| rewrite aret_eq; reflexivity].
  rewrite abind_run.
  destruct (NEEDBITS 3 (mkW s c r)) as [[] [s1 c1 r1] | w | rc w] eqn:HN; [| reflexivity | reflexivity].
  mstep1 BITS_eq. mstep1 (@gs_eq inflate_state). unfold set_lens. mstep1 us_eq. mstep1 us_eq. mstep1 DROPBITS_eq. reflexivity.
Qed.
Lemma lenlens_while1_O : forall w, lenlens_while1 O w = ARun tt w.
Proof. intros. reflexivity. Qed.

Definition ll2_s (s : inflate_state) : inflate_state :=
  iset_have (iset_lens s (arr_set (is_lens s) (arr_get order_a (is_have s)) (wrap16 0))) (wrap32 (is_have s + 1)).
Lemma lenlens_while2_S : forall k s c r,
  lenlens_while2 (S k) (mkW s c r) =
    if is_have s <? 19 then lenlens_while2 k (mkW (ll2_s s) c r) else ARun tt (mkW s c r).
Proof.
  intros k s c r. cbn [lenlens_while2]. rewrite abind_run, gs_eq.
  destruct (is_have s <? 19); [| rewrite aret_eq; reflexivity].
  unfold set_lens. mstep1 us_eq. mstep1 us_eq. reflexivity.
Qed.

Fixpoint ll2 (k : nat) (s : inflate_state) : inflate_state :=
  match k with
  | O => s
  | S k' => if is_have s <? 19 then ll2 k' (ll2_s s) else s
  end.
Lemma lenlens_while2_run : forall k s c r, lenlens_while2 k (mkW s c r) = ARun tt (mkW (ll2 k s) c r).
Proof.
  intros k. induction k as [|k IH]; intros s c r; [reflexivity|].
  rewrite lenlens_while2_S. cbn [ll2]. destruct (is_have s <? 19); [apply IH | reflexivity].
Qed.

Fixpoint ll1 (k : nat) (s : inflate_state) (c : icall) (r : iregs) : option (inflate_state * icall * iregs) :=
  match k with
  | O => Some (s, c, r)
  | S k' => if is_have s <? is_ncode s then
              match NEEDBITS 3 (mkW s c r) with
              | ARun _ (mkW s1 c1 r1) => ll1 k' (ll_s s1 (ir_hold r1)) c1 (ll_r r1)
              | _ => None
              end
            else Some (s, c, r)
  end.

Definition ll_tab (s : inflate_state) (tbl : arr) (next lenbits : Z) (work : arr) : inflate_state :=
  iset_work (iset_lenbits (iset_next (iset_lencode (iset_distcode (iset_codes s tbl) (CDyn 0)) (CDyn 0)) next) lenbits) work.
Definition ll_s2 (s : inflate_state) : inflate_state := iset_mode (iset_have s 0) CODELENS.

Lemma arm_LENLENS_tail : forall flush s c r,
  (do s0 <- gs (fun s0 => s0);
   let '(ret, tbl, next, lenbits, work) := inflate_table CODES (is_lens s0) 0 19 (is_codes s0) 0 7 (is_work s0) in
   us (fun s1 => iset_work (iset_lenbits (iset_next (iset_lencode (iset_distcode (iset_codes s1 tbl) (CDyn 0)) (CDyn 0)) next) lenbits) work) ;;
   ur (fun r0 => irset_ret r0 ret) ;;
   if negb (ret =? 0) then go_bad MSG_invalid_code_lengths_set
   else us (fun s1 => iset_have s1 0) ;; set_mode CODELENS ;; arm_CODELENS ivar_ref flush)%am (mkW s c r)
  = let '(ret, tbl, next, lenbits, work) := inflate_table CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) in
    let s1 := ll_tab s tbl next lenbits work in
    let r1 := irset_ret r ret in
    if negb (ret =? 0) then ARun tt (mkW (iset_mode s1 BAD) (icset_msg c MSG_invalid_code_lengths_set) r1)
    else arm_CODELENS ivar_ref flush (mkW (ll_s2 s1) c r1).
Proof.
  intros flush s c r. rewrite abind_run, gs_eq.
  destruct (inflate_table CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s)) as [[[[ret tbl] next] lenbits] work].
  mstep1 us_eq. mstep1 ur_eq. cbv zeta.
  destruct (negb (ret =? 0)); [rewrite go_bad_eq; reflexivity|].
  mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Fixpoint zlens (n : nat) (a : arr) (i : Z) : arr :=
  match n with
  | O => a
  | S n' => if i <? 19 then zlens n' (arr_set a (arr_get order_a i) 0) (i + 1) else a
  end.

Lemma wrap16_0 : wrap16 0 = 0. Proof. reflexivity. Qed.

Lemma ll2_zlens : forall n s, 0 <= is_have s < 19 -> 19 - is_have s <= Z.of_nat n ->
  ll2 n s = iset_have (iset_lens s (zlens n (is_lens s) (is_have s))) 19.
Proof.
  induction n as [|n IH]; intros s Hh Hn; [cbn [Z.of_nat] in Hn; lia|].
  cbn [ll2 zlens]. rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hh)).
  unfold ll2_s at 1. rewrite wrap16_0.
  set (s1 := iset_have (iset_lens s (arr_set (is_lens s) (arr_get order_a (is_have s)) 0)) (wrap32 (is_have s + 1))).
  assert (E1 : is_have s1 = is_have s + 1) by (subst s1; cbn [is_have iset_have]; apply wrap32_id; lia).
  assert (E2 : is_lens s1 = arr_set (is_lens s) (arr_get order_a (is_have s)) 0) by reflexivity.
  destruct (Z.eq_dec (is_have s + 1) 19) as [He|He].
  - replace (ll2 n s1) with s1 by (destruct n; cbn [ll2]; rewrite ?E1, ?(proj2 (Z.ltb_ge (is_have s + 1) 19) ltac:(lia)); reflexivity).
    replace (zlens n (arr_set (is_lens s) (arr_get order_a (is_have s)) 0) (is_have s + 1)) with (arr_set (is_lens s) (arr_get order_a (is_have s)) 0)
      by (destruct n; cbn [zlens]; rewrite ?(proj2 (Z.ltb_ge (is_have s + 1) 19) ltac:(lia)); reflexivity).
    subst s1. rewrite (wrap32_id (is_have s + 1)) by lia. rewrite He. reflexivity.
  - rewrite (IH s1) by (rewrite E1; first [lia | rewrite Nat2Z.inj_succ in Hn; lia]).
    rewrite E1, E2. subst s1. destruct s; reflexivity.
Qed.

Lemma zlens_len : forall n a i, arr_len (zlens n a i) = arr_len a.
Proof. induction n as [|n IH]; intros a i; cbn [zlens]; [reflexivity|]. destruct (i <? 19); [rewrite IH, arr_len_set|]; reflexivity. Qed.

Lemma ll2_stop : forall k s, 19 <= is_have s -> ll2 k s = s.
Proof. intros k s H. destruct k; cbn [ll2]; [reflexivity|]. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.

Definition ll_fin (flush : Z) (s2 : inflate_state) (c1 : icall) (r1 : iregs) : ares unit :=
  let '(ret, tbl, next, lenbits, work) := inflate_table CODES (is_lens s2) 0 19 (is_codes s2) 0 7 (is_work s2) in
  let s3 := ll_tab s2 tbl next lenbits work in
  let r2 := irset_ret r1 ret in
  if negb (ret =? 0) then ARun tt (mkW (iset_mode s3 BAD) (icset_msg c1 MSG_invalid_code_lengths_set) r2)
  else arm_CODELENS ivar_ref flush (mkW (ll_s2 s3) c1 r2).

Lemma arm_LENLENS_eq : forall flush s c r,
  arm_LENLENS ivar_ref flush (mkW s c r) =
  match lenlens_while1 19 (mkW s c r) with
  | ARun _ (mkW s1 c1 r1) => ll_fin flush (ll2 19 s1) c1 r1
  | ALeave w => ALeave w
  | ARet rc w => ARet rc w
  end.
Proof.
  intros flush s c r. unfold arm_LENLENS. rewrite abind_run.
  destruct (lenlens_while1 19 (mkW s c r)) as [[] [s1 c1 r1] | w | rc w]; [| reflexivity | reflexivity].
  rewrite abind_run, lenlens_while2_run. rewrite arm_LENLENS_tail. unfold ll_fin. reflexivity.
Qed.


Definition ll_post_ok (tbl : arr) (next lenbits : Z) (work : arr) : bool :=
  (arr_len tbl =? 1444) && (arr_len work =? 288) && (0 <=? next) && (next <=? 1444)
  && (0 <=? lenbits) && (lenbits <? 2 ^ 32)
  && forallb (fun i => (0 <=? arr_get tbl (Z.of_nat i)) && (arr_get tbl (Z.of_nat i) <? 2 ^ 32)) (seq 0 1444)
  && forallb (fun i => (0 <=? arr_get work (Z.of_nat i)) && (arr_get work (Z.of_nat i) <? 2 ^ 16)) (seq 0 288).

Definition ll_call_ok (s2 : inflate_state) : bool :=
  forallb (fun i => arr_get (is_lens s2) (Z.of_nat i) <=? 15) (seq 0 19)
  && it_safe CODES (is_lens s2) 0 19 (is_codes s2) 0 7 (is_work s2)
  && (let '(ret, tbl, next, lenbits, work) := inflate_table CODES (is_lens s2) 0 19 (is_codes s2) 0 7 (is_work s2) in
      ll_post_ok tbl next lenbits work).

Definition lenlens_okb (w : iw) : bool :=
  (is_ncode (w_s w) <=? 19)
  && match lenlens_while1 19 w with
     | ARun _ (mkW s1 c1 r1) => ll_call_ok (ll2 19 s1)
     | _ => true
     end.

Definition lenlens_next (w : iw) : option iw :=
  match lenlens_while1 19 w with
  | ARun _ (mkW s1 c1 r1) =>
      let s2 := ll2 19 s1 in
      let '(ret, tbl, next, lenbits, work) := inflate_table CODES (is_lens s2) 0 19 (is_codes s2) 0 7 (is_work s2) in
      if ret =? 0 then Some (mkW (ll_s2 (ll_tab s2 tbl next lenbits work)) c1 (irset_ret r1 ret)) else None
  | _ => None
  end.

Lemma forallb_seq_Z : forall (f : Z -> bool) n i, forallb (fun k => f (Z.of_nat k)) (seq 0 n) = true -> 0 <= i < Z.of_nat n -> f i = true.
Proof.
  intros f n i H Hi. rewrite forallb_forall in H. specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma ll_post_ok_sound : forall tbl next lenbits work, ll_post_ok tbl next lenbits work = true ->
  arr_len tbl = 1444 /\ arr_len work = 288 /\ 0 <= next <= 1444 /\ 0 <= lenbits < 2 ^ 32
  /\ (forall i, 0 <= i < 1444 -> 0 <= arr_get tbl i < 2 ^ 32)
  /\ (forall i, 0 <= i < 288 -> 0 <= arr_get work i < 2 ^ 16).
Proof.
  intros tbl next lenbits work H. unfold ll_post_ok in H.
  apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5. apply Z.ltb_lt in H6.
  split; [exact H1|]. split; [exact H2|]. split; [lia|]. split; [lia|]. split.
  - intros i Hi. pose proof (forallb_seq_Z (fun j => (0 <=? arr_get tbl j) && (arr_get tbl j <? 2 ^ 32)) 1444%nat i H7 ltac:(cbn; lia)) as Y.
    cbv beta in Y. apply andb_prop in Y as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2. lia.
  - intros i Hi. pose proof (forallb_seq_Z (fun j => (0 <=? arr_get work j) && (arr_get work j <? 2 ^ 16)) 288%nat i H8 ltac:(cbn; lia)) as Y.
    cbv beta in Y. apply andb_prop in Y as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2. lia.
Qed.

Lemma ll_call_ok_sound : forall s2, ll_call_ok s2 = true ->
  (forall i, 0 <= i < 19 -> arr_get (is_lens s2) i <= 15)
  /\ it_safe CODES (is_lens s2) 0 19 (is_codes s2) 0 7 (is_work s2) = true
  /\ (let '(ret, tbl, next, lenbits, work) := inflate_table CODES (is_lens s2) 0 19 (is_codes s2) 0 7 (is_work s2) in
      ll_post_ok tbl next lenbits work) = true.
Proof.
  intros s2 H. unfold ll_call_ok in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [| split; [exact H2 | exact H3]].
  intros i Hi. apply Z.leb_le. exact (forallb_seq_Z (fun j => arr_get (is_lens s2) j <=? 15) 19%nat i H1 ltac:(cbn; lia)).
Qed.

Lemma inflate_table_ret : forall ty lens lens_ofs codes tbl table bits work ret tbl' nxt' bits' work',
  inflate_table ty lens lens_ofs codes tbl table bits work = (ret, tbl', nxt', bits', work') -> ret = 0 \/ ret = 1 \/ ret = -1.
Proof.
  intros ty lens lens_ofs codes tbl table bits work ret tbl' nxt' bits' work' H.
  rewrite inflate_table_phases in H. cbv zeta in H.
  destruct (itm_max (itm_count lens lens_ofs codes) =? 0); [injection H as <- _ _ _ _; left; reflexivity|].
  destruct (itm_reject ty _ _); [injection H as <- _ _ _ _; right; right; reflexivity|].
  destruct (it_not_enough ty _); [injection H as <- _ _ _ _; right; left; reflexivity|].
  destruct (it_loop _ codes _) as [st|st].
  - injection H as <- _ _ _ _. left; reflexivity.
  - injection H as <- _ _ _ _. right; left; reflexivity.
Qed.

Lemma ll2_leave_okb : forall k s, leave_okb (ll2 k s) = leave_okb s.
Proof.
  induction k as [|k IH]; intros s; cbn [ll2]; [reflexivity|].
  destruct (is_have s <? 19); [| reflexivity]. rewrite IH. reflexivity.
Qed.

Lemma NEEDBITS_k_run' : forall k n s c r s1 c1 r1,
  NEEDBITS_k k n (mkW s c r) = ARun tt (mkW s1 c1 r1) -> s1 = s /\ c1 = c.
Proof.
  induction k as [|k IH]; intros n s c r s1 c1 r1 HN.
  - cbn in HN. unfold aret in HN. split; congruence.
  - rewrite NEEDBITS_k_S in HN. destruct (ir_bits r <? n); [| split; congruence]. destruct (ir_have r =? 0); [congruence | exact (IH _ _ _ _ _ _ _ HN)].
Qed.

Lemma lenlens_while1_leave_okb : forall k s c r s1 c1 r1,
  lenlens_while1 k (mkW s c r) = ARun tt (mkW s1 c1 r1) -> leave_okb s1 = leave_okb s.
Proof.
  induction k as [|k IH]; intros s c r s1 c1 r1 H.
  - cbn in H. injection H as <- _ _. reflexivity.
  - rewrite lenlens_while1_S in H. destruct (is_have s <? is_ncode s); [| injection H as <- _ _; reflexivity].
    unfold NEEDBITS in H.
    destruct (NEEDBITS_k 8 3 (mkW s c r)) as [[] [s' c' r'] | w | rc w] eqn:HN; [| discriminate H | discriminate H].
    destruct (NEEDBITS_k_run' 8 3 s c r s' c' r' HN) as [-> ->].
    rewrite (IH _ _ _ _ _ _ H). reflexivity.
Qed.
