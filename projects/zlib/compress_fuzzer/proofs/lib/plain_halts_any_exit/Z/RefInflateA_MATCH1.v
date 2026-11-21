(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition mc_src (win ob : arr) (put0 : Z) (from : fromptr) (k : Z) : Z :=
  match from with
  | FWin i => arr_get win (i + k)
  | FOut i => arr_get ob (i + k mod (put0 - i))
  end.

Fixpoint mc_obn (win ob : arr) (put0 : Z) (from : fromptr) (j : nat) : arr :=
  match j with
  | O => ob
  | S j' => arr_set (mc_obn win ob put0 from j') (put0 + Z.of_nat j') (mc_src win ob put0 from (Z.of_nat j'))
  end.

Fixpoint from_add (f : fromptr) (j : nat) : fromptr :=
  match j with O => f | S j' => from_succ (from_add f j') end.

Lemma from_add_Win : forall i j, from_add (FWin i) j = FWin (i + Z.of_nat j).
Proof. intros i j. induction j as [|j IH]; [cbn; f_equal; lia|]. cbn [from_add]. rewrite IH. cbn. f_equal. lia. Qed.
Lemma from_add_Out : forall i j, from_add (FOut i) j = FOut (i + Z.of_nat j).
Proof. intros i j. induction j as [|j IH]; [cbn; f_equal; lia|]. cbn [from_add]. rewrite IH. cbn. f_equal. lia. Qed.

Lemma mc_obn_len : forall win ob put0 from j, arr_len (mc_obn win ob put0 from j) = arr_len ob.
Proof. intros. induction j as [|j IH]; [reflexivity|]. cbn [mc_obn]. rewrite arr_len_set. exact IH. Qed.

Lemma mc_obn_get : forall win ob put0 from j p,
  0 <= put0 -> put0 + Z.of_nat j <= arr_len ob ->
  arr_get (mc_obn win ob put0 from j) p
  = if (put0 <=? p) && (p <? put0 + Z.of_nat j) then mc_src win ob put0 from (p - put0) else arr_get ob p.
Proof.
  intros win ob put0 from j p Hp0. induction j as [|j IH]; intros Hj.
  - cbn [mc_obn]. destruct (Z.leb_spec put0 p); [| reflexivity]. destruct (Z.ltb_spec p (put0 + Z.of_nat 0)); [exfalso; lia | reflexivity].
  - cbn [mc_obn]. rewrite arr_get_set. unfold arr_inb. rewrite mc_obn_len.
    destruct (Z.eqb_spec (put0 + Z.of_nat j) p) as [E|NE].
    + subst p. replace ((0 <=? put0 + Z.of_nat j) && (put0 + Z.of_nat j <? arr_len ob)) with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. destruct (Z.leb_spec put0 (put0 + Z.of_nat j)); [| exfalso; lia].
      destruct (Z.ltb_spec (put0 + Z.of_nat j) (put0 + Z.of_nat (S j))); [| exfalso; lia]. cbn [andb]. f_equal. lia.
    + cbn [andb]. rewrite IH by lia.
      destruct (Z.leb_spec put0 p); [| reflexivity]. cbn [andb].
      destruct (Z.ltb_spec p (put0 + Z.of_nat j)); destruct (Z.ltb_spec p (put0 + Z.of_nat (S j))); try reflexivity; exfalso; lia.
Qed.

Lemma mc_read : forall win ob put0 from j,
  0 <= put0 -> put0 + Z.of_nat j <= arr_len ob ->
  match from with FOut i => i < put0 | FWin _ => True end ->
  match from_add from j with
  | FWin i => arr_get win i
  | FOut i => arr_get (mc_obn win ob put0 from j) i
  end = mc_src win ob put0 from (Z.of_nat j).
Proof.
  intros win ob put0 from j Hp0 Hj Hfrom. destruct from as [i|i].
  - rewrite from_add_Win. reflexivity.
  - rewrite from_add_Out. rewrite mc_obn_get by lia. cbn [mc_src].
    set (d := put0 - i). assert (Hd : 0 < d) by lia.
    destruct (Z_lt_le_dec (Z.of_nat j) d) as [Hlt|Hge].
    + replace ((put0 <=? i + Z.of_nat j) && (i + Z.of_nat j <? put0 + Z.of_nat j)) with false
        by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
      rewrite Z.mod_small by lia. reflexivity.
    + replace ((put0 <=? i + Z.of_nat j) && (i + Z.of_nat j <? put0 + Z.of_nat j)) with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      f_equal. replace (i + Z.of_nat j - put0) with (Z.of_nat j - d) by lia.
      rewrite <- (Z.mod_add _ 1 d) by lia. f_equal. f_equal. lia.
Qed.

Local Definition mc_body (win : arr) :=
  (fun st : arr * Z * fromptr * Z => let '(ob, put, from, copy) := st in
     let v := match from with FWin i => arr_get win i | FOut i => arr_get ob i end in
     let ob := arr_set ob put v in
     let copy := wrap32 (copy - 1) in
     (negb (copy =? 0), (ob, put + 1, from_succ from, copy))).

Lemma mc_loop : forall win ob put0 from n (k j : nat),
  0 <= put0 -> put0 + n <= arr_len ob -> n < 2 ^ 32 ->
  match from with FOut i => i < put0 | FWin _ => True end ->
  (Z.of_nat j + Z.of_nat k = n)%Z -> (0 < k)%nat ->
  loopZ (Z.of_nat k) (mc_body win) (mc_obn win ob put0 from j, put0 + Z.of_nat j, from_add from j, n - Z.of_nat j)
  = (mc_obn win ob put0 from (Z.to_nat n), put0 + n, from_add from (Z.to_nat n), 0).
Proof.
  intros win ob put0 from n k. induction k as [|k IH]; intros j Hp0 Hn Hn32 Hfrom Hjk Hk; [lia|].
  rewrite loopZ_step by lia. unfold mc_body at 1.
  rewrite (mc_read win ob put0 from j Hp0 ltac:(lia) Hfrom).
  rewrite (wrap32_id (n - Z.of_nat j - 1)) by lia.
  destruct (Z.eqb_spec (n - Z.of_nat j - 1) 0) as [E|NE]; cbn [negb].
  - assert (Ej : Z.to_nat n = S j) by lia. rewrite Ej. cbn [mc_obn from_add]. apply f_equal2; [apply f_equal2; [apply f_equal2; [reflexivity | lia] | reflexivity] | lia].
  - replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia.
    specialize (IH (S j) Hp0 Hn Hn32 Hfrom ltac:(lia) ltac:(lia)).
    cbn [mc_obn from_add] in IH. rewrite <- IH. f_equal. apply f_equal2; [apply f_equal2; [apply f_equal2; [reflexivity | lia] | reflexivity] | lia].
Qed.

Lemma match_copy_eq : forall win ob put0 from n,
  0 <= put0 -> put0 + n <= arr_len ob -> 0 < n < 2 ^ 32 ->
  match from with FOut i => i < put0 | FWin _ => True end ->
  match_copy win (ob, put0, from, n) = (mc_obn win ob put0 from (Z.to_nat n), put0 + n, from_add from (Z.to_nat n), 0).
Proof.
  intros win ob put0 from n Hp0 Hn Hn1 Hfrom. unfold match_copy. cbn [snd].
  pose proof (mc_loop win ob put0 from n (Z.to_nat n) 0 Hp0 Hn ltac:(lia) Hfrom ltac:(lia) ltac:(lia)) as H.
  cbn [mc_obn from_add Z.of_nat] in H. rewrite Z.add_0_r, Z.sub_0_r, Z2Nat.id in H by lia. exact H.
Qed.

Definition mt_plan (s : inflate_state) (r : iregs) : option (fromptr * Z) :=
  let copy := wrap32 (ir_out r - ir_left r) in
  if copy <? is_offset s then
    let copy := wrap32 (is_offset s - copy) in
    if is_whave s <? copy then None
    else
      let cf := if is_wnext s <? copy
                then (wrap32 (copy - is_wnext s), FWin (is_wsize s - wrap32 (copy - is_wnext s)))
                else (copy, FWin (is_wnext s - copy)) in
      Some (snd cf, if is_length s <? fst cf then is_length s else fst cf)
  else Some (FOut (ir_put r - is_offset s), is_length s).

Definition mt_clamp (r : iregs) (copy : Z) : Z := if ir_left r <? copy then ir_left r else copy.

Lemma arm_MATCH_eq : forall s c r, is_sane s = 1 ->
  arm_MATCH ivar_ref (mkW s c r) =
    if ir_left r =? 0 then ALeave (mkW s c r)
    else match mt_plan s r with
         | None => ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_distance_too_far_back) r)
         | Some (from, copy0) =>
             let copy := mt_clamp r copy0 in
             let r1 := irset_left r (wrap32 (ir_left r - copy)) in
             let s1 := iset_length s (wrap32 (is_length s - copy)) in
             let '(ob, put, _, _) := match_copy (is_window s) (ic_outbuf c, ir_put r, from, copy) in
             if wrap32 (is_length s - copy) =? 0
             then ARun tt (mkW (iset_mode s1 LEN) (icset_outbuf c ob) (irset_put r1 put))
             else ARun tt (mkW s1 (icset_outbuf c ob) (irset_put r1 put))
         end.
Proof.
  intros s c r Hsane. unfold arm_MATCH. mstep1 (@gr_eq iregs).
  destruct (ir_left r =? 0); [reflexivity|].
  mstep1 (@gs_eq inflate_state). unfold mt_plan.
  destruct (wrap32 (ir_out r - ir_left r) <? is_offset s).
  - cbn [iv_aux ivar_ref]. rewrite Hsane. cbn [Z.eqb negb andb].
    destruct (is_whave s <? wrap32 (is_offset s - wrap32 (ir_out r - ir_left r))).
    + cbn [andb]. rewrite abind_run. rewrite abind_run. rewrite go_bad_eq. cbv beta iota. rewrite aret_eq. cbv beta iota. rewrite aret_eq. reflexivity.
    + cbn [andb]. destruct (is_wnext s <? wrap32 (is_offset s - wrap32 (ir_out r - ir_left r))); cbn [fst snd];
        mstep1 (@aret_eq (option (fromptr * Z))); unfold mt_clamp; mstep1 ur_eq; mstep1 us_eq; rewrite abind_run;
        cbn [w_s w_c w_r is_window iset_length ir_put irset_left];
        (destruct (match_copy _ _) as [[[ob put] fr] cp]); unfold wset_r, wset_c; cbn [w_s w_c w_r]; mstep1 (@gs_eq inflate_state);
        cbn [is_length iset_length]; (destruct (_ =? 0); [rewrite set_mode_eq | rewrite aret_eq]; reflexivity).
  - mstep1 (@aret_eq (option (fromptr * Z))). unfold mt_clamp. mstep1 ur_eq. mstep1 us_eq. rewrite abind_run.
    cbn [w_s w_c w_r is_window iset_length ir_put irset_left].
    destruct (match_copy _ _) as [[[ob put] fr] cp]. unfold wset_r, wset_c. cbn [w_s w_c w_r]. mstep1 (@gs_eq inflate_state).
    cbn [is_length iset_length]. destruct (_ =? 0); [rewrite set_mode_eq | rewrite aret_eq]; reflexivity.
Qed.
