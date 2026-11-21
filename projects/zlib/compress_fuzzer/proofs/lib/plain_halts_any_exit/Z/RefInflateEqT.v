(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItMath.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItSort.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItSimPre.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItSim2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItShape.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItTable.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItRep.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeA1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeR.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeA5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeA6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateEqD.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateEqA1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateEqA2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma applyw_agree : forall ws a1 a2 i,
  arr_len a2 = arr_len a1 ->
  (arr_get a2 i = arr_get a1 i \/ (In i (map fst ws) /\ 0 <= i < arr_len a1)) ->
  arr_get (applyw ws a2) i = arr_get (applyw ws a1) i.
Proof.
  induction ws as [|[j v] ws IH]; intros a1 a2 i HL H.
  - cbn in H |- *. destruct H as [H|[[] _]]. exact H.
  - rewrite !applyw_cons. apply IH; [rewrite !arr_len_set; exact HL|].
    cbn [map fst] in H. rewrite !arr_get_set. unfold arr_inb. rewrite HL, arr_len_set.
    destruct (Z.eqb_spec j i) as [->|NE]; cbn [andb].
    + destruct H as [H|[[H|H] R]].
      * destruct ((0 <=? i) && (i <? arr_len a1)); left; [reflexivity | exact H].
      * rewrite (proj2 (Z.leb_le 0 i)) by lia. rewrite (proj2 (Z.ltb_lt i _)) by lia. left; reflexivity.
      * destruct ((0 <=? i) && (i <? arr_len a1)); [left; reflexivity | right; split; [exact H | exact R]].
    + destruct H as [H|[[H|H] R]]; [left; exact H | exfalso; exact (NE H) | right; split; [exact H | exact R]].
Qed.

Lemma inflate_table_agree : forall ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2,
  0 <= codes <= 288 -> codes <= arr_len work1 -> arr_len work2 = arr_len work1 ->
  (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens1 i <= 15) ->
  (forall i, lens_ofs <= i < lens_ofs + codes -> arr_get lens2 i = arr_get lens1 i) ->
  (ty = CODES -> codes <= 19) -> 1 <= bits <= 15 ->
  arr_len tbl2 = arr_len tbl1 ->
  let '(ret1, tbl1', toff1, bits1, work1') := inflate_table ty lens1 lens_ofs codes tbl1 table bits work1 in
  let '(ret2, tbl2', toff2, bits2, work2') := inflate_table ty lens2 lens_ofs codes tbl2 table bits work2 in
  ret2 = ret1 /\ toff2 = toff1 /\ bits2 = bits1 /\ arr_len tbl2' = arr_len tbl1' /\ arr_len work2' = arr_len work1'
  /\ (forall i, (arr_get tbl2 i = arr_get tbl1 i \/ (table <= i < toff1 /\ 0 <= i < arr_len tbl1)) -> ret1 = 0 ->
                ty_ok ty (lens_list lens1 lens_ofs codes) bits -> arr_get tbl2' i = arr_get tbl1' i)
  /\ (forall i, ~ (table <= i < toff1) -> ret1 = 0 -> ty_ok ty (lens_list lens1 lens_ofs codes) bits ->
                arr_get tbl1' i = arr_get tbl1 i /\ arr_get tbl2' i = arr_get tbl2 i).
Proof.
  intros ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2 Hc Hw HLw Hl15 Hleq Hty Hb HLt.
  assert (Ell : lens_list lens2 lens_ofs codes = lens_list lens1 lens_ofs codes).
  { unfold lens_list. apply map_ext_in. intros a Ha. apply in_seq in Ha. apply Hleq. lia. }
  assert (Hl15' : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens2 i <= 15) by (intros i Hi; rewrite (Hleq i Hi); apply Hl15; exact Hi).
  rewrite (inflate_table_abs ty lens1 lens_ofs codes _ _ table bits Hc Hl15 eq_refl eq_refl Hty Hb tbl1 work1 Hw).
  rewrite (inflate_table_abs ty lens2 lens_ofs codes _ _ table bits Hc Hl15' eq_refl eq_refl Hty Hb tbl2 work2 ltac:(lia)).
  rewrite Ell.
  pose proof (ItSimPre.Hll lens1 lens_ofs codes _ _ Hc Hl15 eq_refl eq_refl) as Hll.
  destruct (it_abs (wl_of (lens_list lens1 lens_ofs codes)) (lens_list lens1 lens_ofs codes) ty table bits) as [[[[ret ws] toff] bits'] ww] eqn:EA.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite !arr_len_applyw; exact HLt|]. split; [rewrite !arr_len_applyw; exact HLw|].
  split.
  - intros i Hi Hret Hok.
    pose proof (it_abs_props (wl_of (lens_list lens1 lens_ofs codes)) (lens_list lens1 lens_ofs codes) table bits Hll eq_refl Hb ty Hok) as P.
    rewrite EA in P. specialize (P Hret). destruct P as (P1 & P2 & P3 & P4 & P5).
    apply applyw_agree; [exact HLt|]. destruct Hi as [Hi|[Hi R]]; [left; exact Hi | right]. split; [apply P4; exact Hi | exact R].
  - intros i Hi Hret Hok.
    pose proof (it_abs_props (wl_of (lens_list lens1 lens_ofs codes)) (lens_list lens1 lens_ofs codes) table bits Hll eq_refl Hb ty Hok) as P.
    rewrite EA in P. specialize (P Hret). destruct P as (P1 & P2 & P3 & P4 & P5).
    split; apply applyw_other; intros v Hin; pose proof (P3 _ _ Hin); lia.
Qed.

Definition FLL (s : inflate_state) (c : icall) (r : iregs) : Prop :=
  CORE s /\ 4 <= is_ncode s <= 19 /\ 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30 /\ 0 <= is_have s <= is_ncode s
  /\ (forall k, 0 <= k < is_have s -> 0 <= arr_get (is_lens s) (arr_get order_a k) <= 7).

Definition FCL (s : inflate_state) (c : icall) (r : iregs) : Prop :=
  CORE s /\ 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30 /\ 0 <= is_have s
  /\ (forall i, 0 <= i < is_have s -> 0 <= arr_get (is_lens s) i <= 15)
  /\ (forall i, 0 <= i < 19 -> 0 <= arr_get (is_lens s) i <= 15).

Lemma BITSv3 : forall h, 0 <= wrap16 (BITSv h 3) <= 7.
Proof. intros h. pose proof (BITSv_bound h 3 ltac:(lia)). rewrite wrap16_id by lia. lia. Qed.

Lemma RES2_step3 {A B} (m1 m2 : AM A) (f1 f2 : A -> AM B) w1 w2 a1 a2 w1' w2' :
  m1 w1 = ARun a1 w1' -> m2 w2 = ARun a2 w2' -> RES2 (f1 a1 w1') (f2 a2 w2') -> RES2 (abind m1 f1 w1) (abind m2 f2 w2).
Proof. intros E1 E2 H. unfold abind. rewrite E1, E2. exact H. Qed.
Ltac rstep3 lem := aflat; eapply RES2_step3; [apply lem | apply lem |]; cbv beta iota.

Section Tables.
  Variable flush : Z.
  Hypothesis fastc : FASTC.

  Lemma lenlens_while1_cong : forall k s1 s2 c r,
    FLL s1 c r -> is_mode s1 = LENLENS -> IEQ s1 s2 -> UW s1 c r ->
    RES2 (lenlens_while1 k (mkW s1 c r)) (lenlens_while1 k (mkW s2 c r)).
  Proof.
    induction k as [|k IH]; intros s1 s2 c r HF E HQ HU.
    - cbn [lenlens_while1]. apply RES2_ret; apply WMID_mk; assumption.
    - notHB HU E W5 F0. pose proof HQ as HQ0. pose proof HF as (HC & Hnc & Hnl & Hnd & Hh & HLs). ieq_open HQ E.
      pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & _).
      rewrite !lenlens_while1_S.
      rstep gs_eq. nrm s1 s2 W5 F0.
      destruct (Z.ltb_spec (is_have s1) (is_ncode s1)) as [LT|GE].
      + pose proof (order_a_range (is_have s1) ltac:(lia)) as OR.
        aflat. rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]. intros [] r1 HU1 _. cbv beta.
        unfold BITS. rstep gr_eq. rstep gs_eq. nrm s1 s2 W5 F0. unfold set_lens. rstep us_eq. nrm s1 s2 W5 F0. rstep us_eq. nrm s1 s2 W5 F0.
        unfold DROPBITS. rstep ur_eq. rewrite wrap32_id by lia.
        apply IH.
        * split; [core_keep HC; apply CORE_length; exact HC|]. sacc. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          intros j Hj. rewrite arr_get_set. unfold arr_inb. rewrite CA1.
          replace ((0 <=? arr_get order_a (is_have s1)) && (arr_get order_a (is_have s1) <? 320)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
          destruct (Z.eqb_spec (arr_get order_a (is_have s1)) (arr_get order_a j)) as [Ej|Ej]; cbn [andb]; [apply BITSv3|].
          apply HLs. destruct (Z.eq_dec j (is_have s1)) as [->|]; [congruence|lia].
        * sacc. exact E.
        * ieq_close E; try (rewrite !arr_len_set; assumption).
          intros j Hj. rewrite !arr_get_set. unfold arr_inb. rewrite QLlens, CA1.
          replace ((0 <=? arr_get order_a (is_have s1)) && (arr_get order_a (is_have s1) <? 320)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
          destruct (Z.eqb_spec (arr_get order_a (is_have s1)) (arr_get order_a j)) as [Ej|Ej]; cbn [andb]; [reflexivity|].
          apply Qlens1. destruct (Z.eq_dec j (is_have s1)) as [->|]; [congruence|lia].
        * uw0 W5 F0.
      + apply RES2_ret; apply WMID_mk; [exact HQ0 | exact HU].
  Qed.

  Lemma lens_repeat_cong : forall copy len s1 s2 c r,
    CORE s1 -> is_mode s1 = CODELENS -> IEQ s1 s2 -> UW s1 c r ->
    0 <= copy -> 0 <= is_have s1 -> is_have s1 + copy <= arr_len (is_lens s1) ->
    RES2 (lens_repeat copy len (mkW s1 c r)) (lens_repeat copy len (mkW s2 c r)).
  Proof.
    intros copy len s1 s2 c r HC E HQ HU Hc Hh Hhl.
    pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & _).
    assert (Hhc : is_have s1 + copy < 2 ^ 32) by (rewrite CA1 in Hhl; lia). notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E.
    destruct (lens_repeat_eq copy len s1 c r Hc Hh Hhc) as (l1 & E1 & L1 & G1).
    destruct (lens_repeat_eq copy len s2 c r Hc ltac:(rewrite Qhave; exact Hh) ltac:(rewrite Qhave; exact Hhc)) as (l2 & E2 & L2 & G2).
    rewrite E1, E2. rewrite Qhave. cbn [RES2]. split; [reflexivity|]. apply WMID_mk; [|uw0 W5 F0].
    ieq_close E; try (rewrite ?L1, ?L2; assumption).
    intros i Hi. rewrite G1, G2, QLlens, Qhave. destruct ((is_have s1 <=? i) && (i <? is_have s1 + copy) && (i <? arr_len (is_lens s1))) eqn:C; [reflexivity|].
    apply Qlens2. destruct Hi as [Hi|Hi]; [left; exact Hi|].
    destruct (Z.lt_ge_cases i (is_have s1)); [right; lia|]. exfalso.
    rewrite (proj2 (Z.leb_le _ _)) in C by lia. rewrite (proj2 (Z.ltb_lt i (is_have s1 + copy))) in C by lia. cbn [andb] in C.
    apply Z.ltb_ge in C. lia.
  Qed.

  Lemma codelens_body_cong : forall s1 s2 c r,
    CL s1 c r -> is_have s1 < is_nlen s1 + is_ndist s1 -> IEQ s1 s2 -> UW s1 c r ->
    RES2 (codelens_body (mkW s1 c r)) (codelens_body (mkW s2 c r)).
  Proof.
    intros s1 s2 c r HCL Hlt HQ HU.
    pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
    pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & _).
    notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E.
    unfold codelens_body.
    rstep gs_eq. nrm s1 s2 W5 F0.
    unfold DECODE1 at 1 2. aflat.
    eapply RES2_bind_lock; [apply DECODE_k_LOCK; intros h; exact (tbl_eq_DECODE1 s1 s2 CODES _ _ Qctbl h) | exact HQ0 | exact HU |].
    intros here r1 HU1 E1. cbv beta.
    destruct (code_val here <? 16) eqn:V16.
    -
      unfold DROPBITS. rstep ur_eq. rstep gs_eq. nrm s1 s2 W5 F0. unfold set_lens. rstep us_eq. nrm s1 s2 W5 F0. rstep us_eq. nrm s1 s2 W5 F0.
      apply RES2_ret. apply WMID_mk; [|uw0 W5 F0].
      ieq_close E; try (rewrite !arr_len_set; assumption).
      intros i Hi. rewrite !arr_get_set. unfold arr_inb. rewrite QLlens.
      destruct ((is_have s1 =? i) && _) eqn:C; [reflexivity|]. apply Qlens2.
      destruct Hi as [Hi|Hi]; [left; exact Hi|]. rewrite wrap32_id in Hi by lia.
      destruct (Z.lt_ge_cases i (is_have s1)); [right; lia|]. exfalso.
      rewrite CA1 in C. rewrite (proj2 (Z.eqb_eq (is_have s1) i)) in C by lia. cbn [andb] in C.
      rewrite (proj2 (Z.leb_le 0 (is_have s1))) in C by lia. rewrite (proj2 (Z.ltb_lt (is_have s1) 320)) in C by lia. discriminate C.
    -
      assert (KT : forall len copy rk, UW s1 c rk -> 0 <= copy ->
        RES2 ((do s <- gs (fun s0 => s0);
               if is_nlen s + is_ndist s <? is_have s + copy then go_bad MSG_invalid_bit_length_repeat;; aret false
               else lens_repeat copy len;; aret true)%am (mkW s1 c rk))
             ((do s <- gs (fun s0 => s0);
               if is_nlen s + is_ndist s <? is_have s + copy then go_bad MSG_invalid_bit_length_repeat;; aret false
               else lens_repeat copy len;; aret true)%am (mkW s2 c rk))).
      { intros len copy rk HUk Hc. rstep gs_eq. nrm s1 s2 W5 F0.
        destruct (Z.ltb_spec (is_nlen s1 + is_ndist s1) (is_have s1 + copy)) as [LT|GE].
        - unfold go_bad, set_msg, set_mode. aflat. rstep uc_eq. rstep us_eq. apply RES2_ret. wmid E W5 F0.
        - aflat. eapply RES2_bind; [apply lens_repeat_cong; [exact HC | exact E | exact HQ0 | exact HUk | exact Hc | lia | rewrite CA1; lia]|].
          intros [] sa sb c2 r2 HQ2 HU2 _. apply RES2_ret. apply WMID_mk; assumption. }
      destruct (code_val here =? 16).
      + aflat. rlock SFREE_NEEDBITS; [exact HQ0 | exact HU1 |]. intros [] r2 HU2 _. cbv beta. aflat.
        unfold DROPBITS at 1 2. rstep ur_eq. rstep gs_eq. nrm s1 s2 W5 F0.
        destruct (is_have s1 =? 0) eqn:H0.
        * unfold go_bad, set_msg, set_mode. aflat. rstep uc_eq. rstep us_eq. rstep aret_eq. apply RES2_ret. wmid E W5 F0.
        * rewrite (Qlens2 (is_have s1 - 1)) by (right; apply Z.eqb_neq in H0; lia).
          unfold BITS. aflat. rstep gr_eq. rstep ur_eq. rstep aret_eq.
          apply KT; [apply (UW_regs s1 c r2); [exact HU2| reflexivity | reflexivity] | pose proof (BITSv_bound (ir_hold (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) (code_bits here))) (wrap32 (ir_bits r2 - code_bits here)))) 2 ltac:(lia)); lia].
      + destruct (code_val here =? 17).
        * aflat. rlock SFREE_NEEDBITS; [exact HQ0 | exact HU1 |]. intros [] r2 HU2 _. cbv beta. aflat.
          unfold DROPBITS at 1 2. rstep ur_eq. unfold BITS. rstep gr_eq. rstep ur_eq. rstep aret_eq.
          apply KT; [apply (UW_regs s1 c r2); [exact HU2| reflexivity | reflexivity] | match goal with |- 0 <= 3 + BITSv ?h ?n => pose proof (BITSv_bound h n ltac:(lia)); lia end].
        * aflat. rlock SFREE_NEEDBITS; [exact HQ0 | exact HU1 |]. intros [] r2 HU2 _. cbv beta. aflat.
          unfold DROPBITS at 1 2. rstep ur_eq. unfold BITS. rstep gr_eq. rstep ur_eq. rstep aret_eq.
          apply KT; [apply (UW_regs s1 c r2); [exact HU2| reflexivity | reflexivity] | match goal with |- 0 <= 11 + BITSv ?h ?n => pose proof (BITSv_bound h n ltac:(lia)); lia end].
  Qed.

  Lemma codelens_while_cong : forall k s1 s2 c r,
    CL s1 c r -> IEQ s1 s2 -> UW s1 c r ->
    RES2 (codelens_while k (mkW s1 c r)) (codelens_while k (mkW s2 c r)).
  Proof.
    induction k as [|k IH]; intros s1 s2 c r HCL HQ HU.
    - cbn [codelens_while]. apply RES2_ret; apply WMID_mk; assumption.
    - pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
      notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E.
      rewrite !codelens_while_S. rstep gs_eq. nrm s1 s2 W5 F0.
      destruct (Z.ltb_spec (is_have s1) (is_nlen s1 + is_ndist s1)) as [LT|GE]; [|apply RES2_ret; apply WMID_mk; [exact HQ0|exact HU]].
      pose proof (codelens_body_spec c s1 r HCL LT) as B.
      eapply RES2_bind; [exact (codelens_body_cong s1 s2 c r HCL LT HQ0 HU)|].
      intros b sa sb c' r' HQ' HU' Eb. rewrite Eb in B.
      destruct b; [|apply RES2_ret; apply WMID_mk; assumption].
      destruct B as (-> & HCL' & _). apply IH; assumption.
  Qed.

  Lemma arm_CODELENS_cong : arm_cong CODELENS CL (arm_CODELENS ivar_ref flush).
  Proof.
    intros s1 s2 c r HCL E HQ HU.
    pose proof HCL as (HC & HR & _ & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
    notHB HU E W5 F0. pose proof HQ as HQ0.
    unfold arm_CODELENS.
    pose proof (codelens_while_spec c 321 s1 r HCL ltac:(cbn; lia)) as W.
    aflat. eapply RES2_bind; [exact (codelens_while_cong 321 s1 s2 c r HCL HQ0 HU)|].
    intros [] t1 t2 c' r' HQ' HU' Ew. rewrite Ew in W.
    pose proof HQ' as HQ1.
    destruct W as [(-> & HCL1 & Hh1 & En1 & Ed1 & _)|(Hm1 & _)].
    2:{ ieq_open HQ' Hm1. rstep gs_eq. sacc. rewrite Qmode, Hm1. change (BAD =? BAD) with true. cbv iota.
        apply RES2_ret. apply WMID_mk; assumption. }
    pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & _ & Hnl1 & Hnd1 & Hh1' & HLs1 & HT1 & HWF1 & HWB1).
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    clear HQ0. notHB HU' E1 W5' F0'. ieq_open HQ' E1.
    rstep gs_eq. nrm t1 t2 W5' F0'. rewrite Qmode, E1. change (CODELENS =? BAD) with false. cbv iota.
    rewrite (Qlens2 256) by (right; lia).
    destruct (arr_get (is_lens t1) 256 =? 0).
    { unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. wmid E1 W5' F0'. }

    pose proof (inflate_table_TBLg LENS (is_lens t1) 0 (is_nlen t1) (is_codes t1) 0 9 (is_work t1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite CB3; lia)) as TL.
    pose proof (inflate_table_agree LENS (is_lens t1) (is_lens t2) 0 (is_nlen t1) (is_codes t1) (is_codes t2) 0 9 (is_work t1) (is_work t2)
                  ltac:(lia) ltac:(rewrite CB2; lia) QLwork ltac:(intros i Hi; apply HLs1; lia) ltac:(intros i Hi; apply Qlens2; right; lia)
                  ltac:(intros X; discriminate X) ltac:(lia) QLcodes) as AL.
    destruct (inflate_table LENS (is_lens t1) 0 (is_nlen t1) (is_codes t1) 0 9 (is_work t1)) as [[[[retL tblL] nextL] lenbitsL] workL].
    destruct (inflate_table LENS (is_lens t2) 0 (is_nlen t1) (is_codes t2) 0 9 (is_work t2)) as [[[[retL2 tblL2] nextL2] lenbitsL2] workL2].
    destruct AL as (-> & -> & -> & ALt & ALw & ALa & ALo). destruct TL as [[TL5 TL6] TL].
    cbv beta iota. aflat. rstep3 us_eq. aflat. rstep ur_eq.
    destruct (Z.eqb_spec retL 0) as [RL0|RL0]; cbn [negb].
    2:{ unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. apply WMID_mk; [|uw0 W5' F0'].
        ieq_close E1; try (rewrite ?ALt, ?ALw; first [assumption | reflexivity]). }
    specialize (TL RL0). destruct TL as (TL1 & TL2 & TL3 & TL4). cbn [it_room] in TL2. unfold ENOUGH_LENS in TL2.
    assert (TYL : ty_ok LENS (lens_list (is_lens t1) 0 (is_nlen t1)) 9) by (cbn [ty_ok]; rewrite NC_lens_list by lia; lia).

    rstep gs_eq. sacc. ieq_rw t1 t2.
    pose proof (inflate_table_TBLg DISTS (is_lens t1) (is_nlen t1) (is_ndist t1) tblL nextL 6 workL
                  ltac:(lia) ltac:(rewrite TL6, CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite TL5, CB3; lia)) as TD.
    pose proof (inflate_table_agree DISTS (is_lens t1) (is_lens t2) (is_nlen t1) (is_ndist t1) tblL tblL2 nextL 6 workL workL2
                  ltac:(lia) ltac:(rewrite TL6, CB2; lia) ALw ltac:(intros i Hi; apply HLs1; lia) ltac:(intros i Hi; apply Qlens2; right; lia)
                  ltac:(intros X; discriminate X) ltac:(lia) ALt) as AD.
    destruct (inflate_table DISTS (is_lens t1) (is_nlen t1) (is_ndist t1) tblL nextL 6 workL) as [[[[retD tblD] nextD] distbitsD] workD].
    destruct (inflate_table DISTS (is_lens t2) (is_nlen t1) (is_ndist t1) tblL2 nextL 6 workL2) as [[[[retD2 tblD2] nextD2] distbitsD2] workD2].
    destruct AD as (-> & -> & -> & ADt & ADw & ADa & ADo). destruct TD as [[TD5 TD6] TD].
    cbv beta iota. aflat. rstep3 us_eq. aflat. rstep ur_eq.
    destruct (Z.eqb_spec retD 0) as [RD0|RD0]; cbn [negb].
    2:{ unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. apply WMID_mk; [|uw0 W5' F0'].
        ieq_close E1; try (rewrite ?ADt, ?ADw, ?ALt, ?ALw; first [assumption | reflexivity]). }
    specialize (TD RD0). destruct TD as (TD1 & TD2 & TD3 & TD4). cbn [it_room] in TD2. unfold ENOUGH_DISTS in TD2.
    assert (TYD : ty_ok DISTS (lens_list (is_lens t1) (is_nlen t1) (is_ndist t1)) 6) by (cbn [ty_ok]; rewrite NC_lens_list by lia; lia).
    unfold set_mode at 1 2. aflat. rstep us_eq.

    match goal with |- RES2 (_ (mkW ?a1 _ ?rr)) (_ (mkW ?a2 _ _)) =>
      assert (HQ3 : IEQ a1 a2); [| assert (HC3 : CORE a1); [| assert (HU3 : UW a1 c rr)]] end.
    { ieq_close E1; try (rewrite ?ADt, ?ADw, ?ALt, ?ALw; first [assumption | reflexivity]).
      all: cbn [tbl_eq].
      - exists (nextL - 0). split.
        + apply (TBLg_ext LENS (fun x => arr_get tblL (0 + x))); [|exact TL3]. intros x Hx. apply TD4. lia.
        + intros i Hi. destruct (ADo i ltac:(lia) RD0 TYD) as [-> ->]. apply ALa; [|exact RL0|exact TYL]. right. rewrite CB3. lia.
      - exists (nextD - nextL). split; [exact TD3|]. intros i Hi. apply ADa; [|exact RD0|exact TYD]. right. rewrite TL5, CB3. lia. }
    { core_keep HC1; [rewrite TD6, TL6; reflexivity | rewrite TD5, TL5; reflexivity | apply CORE_length; exact HC1]. }
    { uw0 W5' F0'. }
    destruct (iv_flush_exits ivar_ref && (flush =? Z_TREES)).
    - apply RES2_leave. apply WMID_mk; [exact HQ3 | exact HU3].
    - apply (arm_LEN__cong fastc); [exact HC3 | reflexivity | exact HQ3 | exact HU3].
  Qed.

  Lemma lenlens_while2_cong : forall k s1 s2 c r,
    CORE s1 -> 0 <= is_have s1 -> is_mode s1 = LENLENS -> IEQ s1 s2 -> UW s1 c r ->
    RES2 (lenlens_while2 k (mkW s1 c r)) (lenlens_while2 k (mkW s2 c r)).
  Proof.
    induction k as [|k IH]; intros s1 s2 c r HC Hh E HQ HU.
    - cbn [lenlens_while2]. apply RES2_ret; apply WMID_mk; assumption.
    - notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E.
      pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & _).
      rewrite !lenlens_while2_S. rstep gs_eq. nrm s1 s2 W5 F0.
      destruct (Z.ltb_spec (is_have s1) 19) as [LT|GE]; [|apply RES2_ret; apply WMID_mk; [exact HQ0 | exact HU]].
      pose proof (order_a_range (is_have s1) ltac:(lia)) as OR.
      unfold set_lens. rstep us_eq. nrm s1 s2 W5 F0. rstep us_eq. nrm s1 s2 W5 F0. rewrite wrap32_id by lia.
      apply IH.
      + core_keep HC; apply CORE_length; exact HC.
      + sacc. lia.
      + sacc. exact E.
      + ieq_close E; try (rewrite !arr_len_set; assumption).
        intros j Hj. rewrite !arr_get_set. unfold arr_inb. rewrite QLlens, CA1.
        replace ((0 <=? arr_get order_a (is_have s1)) && (arr_get order_a (is_have s1) <? 320)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
        destruct (Z.eqb_spec (arr_get order_a (is_have s1)) (arr_get order_a j)) as [Ej|Ej]; cbn [andb]; [reflexivity|].
        apply Qlens1. destruct (Z.eq_dec j (is_have s1)) as [->|]; [congruence|lia].
      + uw0 W5 F0.
  Qed.

  Lemma arm_LENLENS_cong : arm_cong LENLENS LL (arm_LENLENS ivar_ref flush).
  Proof.
    intros s1 s2 c r HLL E HQ HU.
    pose proof HLL as (HC & HR & _ & HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs & HWF & HWB).
    notHB HU E W5 F0. pose proof HQ as HQ0.
    unfold arm_LENLENS.
    pose proof (lenlens_while1_spec c 19 s1 r HLL ltac:(cbn; lia)) as W1.
    aflat. eapply RES2_bind.
    { apply lenlens_while1_cong; [|exact E|exact HQ0|exact HU]. split; [exact HC|]. repeat (split; [lia|]). exact HLs. }
    intros [] t1 t2 c' r1 HQ1 HU1 Ew. rewrite Ew in W1.
    destruct W1 as (-> & HLL1 & Hh1 & Enc & Enl & End & _ & _ & _ & Ecd & Ewk).
    pose proof HLL1 as (HC1 & HR1 & E1 & HCm1 & Hb1 & Hnc1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HWF1 & HWB1).
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    notHB HU1 E1 W5' F0'.
    destruct (lenlens_while2_spec c 19 t1 r1 HC1 ltac:(lia) ltac:(cbn; lia) HLs1) as (lens19 & EQ2 & HL19 & HLs19).
    aflat. eapply RES2_bind; [apply lenlens_while2_cong; [exact HC1|lia|exact E1|exact HQ1|exact HU1]|].
    intros [] u1 u2 c'' r2 HQ2 HU2 Ew2. rewrite EQ2 in Ew2. injection Ew2; intros <- <- <-.
    assert (HLs' : forall i, 0 <= i < 0 + 19 -> 0 <= arr_get lens19 i <= 7).
    { intros i Hi. destruct (order_a_onto i ltac:(lia)) as [j [Hj <-]]. apply HLs19. exact Hj. }
    clear HQ0. pose proof HQ2 as HQ0.
    assert (E2 : is_mode (iset_have (iset_lens t1 lens19) 19) = LENLENS) by (sacc; exact E1).
    ieq_open HQ2 E2. revert Qlens1 QLlens QLwork QLcodes Qhave. sacc. intros Qlens1 QLlens QLwork QLcodes Qhave.
    assert (HLeq : forall i, 0 <= i < 0 + 19 -> arr_get (is_lens u2) i = arr_get lens19 i).
    { intros i Hi. destruct (order_a_onto i ltac:(lia)) as [j [Hj <-]]. apply Qlens1. exact Hj. }
    rstep gs_eq. sacc. ieq_rw (iset_have (iset_lens t1 lens19) 19) u2.
    revert Qnlen Qndist. sacc. intros Qnlen Qndist. rewrite ?Qnlen, ?Qndist.
    pose proof (inflate_table_TBLg CODES lens19 0 19 (is_codes t1) 0 7 (is_work t1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; pose proof (HLs' i Hi); lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; split; [lia|]; split; [lia|]; apply lens_list_forall; intros i Hi; pose proof (HLs' i Hi); lia)
                  ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; rewrite CB3; lia)) as TC.
    pose proof (inflate_table_agree CODES lens19 (is_lens u2) 0 19 (is_codes t1) (is_codes u2) 0 7 (is_work t1) (is_work u2)
                  ltac:(lia) ltac:(rewrite CB2; lia) QLwork ltac:(intros i Hi; pose proof (HLs' i Hi); lia) HLeq
                  ltac:(intros _; lia) ltac:(lia) QLcodes) as AC.
    destruct (inflate_table CODES lens19 0 19 (is_codes t1) 0 7 (is_work t1)) as [[[[retC tblC] nextC] lenbitsC] workC].
    destruct (inflate_table CODES (is_lens u2) 0 19 (is_codes u2) 0 7 (is_work u2)) as [[[[retC2 tblC2] nextC2] lenbitsC2] workC2].
    destruct AC as (-> & -> & -> & ACt & ACw & ACa & ACo). destruct TC as [[TC5 TC6] TC].
    cbv beta iota. aflat. rstep3 us_eq. aflat. rstep ur_eq.
    destruct (Z.eqb_spec retC 0) as [RC0|RC0]; cbn [negb].
    2:{ unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. apply WMID_mk; [|uw0 W5' F0'].
        ieq_close E1; try (rewrite ?ACt, ?ACw; first [assumption | reflexivity]). }
    specialize (TC RC0). destruct TC as (TC1 & TC2 & TC3 & TC4). cbn [it_room] in TC2.
    assert (TYC : ty_ok CODES (lens_list lens19 0 19) 7).
    { cbn [ty_ok]. rewrite NC_lens_list by lia. split; [lia|]. split; [lia|]. apply lens_list_forall. intros i Hi. pose proof (HLs' i Hi). lia. }
    aflat. rstep us_eq. unfold set_mode at 1 2. aflat. rstep us_eq.
    apply arm_CODELENS_cong.
    -
      unfold CL. sacc. split; [core_keep HC1; [rewrite HL19, CB1; reflexivity | rewrite TC6; reflexivity | rewrite TC5; reflexivity | apply CORE_length; exact HC1]|].
      split; [eapply REGS_cview; [apply REGS_ret; exact HR1|reflexivity|reflexivity]|].
      split; [reflexivity|]. split; [common_keep HCm1|]. split; [left; exact Hb1|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [intros i Hi; exfalso; lia|].
      split; [cbn [cpok]; split; [lia|]; exists (nextC - 0); split; [lia|]; exact TC3|].
      split; [exact HWF1|exact HWB1].
    - reflexivity.
    - ieq_close E1; try (rewrite ?ACt, ?ACw; first [assumption | reflexivity]).
      + intros i [Hi|Hi]; [apply HLeq; lia|exfalso; lia].
      + cbn [tbl_eq]. exists (nextC - 0). split; [exact TC3|]. intros i Hi. apply ACa; [|exact RC0|exact TYC]. right. rewrite CB3. lia.
    - uw0 W5' F0'.
  Qed.

  Definition FW (s : inflate_state) (c : icall) (r : iregs) : Prop := WINV (mkW s c r).

  Lemma arm_TABLE_cong : arm_cong TABLE FW (arm_TABLE ivar_ref flush).
  Proof.
    intros s1 s2 c r HW E HQ HU. unfold FW in HW. pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb14].
    pose proof (CORE_length s1 HC) as HL0.
    notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_TABLE.
    aflat. rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]. intros [] r1 HU1 E1.
    destruct (NEEDBITS_spec c 14 s1 r HR ltac:(lia)) as [(r1' & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1' & EQ & _)]; rewrite EQ in E1; [|discriminate E1].
    injection E1; intros ->. cbv beta.
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _).
    pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
    unfold BITS, DROPBITS.
    aflat. rstep gr_eq. aflat. rstep us_eq. aflat. rstep ur_eq.
    aflat. rstep gr_eq. aflat. rstep us_eq. aflat. rstep ur_eq.
    aflat. rstep gr_eq. aflat. rstep us_eq. aflat. rstep ur_eq.
    aflat. rstep gs_eq. nrm s1 s2 W5 F0.
    rewrite (wrap32_id (ir_bits r1 - 5)) by lia. rewrite (wrap32_id (ir_bits r1 - 5 - 5)) by lia. rewrite (wrap32_id (ir_bits r1 - 5 - 5 - 4)) by lia.
    rewrite !BITSv_mod by (repeat (try apply Z.shiftr_nonneg); lia).
    pose proof (mod_pow2_range (ir_hold r1) 5 ltac:(lia)) as M1.
    pose proof (mod_pow2_range (Z.shiftr (ir_hold r1) 5) 5 ltac:(lia)) as M2.
    pose proof (mod_pow2_range (Z.shiftr (Z.shiftr (ir_hold r1) 5) 5) 4 ltac:(lia)) as M3.
    match goal with |- RES2 (_ (mkW _ _ ?r4)) _ => set (r' := r4) in *; assert (HR' : REGS c r') end.
    { subst r'. apply REGS_holdbits; [apply REGS_holdbits; [apply REGS_holdbits; [exact HR1|]|]|].
      all: repeat (apply HB_drop); try (split; [exact RB1|exact RHO1]); lia. }
    destruct ((286 <? _) || (30 <? _)) eqn:Cbad.
    - unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. wmid E W5 F0.
    - apply Bool.orb_false_iff in Cbad as [C1 C2]. apply Z.ltb_ge in C1. apply Z.ltb_ge in C2.
      aflat. rstep us_eq. unfold set_mode at 1 2. aflat. rstep us_eq.
      apply arm_LENLENS_cong.
      + unfold LL. sacc. split; [core_keep HC; exact HL0|]. split; [exact HR'|]. split; [reflexivity|]. split; [common_keep HCm|].
        subst r'. sacc. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [intros k Hk; exfalso; lia|]. split; [rewrite Eo1; exact HWF|rewrite Ep1; exact HWB].
      + reflexivity.
      + ieq_close E. intros k Hk. exfalso. lia.
      + uw0 W5 F0.
  Qed.
End Tables.
