(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqA1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqA2.

Module RefInflateEqT.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItMath.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSort.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSimPre.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSim2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItCover.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItShape.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.ItRep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqA1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqA2.
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
  pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSimPre.Hll lens1 lens_ofs codes _ _ Hc Hl15 eq_refl eq_refl) as Hll.
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
End RefInflateEqT.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateEqS.RefInflateEqT.

Module RefInflateEqF.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeF1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeF2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqA1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateEqA2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma land_zmask_any : forall h n, 0 <= n < 32 -> Z.land h (zmask n) = h mod 2 ^ n.
Proof.
  intros h n Hn. rewrite zmask_pow2 by lia.
  replace (2 ^ n - 1) with (Z.ones n) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  apply Z.land_ones. lia.
Qed.

Lemma land_zmask_range : forall h n, 0 <= n < 32 -> 0 <= Z.land h (zmask n) < 2 ^ n.
Proof. intros h n Hn. rewrite land_zmask_any by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma code_val_range : forall e, 0 <= code_val e <= 65535.
Proof.
  intros e. unfold code_val. split; [apply Z.land_nonneg; right; lia|].
  replace 65535 with (Z.ones 16) by reflexivity. rewrite Z.land_ones by lia.
  change (Z.ones 16) with (2 ^ 16 - 1). pose proof (Z.mod_pos_bound (Z.shiftr e 16) (2 ^ 16) ltac:(lia)). lia.
Qed.

Lemma wrap32_range' : forall z, 0 <= wrap32 z < 2 ^ 32.
Proof. intros z. apply wrap32_range. Qed.


Section FastCong.
  Variable x1 : ffx.
Variable x2 : ffx.
Variable s1 : inflate_state.
Variable s2 : inflate_state.

  Hypothesis EXin : x_input x2 = x_input x1.
  Hypothesis EXlast : x_last x2 = x_last x1.
  Hypothesis EXbeg : x_beg x2 = x_beg x1.
  Hypothesis EXend : x_end x2 = x_end x1.
  Hypothesis EXws : x_wsize x2 = x_wsize x1.
  Hypothesis EXwh : x_whave x2 = x_whave x1.
  Hypothesis EXwn : x_wnext x2 = x_wnext x1.
  Hypothesis EXlm : x_lmask x2 = x_lmask x1.
  Hypothesis EXdm : x_dmask x2 = x_dmask x1.
  Hypothesis EXsane : x_sane x2 = x_sane x1.
  Definition W (j : Z) : Prop := arr_get (x_window x2) j = arr_get (x_window x1) j.
  Hypothesis EW : forall j, 0 <= j < x_whave x1 -> W j.

  Hypothesis Xwh : 0 <= x_whave x1.
  Hypothesis Xwn : 0 <= x_wnext x1.
  Hypothesis Xws : 0 <= x_wsize x1 < 2 ^ 32.
  Hypothesis Xz : x_wsize x1 = 0 -> x_whave x1 = 0 /\ x_wnext x1 = 0.
  Hypothesis Xnz : x_wsize x1 <> 0 -> x_wnext x1 < x_wsize x1 /\ x_whave x1 <= x_wsize x1.
  Hypothesis Xfill : x_wsize x1 <> 0 -> x_whave x1 < x_wsize x1 -> x_wnext x1 = x_whave x1.
  Hypothesis Xsane : x_sane x1 = 1.

  Hypothesis EL : is_lencode s2 = is_lencode s1.
  Hypothesis ED : is_distcode s2 = is_distcode s1.
  Variable okL : Z -> Prop.
Variable okD : Z -> Prop.
  Hypothesis HL0 : forall i, okL i -> code_at s2 (is_lencode s1) i = code_at s1 (is_lencode s1) i.
  Hypothesis HL1 : forall h, okL (Z.land h (x_lmask x1)).
  Hypothesis HL2 : forall i h, okL i ->
    let e := code_at s1 (is_lencode s1) i in
    code_op e <> 0 -> Z.land (code_op e) 16 = 0 -> Z.land (code_op e) 64 = 0 ->
    okL (code_val e + Z.land h (zmask (code_op e))).
  Hypothesis HD0 : forall i, okD i -> code_at s2 (is_distcode s1) i = code_at s1 (is_distcode s1) i.
  Hypothesis HD1 : forall h, okD (Z.land h (x_dmask x1)).
  Hypothesis HD2 : forall i h, okD i ->
    let e := code_at s1 (is_distcode s1) i in
    Z.land (code_op e) 16 = 0 -> Z.land (code_op e) 64 = 0 ->
    okD (code_val e + Z.land h (zmask (code_op e))).


  Lemma fpull_c : forall f, fpull x2 f = fpull x1 f.
  Proof. intros f. unfold fpull. rewrite EXin. reflexivity. Qed.

  Lemma fpull2_if_c : forall f, fpull2_if x2 f = fpull2_if x1 f.
  Proof. intros f. unfold fpull2_if. rewrite !fpull_c. reflexivity. Qed.

  Lemma cp1_c : forall f, (forall i, f_from f = FWin i -> W i) -> cp1 x2 f = cp1 x1 f.
  Proof.
    intros f Hw. unfold cp1. destruct (f_from f) as [i|i] eqn:Ef; [| reflexivity].
    rewrite (Hw i eq_refl). reflexivity.
  Qed.

  Lemma cp1_fields : forall x f,
    f_in (cp1 x f) = f_in f /\ f_out (cp1 x f) = f_out f + 1 /\ f_hold (cp1 x f) = f_hold f /\ f_bits (cp1 x f) = f_bits f
    /\ f_len (cp1 x f) = f_len f /\ f_dist (cp1 x f) = f_dist f /\ f_op (cp1 x f) = f_op f /\ f_from (cp1 x f) = from_succ (f_from f).
  Proof. intros x f. unfold cp1. destruct f; cbn. repeat split; reflexivity. Qed.

  Definition SRC (n : Z) (f : ffs) : Prop :=
    match f_from f with
    | FOut _ => True
    | FWin i => forall j, i <= j < i + n -> W j
    end.

  Lemma SRC_le : forall n m f, SRC n f -> m <= n -> SRC m f.
  Proof. intros n m f H Hm. unfold SRC in *. destruct (f_from f); [| exact I]. intros j Hj. apply H. lia. Qed.

  Lemma SRC_cp1 : forall n f, SRC n f -> 1 <= n -> cp1 x2 f = cp1 x1 f /\ SRC (n - 1) (cp1 x1 f).
  Proof.
    intros n f H Hn. pose proof (cp1_fields x1 f) as (_ & _ & _ & _ & _ & _ & _ & Efr).
    unfold SRC in *. rewrite Efr. destruct (f_from f) as [i|i] eqn:Ef; cbn [from_succ].
    - split; [apply cp1_c; intros i' E; rewrite Ef in E; injection E as <-; apply H; lia|]. intros j Hj. apply H. lia.
    - split; [apply cp1_c; intros i' E; rewrite Ef in E; discriminate E | exact I].
  Qed.

  Lemma SRC_set_op : forall n f v, SRC n f -> SRC n (fset_op f v). Proof. intros n f v H. exact H. Qed.
  Lemma SRC_set_len : forall n f v, SRC n f -> SRC n (fset_len f v). Proof. intros n f v H. exact H. Qed.


  Lemma loopZ_cong_inv : forall {A} (P : A -> Prop) (b1 b2 : A -> bool * A),
    (forall a, P a -> b2 a = b1 a /\ (fst (b1 a) = true -> P (snd (b1 a)))) ->
    forall n a, P a -> loopZ n b2 a = loopZ n b1 a.
  Proof.
    intros A P b1 b2 H n. remember (Z.to_nat n) as m eqn:Em. revert n Em.
    induction m as [|m IH]; intros n Em a Pa.
    - rewrite !loopZ_le0 by lia. reflexivity.
    - rewrite !(loopZ_step n) by lia. destruct (H a Pa) as [E HP]. rewrite E.
      destruct (b1 a) as [c a']. cbn [fst snd] in HP. destruct c; [| reflexivity]. apply IH; [lia | exact (HP eq_refl)].
  Qed.
  Lemma loopZ_inv : forall {A} (P : A -> Prop) (b : A -> bool * A),
    (forall a, P a -> P (snd (b a))) -> forall n a, P a -> P (loopZ n b a).
  Proof.
    intros A P b H n. remember (Z.to_nat n) as m eqn:Em. revert n Em.
    induction m as [|m IH]; intros n Em a Pa.
    - rewrite loopZ_le0 by lia. exact Pa.
    - rewrite (loopZ_step n) by lia. pose proof (H a Pa) as HP. destruct (b a) as [c a']. cbn [snd] in HP.
      destruct c; [apply IH; [lia | exact HP] | exact HP].
  Qed.

  Lemma copy_op_c : forall f, 1 <= f_op f <= 2 ^ 32 -> SRC (f_op f) f -> copy_op x2 f = copy_op x1 f.
  Proof.
    intros f Hop HS. unfold copy_op.
    apply (loopZ_cong_inv (fun g => 1 <= f_op g <= 2 ^ 32 /\ SRC (f_op g) g)); [| exact (conj Hop HS)].
    intros a [Ha Sa]. destruct (SRC_cp1 _ a Sa ltac:(lia)) as [E1 S1].
    pose proof (cp1_fields x1 a) as (_ & _ & _ & _ & _ & _ & Eop & _).
    cbv beta zeta. rewrite E1. facc. rewrite Eop. rewrite wrap32_id by lia.
    split; [reflexivity|]. cbn [fst snd]. intros Hc.
    destruct (Z.eqb_spec (f_op a - 1) 0) as [Z0|Z0]; [discriminate Hc|].
    split; [facc; lia | apply SRC_set_op; facc; exact S1].
  Qed.

  Definition W3 (g : ffs) : Prop := 0 <= f_len g < 2 ^ 32 /\ SRC (f_len g) g.
  Lemma copy_while3_c : forall f, W3 f -> copy_while3 x2 f = copy_while3 x1 f /\ W3 (copy_while3 x1 f).
  Proof.
    intros f Hf. unfold copy_while3.
    assert (STEP : forall a, W3 a ->
      (if 2 <? f_len a then let a' := cp1 x2 (cp1 x2 (cp1 x2 a)) in (true, fset_len a' (wrap32 (f_len a' - 3))) else (false, a))
      = (if 2 <? f_len a then let a' := cp1 x1 (cp1 x1 (cp1 x1 a)) in (true, fset_len a' (wrap32 (f_len a' - 3))) else (false, a))
      /\ W3 (snd (if 2 <? f_len a then let a' := cp1 x1 (cp1 x1 (cp1 x1 a)) in (true, fset_len a' (wrap32 (f_len a' - 3))) else (false, a)))).
    { intros a [Ha Sa]. destruct (Z.ltb_spec 2 (f_len a)) as [L|L]; [| split; [reflexivity | exact (conj Ha Sa)]].
      destruct (SRC_cp1 _ a Sa ltac:(lia)) as [E1 S1]. pose proof (cp1_fields x1 a) as (_ & _ & _ & _ & El1 & _).
      destruct (SRC_cp1 _ (cp1 x1 a) S1 ltac:(lia)) as [E2 S2]. pose proof (cp1_fields x1 (cp1 x1 a)) as (_ & _ & _ & _ & El2 & _).
      destruct (SRC_cp1 _ (cp1 x1 (cp1 x1 a)) S2 ltac:(lia)) as [E3 S3]. pose proof (cp1_fields x1 (cp1 x1 (cp1 x1 a))) as (_ & _ & _ & _ & El3 & _).
      cbv beta zeta. rewrite E1, E2, E3. rewrite El3, El2, El1. rewrite wrap32_id by lia.
      split; [reflexivity|]. cbn [snd]. split; [facc; lia | apply SRC_set_len; facc; eapply SRC_le; [exact S3 | lia]]. }
    split.
    - apply (loopZ_cong_inv W3); [| exact Hf]. intros a Ha. destruct (STEP a Ha) as [E P]. split; [exact E | intros _; exact P].
    - apply (loopZ_inv W3); [| exact Hf]. intros a Ha. exact (proj2 (STEP a Ha)).
  Qed.

  Lemma copy_tail_c : forall f, 0 <= f_len f -> SRC (f_len f) f -> copy_tail x2 f = copy_tail x1 f.
  Proof.
    intros f Hlen HS. unfold copy_tail.
    destruct (Z.eqb_spec (f_len f) 0) as [Z0|Z0]; cbn [negb]; [reflexivity|].
    destruct (SRC_cp1 _ f HS ltac:(lia)) as [E1 HS1]. rewrite E1.
    pose proof (cp1_fields x1 f) as (_ & _ & _ & _ & El1 & _). rewrite El1.
    destruct (Z.ltb_spec 1 (f_len f)) as [L|L]; [| reflexivity].
    destruct (SRC_cp1 _ (cp1 x1 f) HS1 ltac:(lia)) as [E2 _]. exact E2.
  Qed.

  Definition OUTSRC (g : ffs) : Prop := exists i, f_from g = FOut i.
  Lemma f_from_set_len : forall g v, f_from (fset_len g v) = f_from g. Proof. intros g v; destruct g; reflexivity. Qed.
  Lemma cp1_out_c : forall g, OUTSRC g -> cp1 x2 g = cp1 x1 g /\ OUTSRC (cp1 x1 g).
  Proof.
    intros g [i Hg]. split; [apply cp1_c; intros i' E; rewrite Hg in E; discriminate E|].
    pose proof (cp1_fields x1 g) as (_ & _ & _ & _ & _ & _ & _ & Efr). exists (i + 1). rewrite Efr, Hg. reflexivity.
  Qed.
  Lemma copy_do3_c : forall f, OUTSRC f -> copy_do3 x2 f = copy_do3 x1 f /\ OUTSRC (copy_do3 x1 f).
  Proof.
    intros f Hf. unfold copy_do3.
    assert (STEP : forall a, OUTSRC a ->
      (let a' := cp1 x2 (cp1 x2 (cp1 x2 a)) in let a' := fset_len a' (wrap32 (f_len a' - 3)) in (2 <? f_len a', a'))
      = (let a' := cp1 x1 (cp1 x1 (cp1 x1 a)) in let a' := fset_len a' (wrap32 (f_len a' - 3)) in (2 <? f_len a', a'))
      /\ OUTSRC (snd (let a' := cp1 x1 (cp1 x1 (cp1 x1 a)) in let a' := fset_len a' (wrap32 (f_len a' - 3)) in (2 <? f_len a', a')))).
    { intros a Ha. destruct (cp1_out_c a Ha) as [E1 O1]. destruct (cp1_out_c _ O1) as [E2 O2]. destruct (cp1_out_c _ O2) as [E3 O3].
      cbv beta zeta. rewrite E1, E2, E3. split; [reflexivity|]. cbn [snd]. destruct O3 as [i Hi]. exists i. rewrite f_from_set_len. exact Hi. }
    split.
    - apply (loopZ_cong_inv OUTSRC); [| exact Hf]. intros a Ha. destruct (STEP a Ha) as [E P]. split; [exact E | intros _; exact P].
    - apply (loopZ_inv OUTSRC); [| exact Hf]. intros a Ha. exact (proj2 (STEP a Ha)).
  Qed.


  Lemma copy_tail_out_c : forall f, OUTSRC f -> copy_tail x2 f = copy_tail x1 f.
  Proof.
    intros f [i Hi]. unfold copy_tail.
    destruct (negb (f_len f =? 0)); [| reflexivity].
    assert (E1 : cp1 x2 f = cp1 x1 f) by (apply cp1_c; intros i' E; rewrite Hi in E; discriminate E). rewrite E1.
    pose proof (cp1_fields x1 f) as (_ & _ & _ & _ & El1 & _ & _ & Efr). rewrite El1.
    destruct (1 <? f_len f); [| reflexivity].
    apply cp1_c. intros i' E. rewrite Efr, Hi in E. discriminate E.
  Qed.

  Lemma out_copy_c : forall f, out_copy x2 f = out_copy x1 f.
  Proof.
    intros f. unfold out_copy.
    destruct (copy_do3_c (fset_from f (FOut (f_out f - f_dist f))) ltac:(eexists; reflexivity)) as [E O].
    rewrite E. apply copy_tail_out_c. exact O.
  Qed.

  Lemma dist_tailcopy_c : forall f, 0 <= f_len f < 2 ^ 32 -> SRC (f_len f) f -> dist_tailcopy x2 f = dist_tailcopy x1 f.
  Proof.
    intros f Hlen HS. unfold dist_tailcopy.
    destruct (copy_while3_c f (conj Hlen HS)) as [E [Hl HS']]. rewrite E. apply copy_tail_c; [lia | exact HS'].
  Qed.

  Lemma win_place_c : forall f, 1 <= f_op f <= x_whave x1 -> 0 <= f_len f < 2 ^ 32 ->
    win_place x2 f = win_place x1 f
    /\ 0 <= f_len (win_place x1 f) <= f_len f /\ SRC (f_len (win_place x1 f)) (win_place x1 f).
  Proof.
    intros f Hop Hlen.
    assert (Hnz : x_wsize x1 <> 0) by (intros Z0; destruct (Xz Z0); lia).
    destruct (Xnz Hnz) as [Hwn Hwh].
    assert (CPW : forall g i, f_from g = FWin i -> 1 <= f_op g <= 2 ^ 32 -> 0 <= i -> i + f_op g <= x_whave x1 ->
              copy_op x2 g = copy_op x1 g).
    { intros g i Hg Hog Hi Hiw. apply copy_op_c; [exact Hog|]. unfold SRC. rewrite Hg. intros j Hj. apply EW. lia. }
    assert (KL : forall g, 1 <= f_op g < 2 ^ 32 -> f_len (copy_op x1 g) = f_len g /\ f_dist (copy_op x1 g) = f_dist g).
    { intros g Hg. rewrite copy_op_cpn by exact Hg. facc.
      destruct (cpn_keep x1 (Z.to_nat (f_op g)) g) as (_ & _ & _ & K4 & K5 & _). rewrite K4, K5. split; reflexivity. }
    unfold win_place. rewrite EXwn, EXws.
    destruct (Z.eqb_spec (x_wnext x1) 0) as [W0|W0].
    -
      assert (Hfull : x_whave x1 = x_wsize x1)
        by (destruct (Z_lt_le_dec (x_whave x1) (x_wsize x1)); [pose proof (Xfill Hnz ltac:(lia)); lia | lia]).
      facc. destruct (Z.ltb_spec (f_op f) (f_len f)) as [C|C].
      + rewrite (wrap32_id (f_len f - f_op f)) by lia.
        set (f1 := fset_len (fset_from f (FWin (x_wsize x1 - f_op f))) (f_len f - f_op f)).
        rewrite (CPW f1 (x_wsize x1 - f_op f)) by (subst f1; facc; first [reflexivity | lia]).
        split; [reflexivity|]. facc.
        destruct (KL f1 ltac:(subst f1; facc; lia)) as [K4 K5]. rewrite K4. subst f1. facc.
        split; [lia|]. unfold SRC. facc. exact I.
      + split; [reflexivity|]. facc. split; [lia|]. unfold SRC. facc. intros j Hj. apply EW. lia.
    - destruct (Z.ltb_spec (x_wnext x1) (f_op f)) as [C1|C1].
      +
        assert (Hfull : x_whave x1 = x_wsize x1)
          by (destruct (Z_lt_le_dec (x_whave x1) (x_wsize x1)); [pose proof (Xfill Hnz ltac:(lia)); lia | lia]).
        facc. rewrite (wrap32_id (f_op f - x_wnext x1)) by lia.
        destruct (Z.ltb_spec (f_op f - x_wnext x1) (f_len f)) as [C2|C2].
        * rewrite (wrap32_id (f_len f - (f_op f - x_wnext x1))) by lia.
          set (f1 := fset_len (fset_op (fset_from f (FWin (x_wsize x1 + x_wnext x1 - f_op f))) (f_op f - x_wnext x1)) (f_len f - (f_op f - x_wnext x1))).
          rewrite (CPW f1 (x_wsize x1 + x_wnext x1 - f_op f)) by (subst f1; facc; first [reflexivity | lia]).
          destruct (KL f1 ltac:(subst f1; facc; lia)) as [K4 K5].
          set (f2 := copy_op x1 f1) in *. facc. rewrite ?K4, ?K5.
          replace (f_len f1) with (f_len f - (f_op f - x_wnext x1)) by reflexivity.
          destruct (Z.ltb_spec (x_wnext x1) (f_len f - (f_op f - x_wnext x1))) as [C3|C3].
          -- rewrite (wrap32_id (f_len f - (f_op f - x_wnext x1) - x_wnext x1)) by lia.
             set (f3 := fset_len (fset_op (fset_from f2 (FWin 0)) (x_wnext x1)) (f_len f - (f_op f - x_wnext x1) - x_wnext x1)).
             rewrite (CPW f3 0) by (subst f3; facc; first [reflexivity | lia]).
             split; [reflexivity|]. facc.
             destruct (KL f3 ltac:(subst f3; facc; lia)) as [K4' K5']. rewrite K4'. subst f3. facc.
             split; [lia|]. unfold SRC. facc. exact I.
          -- split; [reflexivity|]. facc. rewrite K4. subst f1. facc. split; [lia|].
             unfold SRC. facc. intros j Hj. apply EW. lia.
        * split; [reflexivity|]. facc. split; [lia|]. unfold SRC. facc. intros j Hj. apply EW. lia.
      +
        assert (Hwnh : x_wnext x1 <= x_whave x1)
          by (destruct (Z_lt_le_dec (x_whave x1) (x_wsize x1)); [pose proof (Xfill Hnz ltac:(lia)); lia | lia]).
        facc. destruct (Z.ltb_spec (f_op f) (f_len f)) as [C|C].
        * rewrite (wrap32_id (f_len f - f_op f)) by lia.
          set (f1 := fset_len (fset_from f (FWin (x_wnext x1 - f_op f))) (f_len f - f_op f)).
          rewrite (CPW f1 (x_wnext x1 - f_op f)) by (subst f1; facc; first [reflexivity | lia]).
          split; [reflexivity|]. facc.
          destruct (KL f1 ltac:(subst f1; facc; lia)) as [K4 K5]. rewrite K4. subst f1. facc.
          split; [lia|]. unfold SRC. facc. exact I.
        * split; [reflexivity|]. facc. split; [lia|]. unfold SRC. facc. intros j Hj. apply EW. lia.
  Qed.


  Lemma fdrop_fields : forall f c,
    f_in (fdrop f c) = f_in f /\ f_out (fdrop f c) = f_out f /\ f_len (fdrop f c) = f_len f /\ f_dist (fdrop f c) = f_dist f
    /\ f_op (fdrop f c) = f_op f /\ f_from (fdrop f c) = f_from f /\ f_ob (fdrop f c) = f_ob f.
  Proof. intros f c. unfold fdrop. destruct f; cbn. repeat split; reflexivity. Qed.
  Lemma fpull_fields : forall x f,
    f_out (fpull x f) = f_out f /\ f_len (fpull x f) = f_len f /\ f_dist (fpull x f) = f_dist f
    /\ f_op (fpull x f) = f_op f /\ f_from (fpull x f) = f_from f /\ f_ob (fpull x f) = f_ob f.
  Proof. intros x f. unfold fpull. destruct f; cbn. repeat split; reflexivity. Qed.

  Lemma dist_refill_len : forall f op,
    f_len (if f_bits f <? op then let f1 := fpull x1 f in if f_bits f1 <? op then fpull x1 f1 else f1 else f) = f_len f.
  Proof.
    intros f op. destruct (f_bits f <? op); [| reflexivity]. cbv zeta.
    pose proof (fpull_fields x1 f) as (_ & L1 & _). destruct (f_bits (fpull x1 f) <? op); [| exact L1].
    pose proof (fpull_fields x1 (fpull x1 f)) as (_ & L2 & _). rewrite L2. exact L1.
  Qed.

  Lemma len_extra_c : forall op f, len_extra x2 op f = len_extra x1 op f.
  Proof. intros op f. unfold len_extra. rewrite !fpull_c. reflexivity. Qed.

  Lemma len_extra_len : forall op f, 0 <= f_len f < 2 ^ 32 -> 0 <= f_len (len_extra x1 op f) < 2 ^ 32.
  Proof.
    intros op f H. unfold len_extra. destruct (negb (op =? 0)); [| exact H]. cbv zeta.
    pose proof (fdrop_fields (fset_len (if f_bits f <? op then fpull x1 f else f)
                 (wrap32 (f_len (if f_bits f <? op then fpull x1 f else f) + Z.land (wrap32 (f_hold (if f_bits f <? op then fpull x1 f else f))) (zmask op)))) op) as (_ & _ & L & _).
    rewrite L. facc. apply wrap32_range'.
  Qed.

  Lemma fpull2_if_len : forall f, f_len (fpull2_if x1 f) = f_len f.
  Proof.
    intros f. unfold fpull2_if. destruct (f_bits f <? 15); [| reflexivity].
    pose proof (fpull_fields x1 f) as (_ & L1 & _). pose proof (fpull_fields x1 (fpull x1 f)) as (_ & L2 & _). rewrite L2. exact L1.
  Qed.

  Lemma refill2_len : forall (c1 c2 : bool) fd,
    f_len (if c1 then if c2 then fpull x1 (fpull x1 fd) else fpull x1 fd else fd) = f_len fd.
  Proof.
    intros c1 c2 fd. destruct c1; [| reflexivity].
    pose proof (fpull_fields x1 fd) as (_ & L1 & _). pose proof (fpull_fields x1 (fpull x1 fd)) as (_ & L2 & _).
    destruct c2; [rewrite L2|]; exact L1.
  Qed.

  Lemma dist_base_c : forall F, 0 <= f_len F < 2 ^ 32 -> 0 <= f_dist F < 2 ^ 32 ->
    (if wrap32 (f_out F - x_beg x1) <? f_dist F
     then if (x_whave x1 <? wrap32 (f_dist F - wrap32 (f_out F - x_beg x1))) && negb (x_sane x1 =? 0)
          then FBreak (fset_op F (wrap32 (f_dist F - wrap32 (f_out F - x_beg x1)))) BAD (Some MSG_invalid_distance_too_far_back)
          else FCont (dist_tailcopy x2 (win_place x2 (fset_op F (wrap32 (f_dist F - wrap32 (f_out F - x_beg x1))))))
     else FCont (out_copy x2 F))
    = (if wrap32 (f_out F - x_beg x1) <? f_dist F
       then if (x_whave x1 <? wrap32 (f_dist F - wrap32 (f_out F - x_beg x1))) && negb (x_sane x1 =? 0)
            then FBreak (fset_op F (wrap32 (f_dist F - wrap32 (f_out F - x_beg x1)))) BAD (Some MSG_invalid_distance_too_far_back)
            else FCont (dist_tailcopy x1 (win_place x1 (fset_op F (wrap32 (f_dist F - wrap32 (f_out F - x_beg x1))))))
       else FCont (out_copy x1 F)).
  Proof.
    intros F Hlen Hdist.
    pose proof (wrap32_range' (f_out F - x_beg x1)) as Rz. set (z := wrap32 (f_out F - x_beg x1)) in *. clearbody z.
    destruct (Z.ltb_spec z (f_dist F)) as [C|C]; [| rewrite out_copy_c; reflexivity].
    rewrite (wrap32_id (f_dist F - z)) by lia.
    rewrite Xsane. change (negb (1 =? 0)) with true. rewrite andb_true_r.
    destruct (Z.ltb_spec (x_whave x1) (f_dist F - z)) as [D|D]; [reflexivity|]. f_equal.
    set (G := fset_op F (f_dist F - z)).
    destruct (win_place_c G ltac:(subst G; facc; lia) ltac:(subst G; facc; exact Hlen)) as [E [L S]].
    rewrite E. apply dist_tailcopy_c; [| exact S]. subst G. facc. cbn [f_len fset_op] in L. lia.
  Qed.

  Lemma dodist_c : forall k here i f,
    okD i -> here = code_at s1 (is_distcode s1) i -> 0 <= f_len f < 2 ^ 32 ->
    dodist k x2 s2 here f = dodist k x1 s1 here f.
  Proof.
    induction k as [|k IH]; intros here i f Hi Eh Hlen; [reflexivity|].
    rewrite !dodist_S. cbv zeta. rewrite ED, EXbeg, EXwh, EXsane, !fpull_c.
    destruct (negb (Z.land (code_op here) 16 =? 0)) eqn:B16.
    -
      match goal with |- context [out_copy x2 ?F] => apply (dist_base_c F) end.
      + cbn [f_len fdrop fset_dist fset_bits fset_hold]. rewrite refill2_len. cbn [f_len fset_dist fdrop fset_bits fset_hold]. exact Hlen.
      + cbn [f_dist fdrop fset_dist fset_bits fset_hold]. apply wrap32_range'.
    - destruct (Z.land (code_op here) 64 =? 0) eqn:B64; [| reflexivity].
      apply Bool.negb_false_iff in B16. apply Z.eqb_eq in B16. apply Z.eqb_eq in B64.
      assert (Hi' : okD (code_val here + Z.land (f_hold (fdrop f (code_bits here))) (zmask (code_op here)))).
      { rewrite Eh. apply (HD2 i); [exact Hi | rewrite <- Eh; exact B16 | rewrite <- Eh; exact B64]. }
      rewrite (HD0 _ Hi'). apply (IH _ _ _ Hi' eq_refl).
      pose proof (fdrop_fields f (code_bits here)) as (_ & _ & L & _). rewrite L. exact Hlen.
  Qed.

  Lemma len_base_c : forall F, 0 <= f_len F < 2 ^ 32 ->
    dodist 4 x2 s2 (code_at s2 (is_distcode s1) (Z.land (f_hold F) (x_dmask x1))) F
    = dodist 4 x1 s1 (code_at s1 (is_distcode s1) (Z.land (f_hold F) (x_dmask x1))) F.
  Proof.
    intros F Hlen. rewrite (HD0 _ (HD1 (f_hold F))). apply (dodist_c 4 _ (Z.land (f_hold F) (x_dmask x1))); [apply HD1 | reflexivity | exact Hlen].
  Qed.

  Lemma dolen_c : forall k here i f,
    okL i -> here = code_at s1 (is_lencode s1) i ->
    dolen k x2 s2 here f = dolen k x1 s1 here f.
  Proof.
    induction k as [|k IH]; intros here i f Hi Eh; [reflexivity|].
    rewrite !dolen_S. cbv zeta. rewrite EL, ED, EXdm, !len_extra_c, !fpull2_if_c.
    destruct (code_op here =? 0) eqn:B0; [reflexivity|].
    destruct (negb (Z.land (code_op here) 16 =? 0)) eqn:B16.
    - apply len_base_c. rewrite fpull2_if_len. apply len_extra_len. facc. apply (conj (proj1 (code_val_range here))). pose proof (code_val_range here). lia.
    - destruct (Z.land (code_op here) 64 =? 0) eqn:B64; [| reflexivity].
      apply Z.eqb_neq in B0. apply Bool.negb_false_iff in B16. apply Z.eqb_eq in B16. apply Z.eqb_eq in B64.
      assert (Hi' : okL (code_val here + Z.land (f_hold (fdrop f (code_bits here))) (zmask (code_op here)))).
      { rewrite Eh. apply (HL2 i); [exact Hi | rewrite <- Eh; exact B0 | rewrite <- Eh; exact B16 | rewrite <- Eh; exact B64]. }
      rewrite (HL0 _ Hi'). exact (IH _ _ _ Hi' eq_refl).
  Qed.

  Theorem fast_trip_c : forall f, fast_trip x2 s2 f = fast_trip x1 s1 f.
  Proof.
    intros f. unfold fast_trip. rewrite fpull2_if_c, EL, EXlm.
    rewrite (HL0 _ (HL1 _)). exact (dolen_c 4 _ _ _ (HL1 _) eq_refl).
  Qed.
End FastCong.


Definition ffxo (s : inflate_state) (c : icall) (r : iregs) : ffx :=
  mkFX (ic_input c) (ic_next_in c + wrap32 (ic_avail_in c - 5))
       (ic_next_out c - wrap32 (ir_out r - ic_avail_out c))
       (ic_next_out c + wrap32 (ic_avail_out c - 257))
       (is_wsize s) (is_whave s) (is_wnext s) (is_window s)
       (zmask (is_lenbits s)) (zmask (is_distbits s)) (is_sane s).
Definition ff0o (s : inflate_state) (c : icall) : ffs :=
  mkF (ic_next_in c) (ic_next_out c) (is_hold s) (is_bits s) 0 0 0 (FOut 0) (ic_outbuf c).
Definition ff_stepo (x : ffx) (s : inflate_state) (f : ffs) : ffs + (ffs * option (Z * option Z)) :=
  match fast_trip x s f with
  | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', None)
  | FBreak f' mode msg => inr (f', Some (mode, msg))
  end.
Definition ff_loopo (s : inflate_state) (c : icall) (r : iregs) : ffs * option (Z * option Z) :=
  iterZ (8 * ic_avail_in c + ic_avail_out c + 80) (ff_stepo (ffxo s c r) s) (fun f => (f, None)) (ff0o s c).
Definition ff_fino (f : ffs) : ffs :=
  let len := Z.shiftr (f_bits f) 3 in
  let f := fset_in f (f_in f - len) in
  let f := fset_bits f (wrap32 (f_bits f - Z.shiftl len 3)) in
  fset_hold f (Z.land (f_hold f) (zmask (f_bits f))).
Definition ff_posto (s : inflate_state) (c : icall) (r : iregs) (x : ffx) (f : ffs) (mm : option (Z * option Z)) : iw :=
  let c := icset_outbuf c (f_ob f) in
  let c := icset_next_in c (f_in f) in
  let c := icset_next_out c (f_out f) in
  let c := icset_avail_in c (wrap32 (if f_in f <? x_last x then 5 + (x_last x - f_in f) else 5 - (f_in f - x_last x))) in
  let c := icset_avail_out c (wrap32 (if f_out f <? x_end x then 257 + (x_end x - f_out f) else 257 - (f_out f - x_end x))) in
  let s := iset_hold s (f_hold f) in
  let s := iset_bits s (f_bits f) in
  let '(s, c) := match mm with
                 | Some (mode, Some msg) => (iset_mode s mode, icset_msg c msg)
                 | Some (mode, None) => (iset_mode s mode, c)
                 | None => (s, c)
                 end in
  mkW s c r.

Lemma inflate_fast_eqo : forall s c r,
  inflate_fast (mkW s c r) = let '(f, mm) := ff_loopo s c r in ff_posto s c r (ffxo s c r) (ff_fino f) mm.
Proof. intros. reflexivity. Qed.


Lemma land64_96 : Z.land 96 64 <> 0. Proof. discriminate. Qed.
Lemma land64_203 : Z.land 203 64 <> 0. Proof. discriminate. Qed.
Lemma land64_77 : Z.land 77 64 <> 0. Proof. discriminate. Qed.

Lemma okT_lens : forall s1 s2,
  tbl_eq (is_codes s1) (is_codes s2) LENS (is_lencode s1) (is_lenbits s1) ->
  exists okL : Z -> Prop,
    (forall i, okL i -> code_at s2 (is_lencode s1) i = code_at s1 (is_lencode s1) i)
    /\ (forall h, okL (Z.land h (zmask (is_lenbits s1))))
    /\ (forall i h, okL i -> let e := code_at s1 (is_lencode s1) i in
          code_op e <> 0 -> Z.land (code_op e) 16 = 0 -> Z.land (code_op e) 64 = 0 ->
          okL (code_val e + Z.land h (zmask (code_op e)))).
Proof.
  intros s1 s2. destruct (is_lencode s1) as [o| |]; cbn [tbl_eq code_at]; intros T.
  - destruct T as [used [HT HA]]. exists (fun i => 0 <= i < used).
    pose proof (T_root _ _ _ _ HT) as HR. pose proof (T_used _ _ _ _ HT) as HU.
    split; [intros i Hi; apply HA; lia|]. split.
    + intros h. pose proof (land_zmask_range h (is_lenbits s1) ltac:(lia)). lia.
    + intros i h Hi. cbv zeta. intros B0 B16 B64.
      destruct (T_shape _ _ _ _ HT i Hi) as [[(sy & len & Hsy & Hlen & Hop & Hval & _)|[(Hx & Hb & Hop & Hv1 & Hv2)|(Hop & _)]]|[Hop _]].
      * exfalso. pose proof (lens_sym_cases sy Hsy) as SC. destruct (sym_entry LENS sy) as [op v]. cbn [fst snd] in Hop, Hval.
        rewrite Hop in B0, B16, B64. clear Hop Hval.
        destruct SC as [[O1 _]|[[O1 _]|[(O1 & _)|[O1|O1]]]].
        -- exact (B0 O1).
        -- rewrite O1 in B64. exact (land64_96 B64).
        -- destruct (len_op_facts _ O1) as (_ & _ & _ & F4 & _). exact (F4 B16).
        -- rewrite O1 in B64. exact (land64_203 B64).
        -- rewrite O1 in B64. exact (land64_77 B64).
      * pose proof (land_zmask_range h (code_op (arr_get (is_codes s1) (o + i))) ltac:(lia)). lia.
      * exfalso. rewrite Hop in B64. discriminate B64.
      * exfalso. rewrite Hop in B64. discriminate B64.
  - exists (fun _ => True). repeat split; intros; exact I || reflexivity.
  - exists (fun _ => True). repeat split; intros; exact I || reflexivity.
Qed.

Lemma okT_dists : forall s1 s2,
  tbl_eq (is_codes s1) (is_codes s2) DISTS (is_distcode s1) (is_distbits s1) ->
  exists okD : Z -> Prop,
    (forall i, okD i -> code_at s2 (is_distcode s1) i = code_at s1 (is_distcode s1) i)
    /\ (forall h, okD (Z.land h (zmask (is_distbits s1))))
    /\ (forall i h, okD i -> let e := code_at s1 (is_distcode s1) i in
          Z.land (code_op e) 16 = 0 -> Z.land (code_op e) 64 = 0 ->
          okD (code_val e + Z.land h (zmask (code_op e)))).
Proof.
  intros s1 s2. destruct (is_distcode s1) as [o| |]; cbn [tbl_eq code_at]; intros T.
  - destruct T as [used [HT HA]]. exists (fun i => 0 <= i < used).
    pose proof (T_root _ _ _ _ HT) as HR. pose proof (T_used _ _ _ _ HT) as HU.
    split; [intros i Hi; apply HA; lia|]. split.
    + intros h. pose proof (land_zmask_range h (is_distbits s1) ltac:(lia)). lia.
    + intros i h Hi. cbv zeta. intros B16 B64.
      destruct (T_shape _ _ _ _ HT i Hi) as [[(sy & len & Hsy & Hlen & Hop & Hval & _)|[(Hx & Hb & Hop & Hv1 & Hv2)|(Hop & _)]]|[Hop _]].
      * exfalso. pose proof (dists_sym_cases sy Hsy) as SC. destruct (sym_entry DISTS sy) as [op v]. cbn [fst snd] in Hop, Hval.
        rewrite Hop in B16, B64. clear Hop Hval.
        destruct SC as [(O1 & _)|[O1 _]]; [destruct (dist_op_facts _ O1) as (_ & _ & _ & F4); exact (F4 B16) | rewrite O1 in B64; discriminate B64].
      * pose proof (land_zmask_range h (code_op (arr_get (is_codes s1) (o + i))) ltac:(lia)). lia.
      * exfalso. rewrite Hop in B64. discriminate B64.
      * exfalso. rewrite Hop in B64. discriminate B64.
  - exists (fun _ => True). repeat split; intros; exact I || reflexivity.
  - exists (fun _ => True). repeat split; intros; exact I || reflexivity.
Qed.


Section Inst.
  Variable s1 : inflate_state.
Variable s2 : inflate_state.
Variable c : icall.
Variable r : iregs.
  Hypothesis HC : CORE s1.
  Hypothesis E : is_mode s1 = LEN.
  Hypothesis HQ : IEQ s1 s2.

  Lemma fast_trip_inst : forall f, fast_trip (ffxo s2 c r) s2 f = fast_trip (ffxo s1 c r) s1 f.
  Proof.
    intros f. pose proof HQ as HQ0. ieq_open HQ E.
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
    destruct (okT_lens s1 s2 QtblL) as [okL (HL0 & HL1 & HL2)].
    destruct (okT_dists s1 s2 QtblD) as [okD (HD0 & HD1 & HD2)].
    assert (Xws : 0 <= is_wsize s1 < 2 ^ 32).
    { destruct (Z.eq_dec (is_wsize s1) 0) as [Z0|Z0]; [lia|]. rewrite (C3 Z0). unfold shl32. apply wrap32_range'. }
    refine (fast_trip_c (ffxo s1 c r) (ffxo s2 c r) s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ okL okD _ _ _ _ _ _ f);
      cbn [x_input x_beg x_wsize x_whave x_wnext x_lmask x_dmask x_sane x_window ffxo]; unfold W; cbn [x_window ffxo];
      try assumption; try reflexivity.
    - rewrite Qlenbits. reflexivity.
    - rewrite Qdistbits. reflexivity.
  Qed.

  Lemma ff_loop_inst : ff_loopo s2 c r = ff_loopo s1 c r.
  Proof.
    unfold ff_loopo.
    replace (ff0o s2 c) with (ff0o s1 c).
    2:{ pose proof HQ as HQ0. ieq_open HQ0 E. unfold ff0o. rewrite Qhold, Qbits. reflexivity. }
    replace (ff_stepo (ffxo s2 c r) s2) with (ff_stepo (ffxo s1 c r) s1); [reflexivity|].
    extensionality f. unfold ff_stepo. rewrite fast_trip_inst. cbn [x_last x_end ffxo]. reflexivity.
  Qed.
End Inst.


Definition mode_ok (st : fstep) : Prop := match st with FCont _ => True | FBreak _ m _ => m = TYPE \/ m = BAD end.

Lemma dodist_mode : forall k x s here f, mode_ok (dodist k x s here f).
Proof.
  induction k as [|k IH]; intros x s here f; [exact I|]. rewrite dodist_S. cbv zeta.
  destruct (negb _); [| destruct (_ =? 0); [apply IH | right; reflexivity]].
  destruct (_ <? _); [| exact I]. destruct (_ && _); [right; reflexivity | exact I].
Qed.
Lemma dolen_mode : forall k x s here f, mode_ok (dolen k x s here f).
Proof.
  induction k as [|k IH]; intros x s here f; [exact I|]. rewrite dolen_S. cbv zeta.
  destruct (_ =? 0); [exact I|]. destruct (negb _); [apply dodist_mode|].
  destruct (_ =? 0); [apply IH|]. destruct (negb _); [left | right]; reflexivity.
Qed.
Lemma ff_loopo_mode : forall s c r, match snd (ff_loopo s c r) with Some (m, _) => m = TYPE \/ m = BAD | None => True end.
Proof.
  intros s c r. unfold ff_loopo.
  set (n := 8 * ic_avail_in c + ic_avail_out c + 80). clearbody n. set (f := ff0o s c). clearbody f.
  remember (Z.to_nat n) as m eqn:Em. revert n Em f.
  induction m as [|m IH]; intros n Em f.
  - rewrite iterZ_le0 by lia. exact I.
  - rewrite iterZ_step by lia. unfold ff_stepo at 1.
    pose proof (dolen_mode 4 (ffxo s c r) s (code_at s (is_lencode s) (Z.land (f_hold (fpull2_if (ffxo s c r) f)) (x_lmask (ffxo s c r)))) (fpull2_if (ffxo s c r) f)) as M.
    unfold fast_trip. destruct (dolen 4 _ s _ _) as [f'|f' mode msg]; cbn [mode_ok] in M.
    + destruct (_ && _); [apply IH; lia | exact I].
    + exact M.
Qed.


Theorem fastc_proof : FASTC.
Proof.
  intros s1 s2 c r HC E HQ HU Hh Hl. unfold amodify. cbn [RES2]. split; [reflexivity|].
  notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E.
  pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
  unfold RESTORE. cbn [w_s w_c w_r].
  set (cR := icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)).
  set (sR1 := iset_bits (iset_hold s1 (ir_hold r)) (ir_bits r)).
  set (sR2 := iset_bits (iset_hold s2 (ir_hold r)) (ir_bits r)).
  assert (ER : is_mode sR1 = LEN) by (subst sR1; sacc; exact E).
  assert (HQR : IEQ sR1 sR2) by (subst sR1 sR2; ieq_close E).
  assert (HCR : CORE sR1).
  { apply (CORE_keep s1); [exact HC | subst sR1; sacc; reflexivity .. | subst sR1; sacc; exact C14]. }
  rewrite !inflate_fast_eqo. rewrite (ff_loop_inst sR1 sR2 cR r HCR ER HQR).
  pose proof (ff_loopo_mode sR1 cR r) as HM.
  destruct (ff_loopo sR1 cR r) as [f mm]. cbn [snd] in HM.
  unfold ff_posto, LOAD. cbv zeta.
  destruct mm as [[mode [msg|]]|].
  - destruct HM as [-> | ->]; subst sR1 sR2 cR; cbn [w_s w_c w_r]; unfold wset_r; cbn [w_s w_c w_r]; sacc;
      (apply WMID_mk; [ieq_close E | uw0 W5 F0]).
  - destruct HM as [-> | ->]; subst sR1 sR2 cR; cbn [w_s w_c w_r]; unfold wset_r; cbn [w_s w_c w_r]; sacc;
      (apply WMID_mk; [ieq_close E | uw0 W5 F0]).
  - subst sR1 sR2 cR; cbn [w_s w_c w_r]; unfold wset_r; cbn [w_s w_c w_r]; sacc.
    apply WMID_mk; [ieq_close E | uw0 W5 F0].
Qed.
End RefInflateEqF.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section Dispatch.
  Variable flush : Z.
  Hypothesis fastc : FASTC.

  Theorem dispatch_cong : forall s1 s2 c r,
    WINV (mkW s1 c r) -> IEQ s1 s2 -> UW s1 c r ->
    RES2 (dispatch ivar_ref flush (mkW s1 c r)) (dispatch ivar_ref flush (mkW s2 c r)).
  Proof.
    intros s1 s2 c r HW HQ HU. pose proof HW as HW0. unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (HC & HR & HMF & HWF & HWB).
    unfold dispatch. rstep gs_eq. cbv zeta. destruct HQ as [[Qm Qrest1] Qrest2]. rewrite Qm.
    assert (HQ : IEQ s1 s2) by (split; [split; [exact Qm|exact Qrest1]|exact Qrest2]). clear Qrest1 Qrest2.
    Ltac tryc lem ftac := lazymatch goal with |- RES2 ((if is_mode ?s =? ?M then _ else _) _) _ =>
      destruct (Z.eqb_spec (is_mode s) M) as [E|?NE]; [apply lem; [ftac | exact E | assumption | assumption] |] end.
    tryc (arm_HEAD_cong ivar_ref) ltac:(exact I).
    tryc (arm_gz_cong FLAGS FTrue arm_FLAGS eq_refl) ltac:(exact I).
    tryc (arm_gz_cong TIME FTrue arm_TIME eq_refl) ltac:(exact I).
    tryc (arm_gz_cong OS FTrue arm_OS eq_refl) ltac:(exact I).
    tryc (arm_gz_cong EXLEN FTrue arm_EXLEN eq_refl) ltac:(exact I).
    tryc (arm_gz_cong EXTRA FTrue arm_EXTRA eq_refl) ltac:(exact I).
    tryc (arm_gz_cong NAME FTrue arm_NAME eq_refl) ltac:(exact I).
    tryc (arm_gz_cong COMMENT FTrue arm_COMMENT eq_refl) ltac:(exact I).
    tryc (arm_gz_cong HCRC FTrue arm_HCRC eq_refl) ltac:(exact I).
    tryc (arm_DICTID_cong ivar_ref flush) ltac:(exact I).
    tryc (arm_DICT_cong ivar_ref flush) ltac:(exact I).
    tryc (arm_TYPE_cong ivar_ref flush) ltac:(exact I).
    tryc (arm_TYPEDO_cong ivar_ref flush TYPEDO (or_intror eq_refl)) ltac:(exact I).
    tryc (arm_STORED_cong ivar_ref flush) ltac:(exact I).
    tryc (arm_COPY__cong) ltac:(exact I).
    tryc (arm_COPY_cong) ltac:(exact I).
    tryc (arm_TABLE_cong flush fastc) ltac:(exact HW0).
    tryc (arm_LENLENS_cong flush fastc) ltac:(rewrite E in HMF, HWF; mred_in HMF; mred_in HWF; destruct HMF as (HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs); unfold LL; repeat (split; [first [assumption | lia]|]); exact HWB).
    tryc (arm_CODELENS_cong flush fastc) ltac:(rewrite E in HMF, HWF; mred_in HMF; mred_in HWF; destruct HMF as (HCm & Hbx & Hnl & Hnd & Hh & HLs & HT); unfold CL; repeat (split; [first [assumption | lia]|]); exact HWB).
    tryc (arm_LEN__cong fastc) ltac:(exact HC).
    tryc (arm_LEN_cong fastc) ltac:(exact HC).
    tryc (arm_LENEXT_cong) ltac:(exact HC).
    tryc (arm_DIST_cong) ltac:(exact HC).
    tryc (arm_DISTEXT_cong) ltac:(exact HC).
    tryc (arm_MATCH_cong) ltac:(exact HC).
    tryc (arm_LIT_cong) ltac:(exact I).
    tryc (arm_CHECK_cong) ltac:(exact I).
    tryc (arm_LENGTH_cong LENGTH FTrue ltac:(discriminate) ltac:(discriminate)) ltac:(exact I).
    tryc (arm_DONE_cong DONE FTrue) ltac:(exact I).
    tryc (arm_BAD_cong FTrue) ltac:(exact I).
    tryc (arm_MEM_cong FTrue) ltac:(exact I).
    destruct (Z.eqb_spec (is_mode s1) SYNC) as [E|NE'].
    - apply (arm_SYNC_cong FTrue); [exact I | exact E | exact HQ | exact HU].
    - exfalso. unfold MF in HMF.
      repeat match goal with N : is_mode s1 <> ?K |- _ => rewrite (proj2 (Z.eqb_neq _ _) N) in HMF; clear N end.
      cbn [orb] in HMF. exact HMF.
  Qed.
End Dispatch.


Section Loop.
  Variable flush : Z.
  Hypothesis fastc : FASTC.

  Lemma WMID_c : forall w1 w2, WMID w1 w2 -> w_c w2 = w_c w1.
  Proof. intros w1 w2 (Ec & _). exact Ec. Qed.

  Lemma iter_cong : forall m w1 w2, WINV w1 -> WMID w1 w2 ->
    let '(st1, w1') := iterZ (Z.of_nat m) (lstep flush) (fun w0 => (SLeave, w0)) w1 in
    let '(st2, w2') := iterZ (Z.of_nat m) (lstep flush) (fun w0 => (SLeave, w0)) w2 in
    st2 = st1 /\ WMID w1' w2'.
  Proof.
    induction m as [|m IH]; intros w1 w2 HW HM.
    - cbn [Z.of_nat]. rewrite !iterZ_le0 by lia. split; [reflexivity|exact HM].
    - rewrite !iterZ_step by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
      destruct w1 as [s1 c r]. destruct w2 as [s2 c2 r2]. destruct HM as (Ec & Er & HQ & HU). cbn [w_s w_c w_r] in Ec, Er, HQ, HU. subst c2 r2.
      pose proof (dispatch_safe flush (mkW s1 c r) s1 c r HW ltac:(lia)) as D.
      pose proof (dispatch_cong flush fastc s1 s2 c r HW HQ HU) as R.
      unfold lstep at 1 3.
      destruct (dispatch ivar_ref flush (mkW s1 c r)) as [u w1'|w1'|rc w1'];
        destruct (dispatch ivar_ref flush (mkW s2 c r)) as [u2 w2'|w2'|rc2 w2']; cbn [RES2] in R; try contradiction.
      + destruct R as [-> R]. destruct D as [HW' _]. apply IH; [exact HW'|exact R].
      + split; [reflexivity|exact R].
      + destruct R as [-> R]. split; [reflexivity|exact R].
  Qed.

  Theorem inf_loop_cong : forall w1 w2, WINV w1 -> WMID w1 w2 ->
    let '(st1, w1') := inf_loop ivar_ref flush w1 in
    let '(st2, w2') := inf_loop ivar_ref flush w2 in
    st2 = st1 /\ WMID w1' w2'.
  Proof.
    intros w1 w2 HW HM. unfold inf_loop. change (fun w0 : iw => _) with (lstep flush) at 1.
    change (fun w0 : iw => match dispatch ivar_ref flush w0 with ARun _ w' => inl w' | ALeave w' => inr (SLeave, w') | ARet rc w' => inr (SRet rc, w') end) with (lstep flush).
    rewrite (WMID_c _ _ HM).
    set (n := 64 * (ic_avail_in (w_c w1) + ic_avail_out (w_c w1) + 64)).
    destruct (Z_lt_le_dec n 0) as [Hn|Hn].
    - rewrite !iterZ_le0 by lia. split; [reflexivity|exact HM].
    - rewrite <- (Z2Nat.id n) by lia. apply iter_cong; [exact HW|exact HM].
  Qed.
End Loop.


Lemma blit_agree : forall (w1 w2 src : arr) dofs sofs n j,
  arr_len w2 = arr_len w1 ->
  (arr_get w2 j = arr_get w1 j \/ (dofs <= j < dofs + n /\ 0 <= j < arr_len w1)) ->
  arr_get (arr_blit w2 dofs src sofs n) j = arr_get (arr_blit w1 dofs src sofs n) j.
Proof.
  intros w1 w2 src dofs sofs n j HL H. rewrite !arr_get_blit. unfold arr_inb. rewrite HL.
  destruct H as [H|[H1 H2]].
  - destruct ((dofs <=? j) && (j <? dofs + Z.max 0 n) && ((0 <=? j) && (j <? arr_len w1))); [reflexivity|exact H].
  - replace ((dofs <=? j) && (j <? dofs + Z.max 0 n) && ((0 <=? j) && (j <? arr_len w1))) with true; [reflexivity|].
    symmetry. rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia.
Qed.

Ltac ieq_facts HQ :=
  let HQ' := fresh "XQ" in pose proof HQ as HQ';
  unfold IEQ in HQ'; cbv zeta in HQ';
  destruct HQ' as ((Xmode & Xlast & Xwrap & Xhavedict & Xflags & Xdmax & Xtotal & Xhead & Xwbits & Xwsize & Xwhave & Xwnext
                    & Xwblk & Xhold & Xbits & Xlencode & Xdistcode & Xnext & Xsane & Xback & Xself & XLwin & XLlens & XLwork & XLcodes)
                   & Xcheck & Xlength & Xoffset & Xextra & Xlenbits & Xdistbits & Xncode & Xnlen & Xwin & Xlens1 & Xlens2 & Xctbl & Xtbls).
Ltac ieq_xfer :=
  unfold IEQ; cbv zeta; sacc;
  repeat match goal with |- _ /\ _ => split end;
  first [ assumption | reflexivity | idtac ].

Lemma shl32_1_nz : forall wb, 0 < wb < 32 -> wrap32 (Z.shiftl 1 wb) <> 0.
Proof.
  intros wb Hwb. rewrite Z.shiftl_1_l. rewrite wrap32_id; [pose proof (Z.pow_pos_nonneg 2 wb); lia|].
  split; [apply Z.pow_nonneg; lia|]. apply Z.pow_lt_mono_r; lia.
Qed.

Section UpdW.
  Variable t1 : inflate_state.
Variable t2 : inflate_state.
Variable src : arr.
Variable e : Z.
Variable copy : Z.
  Hypothesis HC : CORE t1.
  Hypothesis Hb : is_window_blk t1 <> None.
  Hypothesis HQ : IEQ t1 t2.
  Hypothesis Hcopy : 0 <= copy.

  Let V := wrap32 (Z.shiftl 1 (is_wbits t1)).

  Lemma sA_cong : exists u1 u2,
    updw_core t1 src e copy = updw_core u1 src e copy /\ updw_core t2 src e copy = updw_core u2 src e copy
    /\ IEQ u1 u2 /\ is_wsize u1 = V /\ 0 <= is_whave u1 <= V /\ 0 <= is_wnext u1 /\ (V <> 0 -> is_wnext u1 < V)
    /\ (is_whave u1 < V -> is_wnext u1 = is_whave u1) /\ arr_len (is_window u1) = V /\ is_wbits u1 = is_wbits t1 /\ 0 <= V.
  Proof.
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
    destruct (C2 Hb) as [WL WB]. unfold shl32 in *.
    pose proof (wrap32_range (Z.shiftl 1 (is_wbits t1))) as VR. fold V in VR, WL, C3.
    ieq_facts HQ.
    destruct (Z.eqb_spec (is_wsize t1) 0) as [Z0|Z0].
    - destruct (C6 Z0) as [WH0 WN0].
      destruct (Z.eqb_spec V 0) as [V0|V0].
      +
        exists t1, t2. split; [reflexivity|]. split; [reflexivity|]. split; [exact HQ|]. rewrite Z0, WH0, WN0, V0.
        clear - WL V0. repeat split; lia.
      + exists (iset_whave (iset_wnext (iset_wsize t1 V) 0) 0), (iset_whave (iset_wnext (iset_wsize t2 V) 0) 0).
        split; [|split; [|split; [ieq_xfer; intros i Hi; exfalso; lia| sacc; clear - VR WL; repeat split; lia]]].
        * unfold updw_core, sA. unfold shl32. fold V. sacc. rewrite Z0, (proj2 (Z.eqb_neq V 0) V0). reflexivity.
        * unfold updw_core, sA. unfold shl32. rewrite Xwsize, Xwbits. fold V. sacc. rewrite Z0, (proj2 (Z.eqb_neq V 0) V0). reflexivity.
    - exists t1, t2. split; [reflexivity|]. split; [reflexivity|]. split; [exact HQ|].
      pose proof (C3 Z0) as F3. pose proof (C7 Z0) as F7. pose proof (C8 Z0) as F8.
      clear - Z0 F3 F7 F8 VR WL WB C4 C5. repeat split; lia.
  Qed.

  Lemma updw_core_cong : IEQ (updw_core t1 src e copy) (updw_core t2 src e copy).
  Proof.
    destruct sA_cong as (u1 & u2 & -> & -> & HQu & W1 & W2 & W3 & W4 & W5 & L1 & WBu & VP).
    pose proof (wrap32_range (Z.shiftl 1 (is_wbits t1))) as VR. fold V in VR.
    clear HQ HC Hb. ieq_facts HQu.
    Ltac nz W1 := sacc;
      repeat match goal with X : ?f ?b = ?f ?a |- context [?f ?b] => lazymatch f with is_window => fail | _ => rewrite !X end end;
      rewrite ?W1.
    unfold updw_core, sA. nz W1. unfold shl32. rewrite ?WBu. fold V.
    destruct (Z.eqb_spec V 0) as [V0|V0].
    {
      nz W1. rewrite V0. rewrite (proj2 (Z.leb_le 0 copy) Hcopy). ieq_xfer; try (rewrite !arr_len_blit; exact XLwin).
      intros i Hi. exfalso. lia. }
    nz W1.
    rewrite (wrap32_id (V - is_wnext u1)) by lia.
    destruct (Z.leb_spec V copy) as [LE|GT]; nz W1.
    - ieq_xfer.
      + rewrite !arr_len_blit. exact XLwin.
      + intros i Hi. apply blit_agree; [exact XLwin|]. right. rewrite L1. lia.
    - set (dist := if copy <? V - is_wnext u1 then copy else V - is_wnext u1).
      assert (Hd : 0 <= dist <= copy /\ dist <= V - is_wnext u1 /\ (dist = copy \/ dist = V - is_wnext u1))
        by (subst dist; destruct (Z.ltb_spec copy (V - is_wnext u1)); lia).
      rewrite (wrap32_id (copy - dist)) by lia.
      destruct (Z.eqb_spec (copy - dist) 0) as [CD|CD]; cbn [negb]; nz W1.
      + rewrite (wrap32_id (is_wnext u1 + dist)) by lia.
        assert (AG : forall i, 0 <= i < (if is_whave u1 <? V then is_whave u1 + dist else is_whave u1) ->
                  arr_get (arr_blit (is_window u2) (is_wnext u1) src (e - copy) dist) i = arr_get (arr_blit (is_window u1) (is_wnext u1) src (e - copy) dist) i).
        { intros i Hi. apply blit_agree; [exact XLwin|]. rewrite L1.
          destruct (Z_lt_le_dec i (is_wnext u1)) as [A|A]; [left; apply Xwin|].
          - destruct (Z.ltb_spec (is_whave u1) V); [pose proof (W5 ltac:(lia)); lia|lia].
          - destruct (Z_lt_le_dec i (is_wnext u1 + dist)) as [B|B]; [right; lia|left; apply Xwin].
            destruct (Z.ltb_spec (is_whave u1) V); [pose proof (W5 ltac:(lia)); lia|lia]. }
        destruct (Z.eqb_spec (is_wnext u1 + dist) V) as [EV|EV]; nz W1;
          (destruct (Z.ltb_spec (is_whave u1) V) as [WH|WH]; nz W1); rewrite ?(wrap32_id (is_whave u1 + dist)) by lia;
          ieq_xfer; try (rewrite !arr_len_blit; exact XLwin); intros i Hi; apply AG;
          first [rewrite (proj2 (Z.ltb_lt _ _) WH); exact Hi | rewrite (proj2 (Z.ltb_ge _ _) WH); exact Hi].
      + ieq_xfer.
        * rewrite !arr_len_blit. exact XLwin.
        * intros i Hi. apply blit_agree; [rewrite !arr_len_blit; exact XLwin|]. rewrite arr_len_blit, L1.
          destruct (Z_lt_le_dec i (copy - dist)) as [A|A]; [right; lia|left].
          apply blit_agree; [exact XLwin|]. rewrite L1.
          destruct (Z_lt_le_dec i (is_wnext u1)) as [B|B]; [left; apply Xwin|right; lia].
          destruct (Z_lt_le_dec (is_whave u1) V); [pose proof (W5 ltac:(lia)); lia|lia].
  Qed.
End UpdW.


Definition UWS (s : inflate_state) : Prop :=
  is_wrap s = 5 /\ gzb (is_mode s) = false
  /\ (is_flags s = 0 \/ (is_flags s = -1 /\ (is_mode s = HEAD \/ is_mode s = BAD \/ is_mode s = MEM))).

Lemma UW_UWS : forall s c r, UW s c r -> UWS s.
Proof.
  intros s c r (W & G & [F|(F & M & _)]); (split; [exact W|]); (split; [exact G|]); [left; exact F|right].
  split; [exact F|]. destruct M as [M|M]; [left; exact M|right; left; exact M].
Qed.
Lemma UWS_UW : forall s c r, UWS s -> is_mode s <> MEM -> ir_put r = 0 -> ir_out r = arr_len (ic_outbuf c) -> UW s c r.
Proof.
  intros s c r (W & G & [F|[F M]]) NM Hp Ho; (split; [exact W|]); (split; [exact G|]); [left; exact F|right].
  split; [exact F|]. split; [|exact (conj Hp Ho)]. destruct M as [M|[M|M]]; [left; exact M|right; exact M|exfalso; exact (NM M)].
Qed.


Lemma lv_fin_cong : forall flush t1 t2 c r,
  IEQ t1 t2 -> UW t1 c r -> REGS c r ->
  snd (lv_fin flush t1 (c_rest c r) r) = snd (lv_fin flush t2 (c_rest c r) r)
  /\ IEQ (fst (lv_fin flush t1 (c_rest c r) r)) (fst (lv_fin flush t2 (c_rest c r) r))
  /\ UWS (fst (lv_fin flush t1 (c_rest c r) r)).
Proof.
  intros flush t1 t2 c r HQ HU HR. ieq_facts HQ.
  pose proof HR as (RN & RH & RNH & RP & RL & RPL & _).
  assert (OUT0 : is_flags t1 <> 0 -> wrap32 (ir_out r - ic_avail_out (c_rest c r)) = 0).
  { intros F. destruct HU as (_ & _ & [F0|(_ & _ & P0 & O0)]); [exfalso; exact (F F0)|].
    unfold c_rest. sacc. rewrite O0, <- RPL, P0. replace (0 + ir_left r - ir_left r) with 0 by lia. reflexivity. }
  unfold lv_fin, dt_model, UPDATE_CHECK_bytes. cbv zeta.
  sacc; rewrite ?Xwrap, ?Xtotal, ?Xflags, ?Xbits, ?Xlast, ?Xmode.
  destruct (Z.eqb_spec (is_flags t1) 0) as [F0|F0]; cbn [negb].
  - rewrite (Xcheck F0).
    match goal with |- context [if ?cnd then _ else _] => destruct cnd eqn:C end; sacc; rewrite ?Xwrap, ?Xtotal, ?Xflags, ?Xbits, ?Xlast, ?Xmode.
    + split; [reflexivity|]. split; [ieq_xfer|]. apply (UW_UWS _ c r). destruct HU as (A1 & A2 & A3). sacc. exact (conj A1 (conj A2 A3)).
    + split; [reflexivity|]. split; [ieq_xfer|]. apply (UW_UWS _ c r). destruct HU as (A1 & A2 & A3). sacc. exact (conj A1 (conj A2 A3)).
  - rewrite (OUT0 F0). rewrite Z.eqb_refl. cbn [negb]. rewrite !Bool.andb_false_r. sacc; rewrite ?Xwrap, ?Xtotal, ?Xflags, ?Xbits, ?Xlast, ?Xmode.
    split; [reflexivity|]. split; [ieq_xfer|]. apply (UW_UWS _ c r). destruct HU as (A1 & A2 & A3). sacc. exact (conj A1 (conj A2 A3)).
Qed.


Definition ZC (zc : ZCall) : Prop :=
  0 <= zc_avail_out zc < 2 ^ 32 /\ zlength (zc_input zc) < 2 ^ 32 /\ bytes_ok (zc_input zc).

Lemma WINV_entry' : forall st zc,
  INV st -> ZC zc ->
  WINV (W0 st zc) /\ PHI (W0 st zc) < 64 * (ic_avail_in (w_c (W0 st zc)) + ic_avail_out (w_c (W0 st zc)) + 64).
Proof.
  intros st zc (HC & HBs & HM) (Hao & Hlen & Hby).
  pose proof (zlength_nonneg (zc_input zc)) as LN. destruct HBs as [B1 B2].
  assert (HR : REGS (icall_of_zcall zc) (mkIR 0 (zlength (zc_input zc)) 0 (zc_avail_out zc) (is_hold st) (is_bits st) (zlength (zc_input zc)) (zc_avail_out zc) Z_OK)).
  { unfold REGS, HB, icall_of_zcall. cbn [ic_input ic_outbuf ir_next ir_have ir_put ir_left ir_hold ir_bits].
    rewrite arr_len_of_list. unfold arr_make. rewrite arr_len_init.
    repeat (split; [first [lia | intros i; apply arr_get_of_list_byte; exact Hby] |]). lia. }
  unfold W0, s_entry. destruct (Z.eqb_spec (is_mode st) TYPE) as [ET|ET].
  - split.
    + unfold WINV. cbn [w_s w_c w_r]. sacc. split; [core_keep HC; apply CORE_length; exact HC|]. split; [exact HR|].
      rewrite ET in HM. split; [revert HM; mred; intros HM; split; [common_keep (proj1 HM) | exact (proj2 HM)]|].
      split; [mred; unfold icall_of_zcall; cbn [ic_outbuf]; unfold arr_make; rewrite arr_len_init; reflexivity|].
      intros _; reflexivity.
    + unfold PHI. cbn [w_s w_c w_r]. sacc. unfold icall_of_zcall. cbn [ic_avail_in ic_avail_out]. mred. lia.
  - split.
    + unfold WINV. cbn [w_s w_c w_r]. cbn [ir_hold ir_bits ir_out ir_put]. split; [exact HC|]. split; [exact HR|]. split; [exact HM|].
      split; [|intros _; reflexivity].
      unfold WF. destruct ((is_mode st =? LENGTH) || (is_mode st =? DONE) || (is_mode st =? BAD)); [exact I|].
      unfold icall_of_zcall. cbn [ic_outbuf]. unfold arr_make. rewrite arr_len_init.
      destruct ((is_mode st =? HEAD) || (is_mode st =? FLAGS)); [split|]; reflexivity.
    + unfold PHI. cbn [w_s w_c w_r]. cbn [ir_have ir_bits ir_left]. unfold icall_of_zcall. cbn [ic_avail_in ic_avail_out].
      pose proof (rank_range (is_mode st)). lia.
Qed.

Lemma inf_loop_MEM : forall flush w,
  is_mode (w_s w) = MEM -> 0 <= ic_avail_in (w_c w) -> 0 <= ic_avail_out (w_c w) ->
  inf_loop ivar_ref flush w = (SRet Z_MEM_ERROR, w).
Proof.
  intros flush [s c r] E Hai Hao. cbn [w_s w_c] in E, Hai, Hao. unfold inf_loop. cbn [w_c].
  rewrite iterZ_step by lia. unfold dispatch at 1. unfold abind at 1. rewrite gs_eq. cbn [w_s]. cbv zeta. rewrite E.
  mred. reflexivity.
Qed.

Lemma W0_WMID : forall s1 s2 zc, IEQ s1 s2 -> UWS s1 -> is_mode s1 <> MEM -> 0 <= zc_avail_out zc ->
  WMID (W0 s1 zc) (W0 s2 zc).
Proof.
  intros s1 s2 zc HQ HUS NM Hao. ieq_facts HQ. unfold W0, s_entry. rewrite Xmode, Xhold, Xbits.
  apply WMID_mk.
  - destruct (Z.eqb_spec (is_mode s1) TYPE) as [ET|ET]; [|exact HQ].
    unfold IEQ; cbv zeta; sacc. live_red. cbn [tbl_eq].
    repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | (intros X; discriminate X) | idtac].
  - apply UWS_UW.
    + destruct HUS as (A1 & A2 & A3). destruct (Z.eqb_spec (is_mode s1) TYPE) as [ET|ET]; [|exact (conj A1 (conj A2 A3))].
      split; [sacc; exact A1|]. split; [reflexivity|]. sacc. destruct A3 as [F|(F & M)]; [left; exact F|exfalso].
      rewrite ET in M. destruct M as [M|[M|M]]; discriminate M.
    + destruct (Z.eqb_spec (is_mode s1) TYPE) as [ET|ET]; sacc; [intros X; discriminate X|exact NM].
    + reflexivity.
    + cbn [ir_out icall_of_zcall ic_outbuf]. unfold arr_make. rewrite arr_len_init. reflexivity.
Qed.

Section TwoHooks.
  Context {St : Type}.
  Variable H1 : zhooks St.
Variable H2 : zhooks St.
  Hypothesis HZ : forall a b, srel (fun r1 r2 => option_map fst r1 = option_map fst r2) (zalloc H1 a b) (zalloc H2 a b).
  Hypothesis HF : forall b, srel eq (zfree H1 b) (zfree H2 b).

  Definition UWO (s1 : inflate_state) (o1 o2 : option inflate_state) : Prop :=
    match o1, o2 with
    | None, None => True
    | Some t1, Some t2 => IEQ t1 t2 /\ is_mode t1 = is_mode s1 /\ is_wrap t1 = is_wrap s1 /\ is_flags t1 = is_flags s1
    | _, _ => False
    end.

  Lemma updw_core_mwf : forall s src e copy,
    is_mode (updw_core s src e copy) = is_mode s /\ is_wrap (updw_core s src e copy) = is_wrap s /\ is_flags (updw_core s src e copy) = is_flags s.
  Proof.
    intros. pose proof (updw_core_fields s src e copy) as F. cbv zeta in F. destruct F as (F1 & F2 & F3 & _).
    exact (conj F1 (conj F2 F3)).
  Qed.

  Lemma updatewindow_cong : forall s1 s2 src e copy,
    CORE s1 -> is_wbits s1 <> 0 -> IEQ s1 s2 -> 0 <= copy ->
    srel (UWO s1) (updatewindow H1 s1 src e copy) (updatewindow H2 s2 src e copy).
  Proof.
    intros s1 s2 src e copy HC Hwb HQ Hcopy. ieq_facts HQ.
    rewrite !updatewindow_unfold. rewrite Xwblk, Xwbits.
    pose proof HC as (C1 & C2 & _).
    destruct (is_window_blk s1) as [b|] eqn:EB.
    - eapply (srel_bind (fun o1 o2 => o1 = Some s1 /\ o2 = Some s2)).
      + apply srel_ret. split; reflexivity.
      + intros o1 o2 [-> ->]. rewrite !updw_body_eq. apply srel_ret. cbn [UWO]. split; [|apply updw_core_mwf].
        apply updw_core_cong; [exact HC | rewrite EB; intros X; discriminate X | exact HQ | exact Hcopy].
    - eapply (srel_bind (fun o1 o2 => match o1, o2 with
                                       | None, None => True
                                       | Some t1, Some t2 => IEQ t1 t2 /\ CORE t1 /\ is_window_blk t1 <> None /\ is_wbits t1 = is_wbits s1
                                                             /\ (is_mode t1 = is_mode s1 /\ is_wrap t1 = is_wrap s1 /\ is_flags t1 = is_flags s1)
                                       | _, _ => False end)).
      + eapply srel_bind; [apply HZ|]. intros r1 r2 Er.
        destruct r1 as [[b1 g1]|]; destruct r2 as [[b2 g2]|]; cbn [option_map fst] in Er; try discriminate Er.
        * injection Er; intros <-. apply srel_ret. split; [|split; [apply CORE_fresh_window; [exact HC|first [exact EB|reflexivity]|exact Hwb]|split; [sacc; intros X; discriminate X|split; [reflexivity|sacc; repeat split; reflexivity]]]].
          pose proof (C1 ltac:(first [exact EB|reflexivity])) as Z0. pose proof HC as (_ & _ & _ & _ & _ & C6 & _). destruct (C6 Z0) as [WH0 _].
          ieq_xfer; unfold iarr_u8_of; rewrite ?arr_len_init; try reflexivity.
          intros i Hi. exfalso. rewrite WH0 in Hi. lia.
        * apply srel_ret. exact I.
      + intros o1 o2 Ho. destruct o1 as [u1|]; destruct o2 as [u2|]; try contradiction; [|apply srel_ret; exact I].
        destruct Ho as (HQ' & HC' & Hb' & Hwb' & (M1 & M2 & M3)). rewrite !updw_body_eq. apply srel_ret. cbn [UWO]. rewrite <- M1, <- M2, <- M3. split; [|apply updw_core_mwf].
        apply updw_core_cong; [exact HC' | exact Hb' | exact HQ' | exact Hcopy].
  Qed.

  Definition IRES (p1 p2 : inflate_state * ZRet) : Prop :=
    snd p1 = snd p2 /\ IEQ (fst p1) (fst p2) /\ UWS (fst p1).

  Lemma IEQ_MEM : forall a b, IEQ a b -> IEQ (iset_mode a MEM) (iset_mode b MEM).
  Proof.
    intros a b HQ. ieq_facts HQ. unfold IEQ; cbv zeta; sacc. live_red. cbn [tbl_eq].
    repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | (intros X; discriminate X) | idtac].
  Qed.
  Lemma UWS_MEM : forall a, UWS a -> UWS (iset_mode a MEM).
  Proof.
    intros a (A1 & A2 & A3). unfold UWS. sacc. split; [exact A1|]. split; [reflexivity|].
    destruct A3 as [F|(F & _)]; [left; exact F|right]. split; [exact F|]. right; right; reflexivity.
  Qed.

  Lemma inf_leave_cong : forall flush s1 s2 c r,
    WINV (mkW s1 c r) -> IEQ s1 s2 -> UW s1 c r ->
    srel IRES (inf_leave H1 flush (mkW s1 c r)) (inf_leave H2 flush (mkW s2 c r)).
  Proof.
    intros flush s1 s2 c r HW HQ HU. ieq_facts HQ.
    unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (HC & HR & HMF & HWF & HWB).
    pose proof HR as (RN & RH & RNH & RP & RL & RPL & HBr & RIN & RNI & RNO).
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & _).
    intros g. rewrite !(inf_leave_eq _). revert g.
    match goal with |- forall g, mrel _ (?m1 g) (?m2 g) => change (srel IRES m1 m2) end.
    assert (EQc : lv_cond flush (s_rest s2 r) (c_rest c r) r = lv_cond flush (s_rest s1 r) (c_rest c r) r)
      by (unfold lv_cond, s_rest; sacc; rewrite Xwsize, Xmode; reflexivity).
    rewrite EQc.
    assert (HQr : IEQ (s_rest s1 r) (s_rest s2 r)) by (unfold s_rest; ieq_xfer).
    assert (HUr : UW (s_rest s1 r) c r) by (unfold s_rest; destruct HU as (A1 & A2 & A3); split; [sacc; exact A1|]; split; [sacc; exact A2|sacc; exact A3]).
    assert (HCr : CORE (s_rest s1 r)) by (unfold s_rest; core_keep HC; apply CORE_length; exact HC).
    destruct (lv_cond flush (s_rest s1 r) (c_rest c r) r) eqn:LC.
    -
      assert (WB : is_wbits s1 <> 0).
      { intros W. destruct (C9 W) as [N _]. pose proof (C1 N) as Z0. pose proof (HWB W) as P0.
        assert (NLD : is_mode s1 <> LENGTH /\ is_mode s1 <> DONE).
        { split; intros E; rewrite E in HMF; revert HMF; mred; intros [X _]; exact (X W). }
        unfold WF in HWF.
        revert LC. unfold lv_cond, s_rest, c_rest. sacc. rewrite Z0, Z.eqb_refl. change (negb true) with false. rewrite Bool.orb_false_l.
        destruct (Z.eqb_spec (is_mode s1) BAD) as [EB'|NB].
        - rewrite EB' in *. replace (BAD <? BAD) with false by reflexivity. rewrite Bool.andb_false_r. cbn [andb]. intros X; discriminate X.
        - assert (EO : ir_out r = ir_left r).
          { destruct NLD as [N1 N2]. rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2) in HWF. cbn [orb] in HWF.
            destruct ((is_mode s1 =? HEAD) || (is_mode s1 =? FLAGS)); [destruct HWF as [E1 _]|rename HWF into E1]; rewrite E1, <- RPL, P0; lia. }
          rewrite EO. replace (ir_left r - ir_left r) with 0 by lia. change (wrap32 0 =? 0) with true. cbn [negb andb]. intros X; discriminate X. }
      eapply srel_bind.
      { apply updatewindow_cong; [exact HCr | unfold s_rest; sacc; exact WB | exact HQr | pose proof (wrap32_range (ir_out r - ic_avail_out (c_rest c r))); lia]. }
      intros o1 o2 Ho. destruct o1 as [t1|]; destruct o2 as [t2|]; try contradiction.
      + destruct Ho as (HQt & M1 & M2 & M3). apply srel_ret.
        assert (HUt : UW t1 c r).
        { destruct HUr as (A1 & A2 & A3). split; [rewrite M2; exact A1|]. split; [rewrite M1; exact A2|rewrite M1, M3; exact A3]. }
        destruct (lv_fin_cong flush t1 t2 c r HQt HUt HR) as (E1 & E2 & E3).
        split; [exact E1|]. split; [exact E2|exact E3].
      +
        apply srel_ret.
        destruct (lv_fin_cong flush (s_rest s1 r) (s_rest s2 r) c r HQr HUr HR) as (E1 & E2 & E3).
        rewrite (lv_fin_pre flush (s_rest s1 r)), (lv_fin_pre flush (s_rest s2 r)) in E1, E2. rewrite (lv_fin_pre flush (s_rest s1 r)) in E3.
        cbn [fst snd] in E1, E2, E3.
        unfold lv_mem. split; [| split]; cbn [fst snd].
        * unfold zret_of_icall. f_equal; [exact (f_equal zr_consumed E1) | exact (f_equal zr_output E1) | exact (f_equal zr_strm E1)].
        * exact (IEQ_MEM _ _ E2).
        * exact (UWS_MEM _ E3).
    - apply srel_ret. destruct (lv_fin_cong flush (s_rest s1 r) (s_rest s2 r) c r HQr HUr HR) as (E1 & E2 & E3).
      split; [exact E1|]. split; [exact E2|exact E3].
  Qed.

  Theorem inflate_m_cong : forall flush s1 s2 zc,
    FASTC ->
    INV s1 -> ZC zc -> IEQ s1 s2 -> UWS s1 ->
    srel IRES (inflate_m ivar_ref H1 s1 zc flush) (inflate_m ivar_ref H2 s2 zc flush).
  Proof.
    intros flush s1 s2 zc fastc I1 Hzc HQ HUS. pose proof Hzc as (Hao & Hlen & Hby). pose proof (zlength_nonneg (zc_input zc)) as LN.
    pose proof (INV_check s1 I1) as CK1.
    assert (CK2 : inflateStateCheck s2 = false) by (unfold inflateStateCheck; rewrite (proj1 (proj1 HQ)); exact CK1).
    rewrite (inflate_m_W0 H1) by exact CK1. rewrite (inflate_m_W0 H2) by exact CK2.
    destruct (Z.eq_dec (is_mode s1) MEM) as [EM|NM].
    -
      assert (EM2 : is_mode s2 = MEM) by (rewrite (proj1 (proj1 HQ)); exact EM).
      rewrite (inf_loop_MEM flush (W0 s1 zc)); cycle 1.
      { unfold W0, s_entry. cbn [w_s]. rewrite EM. change (MEM =? TYPE) with false. cbv iota. exact EM. }
      { cbn [W0 w_c icall_of_zcall ic_avail_in]. lia. }
      { cbn [W0 w_c icall_of_zcall ic_avail_out]. lia. }
      rewrite (inf_loop_MEM flush (W0 s2 zc)); cycle 1.
      { unfold W0, s_entry. cbn [w_s]. rewrite EM2. change (MEM =? TYPE) with false. cbv iota. exact EM2. }
      { cbn [W0 w_c icall_of_zcall ic_avail_in]. lia. }
      { cbn [W0 w_c icall_of_zcall ic_avail_out]. lia. }
      apply srel_ret. split; [reflexivity|]. cbn [fst]. split; [|unfold W0, s_entry; cbn [w_s]; rewrite EM; change (MEM =? TYPE) with false; cbv iota; exact HUS].
      unfold W0, s_entry. cbn [w_s]. rewrite EM, EM2. change (MEM =? TYPE) with false. cbv iota. exact HQ.
    - destruct (WINV_entry' s1 zc I1 Hzc) as [HW HP].
      pose proof (W0_WMID s1 s2 zc HQ HUS NM ltac:(lia)) as HM.
      pose proof (inf_loop_cong flush fastc _ _ HW HM) as L. pose proof (inf_loop_post flush _ HW HP) as P.
      destruct (inf_loop ivar_ref flush (W0 s1 zc)) as [st1 w1']. destruct (inf_loop ivar_ref flush (W0 s2 zc)) as [st2 w2'].
      destruct L as [-> HM']. destruct P as [HW' Pst].
      destruct w1' as [t1 c1 r1]. destruct w2' as [t2 c2 r2]. destruct HM' as (Ec & Er & HQ' & HU'). cbn [w_s w_c w_r] in Ec, Er, HQ', HU'. subst c2 r2.
      destruct st1 as [|rc].
      + apply inf_leave_cong; [exact HW' | exact HQ' | exact HU'].
      + apply srel_ret. split; [reflexivity|]. cbn [fst]. split; [exact HQ'|exact (UW_UWS _ _ _ HU')].
  Qed.
End TwoHooks.


Lemma inflate_m_sim {St} (H : zhooks St) : forall s zc flush g,
  mall (fun p => exists ch, ipure (inflate_m ivar_ref hooks_pure s zc flush) ch = Some (fst p))
       (inflate_m ivar_ref H s zc flush g).
Proof.
  intros s zc flush g.
  destruct (inflateStateCheck s) eqn:CK.
  { unfold inflate_m at 2. rewrite CK. unfold sret. cbn [mall fst]. exists None. unfold ipure, inflate_m. rewrite CK. reflexivity. }
  rewrite (inflate_m_W0 H) by exact CK.
  assert (P2 : forall ch, ipure (inflate_m ivar_ref hooks_pure s zc flush) ch
                         = ipure (let '(stop, w) := inf_loop ivar_ref flush (W0 s zc) in
                                  match stop with SLeave => inf_leave hooks_pure flush w | SRet rc => sret (w_s w, zret_of_icall (w_c w) rc) end) ch).
  { intros ch. rewrite (inflate_m_W0 hooks_pure) by exact CK. reflexivity. }
  destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop [t c r]].
  destruct stop as [|rc].
  2:{ unfold sret. cbn [mall fst]. exists None. rewrite P2. reflexivity. }
  rewrite (inf_leave_eq H).
  assert (P3 : forall ch, ipure (inf_leave hooks_pure flush (mkW t c r)) ch =
            ipure (sbind (if lv_cond flush (s_rest t r) (c_rest c r) r
                          then updatewindow hooks_pure (s_rest t r) (ic_outbuf (c_rest c r)) (ic_next_out (c_rest c r)) (wrap32 (ir_out r - ic_avail_out (c_rest c r)))
                          else sret (Some (s_rest t r)))
                         (fun so => match so with
                                    | None => sret (lv_mem (s_rest t r) (c_rest c r) r)
                                    | Some s' => sret (lv_fin flush s' (c_rest c r) r)
                                    end)) ch).
  { intros ch. unfold ipure. rewrite (inf_leave_eq hooks_pure). reflexivity. }
  destruct (lv_cond flush (s_rest t r) (c_rest c r) r).
  2:{ unfold sbind, sret. cbn [mall mbind fst snd]. exists None. rewrite P2, P3. reflexivity. }
  destruct (is_window_blk (s_rest t r)) as [b|] eqn:EB.
  - rewrite (updatewindow_some H _ _ _ _ b EB). unfold sbind, sret. cbn [mall mbind fst snd]. exists None.
    rewrite P2, P3. unfold ipure, sbind. rewrite (updatewindow_some hooks_pure _ _ _ _ b EB). unfold sret. cbn [mbind fst snd]. reflexivity.
  - rewrite updatewindow_unfold, EB. rewrite !sbind_assoc.
    apply mall_sbind_any. intros rr g1.
    destruct rr as [[b gg]|].
    + unfold sbind at 1. unfold sret at 1. cbn [mbind fst snd]. rewrite updw_body_eq. unfold sret. cbn [mall mbind fst snd].
      exists (Some (b, gg)). rewrite P2, P3. unfold ipure, sbind. rewrite updatewindow_unfold, EB.
      unfold sbind, sret. cbn [zalloc hooks_pure mbind fst snd]. rewrite updw_body_eq. reflexivity.
    + unfold sbind, sret. cbn [mall mbind fst snd]. exists None. rewrite P2, P3. unfold ipure, sbind. rewrite updatewindow_unfold, EB.
      unfold sbind, sret. cbn [zalloc hooks_pure mbind fst snd]. reflexivity.
Qed.

Lemma inflate_INV' : forall s zc flush ch s' zr,
  INV s -> ZC zc -> ipure (inflate_m ivar_ref hooks_pure s zc flush) ch = Some (s', zr) -> INV s'.
Proof.
  intros s zc flush ch s' zr HI Hz E.
  unfold ipure in E. rewrite (inflate_m_W0 hooks_pure) in E by (apply INV_check; exact HI).
  destruct (WINV_entry' s zc HI Hz) as [HW HP].
  pose proof (inf_loop_post flush (W0 s zc) HW HP) as L.
  destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop w'].
  destruct stop as [|rc].
  - destruct L as [HW' _]. destruct w' as [s1 c1 r1].
    destruct (inf_leave hooks_pure flush (mkW s1 c1 r1) ch) as [p| | |] eqn:EL; try discriminate E.
    destruct p as [[s2 zr2] ch']. cbn [fst] in E.
    assert (E2 : s2 = s') by (injection E; intros _ X; exact X). subst s2.
    exact (inf_leave_INV flush s1 c1 r1 ch s' zr2 ch' HW' EL).
  - destruct L as [_ HI']. unfold sret in E. cbn [fst] in E.
    assert (E2 : w_s w' = s') by (injection E; intros _ X; exact X). rewrite <- E2. exact HI'.
Qed.

Lemma inflate_m_INV {St} (H : zhooks St) : forall s zc flush g,
  INV s -> ZC zc -> mall (fun p => INV (fst (fst p))) (inflate_m ivar_ref H s zc flush g).
Proof.
  intros s zc flush g HI Hz. eapply mall_mono; [|apply (inflate_m_sim H)].
  intros [[s' zr] g'] [ch E]. cbn [fst] in E |- *. exact (inflate_INV' s zc flush ch s' zr HI Hz E).
Qed.
