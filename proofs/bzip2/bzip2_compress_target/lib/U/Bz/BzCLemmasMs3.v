(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM BzCPermM BzCLemmasMs BzCQsortM1 BzCQsortM2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewF BzCLemmasMs2.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Lemma mqs_eta : forall x, x = MQS (mq_a1 x) (mq_sp x) (mq_slo x) (mq_shi x) (mq_sd x) (mq_nlo x) (mq_nhi x) (mq_nd x) (mq_budget x) (mq_exit x).
Proof. intros x. destruct x. reflexivity. Qed.

Lemma ITER_leaf : forall a2 qoff nb a1 qsp slo shi sd nlo nhi nd b,
  let lo := zget slo (qsp - 1) in let hi := zget shi (qsp - 1) in let d := zget sd (qsp - 1) in
  (hi - lo <? 20) || (14 <? d) = true ->
  ITER a2 qoff nb (MQS a1 qsp slo shi sd nlo nhi nd b false) =
  MQS (fst (mainSimpleSort a1 a2 qoff nb lo hi d b)) (qsp - 1) slo shi sd nlo nhi nd
      (snd (mainSimpleSort a1 a2 qoff nb lo hi d b)) (snd (mainSimpleSort a1 a2 qoff nb lo hi d b) <? 0).
Proof.
  intros. unfold ITER, TOPlo, TOPhi, TOPd. cbn [mq_sp mq_slo mq_shi mq_sd]. subst lo hi d. rewrite H.
  unfold LEAF, TOPlo, TOPhi, TOPd. cbn [mq_a1 mq_sp mq_slo mq_shi mq_sd mq_nlo mq_nhi mq_nd mq_budget].
  destruct (mainSimpleSort _ _ _ _ _ _ _ _) as [a1' b']. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ITER_part : forall a2 a1 qsp slo shi sd nlo nhi nd b med,
  let lo := zget slo (qsp - 1) in let hi := zget shi (qsp - 1) in let d := zget sd (qsp - 1) in
  0 <= lo -> lo <= hi ->
  med = mmed3 (rd8 a2 (rd32 a1 lo + d)) (rd8 a2 (rd32 a1 hi + d)) (rd8 a2 (rd32 a1 (Z.shiftr (lo + hi) 1) + d)) ->
  let pp := mpart_loop (S (Z.to_nat (hi - lo + 1))) (Z.to_nat (hi - lo + 1)) a2 d med (MP a1 lo hi lo hi) in
  PART a2 (MQS a1 qsp slo shi sd nlo nhi nd b false) = pp /\
  lo <= mp_ltLo pp /\ mp_ltLo pp <= mp_unLo pp /\ mp_unLo pp = mp_unHi pp + 1 /\ mp_unHi pp <= mp_gtHi pp /\ mp_gtHi pp <= hi.
Proof.
  intros a2 a1 qsp slo shi sd nlo nhi nd b med lo hi d Hlo Hlh Hmed pp.
  assert (HX : exists x, lo <= x <= hi /\ med = rd8 a2 (rd32 a1 x + d)).
  { pose proof (mmed3_in (rd8 a2 (rd32 a1 lo + d)) (rd8 a2 (rd32 a1 hi + d)) (rd8 a2 (rd32 a1 (Z.shiftr (lo + hi) 1) + d))) as MM.
    rewrite <- Hmed in MM.
    assert (MID : lo <= Z.shiftr (lo + hi) 1 <= hi).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
    destruct MM as [MM|[MM|MM]]; [exists lo | exists hi | exists (Z.shiftr (lo + hi) 1)]; split; try exact MM; lia. }
  cps_destruct HX as (x & Hx & Hm).
  pose proof (mq_part a2 d med lo hi a1 x Hx ltac:(unfold key; exact Hm)) as PP. cbn zeta in PP.
  split; [| subst pp; tauto].
  unfold PART, MED, TOPlo, TOPhi, TOPd. cbn [mq_a1 mq_sp mq_slo mq_shi mq_sd]. subst pp lo hi d. rewrite <- Hmed. reflexivity.
Qed.

Lemma ITER_repush : forall a2 qoff nb a1 qsp slo shi sd nlo nhi nd b pp,
  let lo := zget slo (qsp - 1) in let hi := zget shi (qsp - 1) in let d := zget sd (qsp - 1) in
  (hi - lo <? 20) || (14 <? d) = false ->
  PART a2 (MQS a1 qsp slo shi sd nlo nhi nd b false) = pp -> mp_gtHi pp < mp_ltLo pp ->
  ITER a2 qoff nb (MQS a1 qsp slo shi sd nlo nhi nd b false) =
  MQS (mp_a1 pp) qsp (zset slo (qsp - 1) lo) (zset shi (qsp - 1) hi) (zset sd (qsp - 1) (d + 1)) nlo nhi nd b false.
Proof.
  intros a2 qoff nb a1 qsp slo shi sd nlo nhi nd b pp lo hi d Hc Hp Hlt.
  unfold ITER. unfold TOPlo, TOPhi, TOPd. cbn [mq_sp mq_slo mq_shi mq_sd]. subst lo hi d. rewrite Hc. rewrite Hp.
  replace (mp_gtHi pp <? mp_ltLo pp) with true by (symmetry; apply Z.ltb_lt; exact Hlt).
  unfold mpush, Q1. cbn. replace (qsp - 1 + 1) with qsp by lia. reflexivity.
Qed.

Lemma ITER_push3 : forall a2 qoff nb a1 qsp slo shi sd nlo nhi nd b pp,
  let q := MQS a1 qsp slo shi sd nlo nhi nd b false in
  let lo := zget slo (qsp - 1) in let hi := zget shi (qsp - 1) in let d := zget sd (qsp - 1) in
  (hi - lo <? 20) || (14 <? d) = false ->
  PART a2 q = pp -> mp_ltLo pp <= mp_gtHi pp ->
  ITER a2 qoff nb q = PUSH3 (net (Q2 q pp)).
Proof.
  intros a2 qoff nb a1 qsp slo shi sd nlo nhi nd b pp q lo hi d Hc Hp Hle.
  unfold ITER. unfold TOPlo, TOPhi, TOPd. subst q. cbn [mq_sp mq_slo mq_shi mq_sd]. subst lo hi d. rewrite Hc. rewrite Hp.
  replace (mp_gtHi pp <? mp_ltLo pp) with false by (symmetry; apply Z.ltb_ge; exact Hle). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mqs_loop_step : forall f a2 qoff nb a1 qsp slo shi sd nlo nhi nd b, 0 < qsp ->
  mqs_loop (S f) a2 qoff nb (MQS a1 qsp slo shi sd nlo nhi nd b false) =
  mqs_loop f a2 qoff nb (ITER a2 qoff nb (MQS a1 qsp slo shi sd nlo nhi nd b false)).
Proof.
  intros. rewrite mqs_loop_S. cbn [mq_sp mq_exit negb andb]. replace (0 <? qsp) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite mqs_iter_ITER. reflexivity.
Qed.
Lemma mqs_loop_halt : forall f a2 qoff nb q, mq_sp q <= 0 \/ mq_exit q = true -> mqs_loop f a2 qoff nb q = q.
Proof.
  intros f a2 qoff nb q H. destruct f; [reflexivity|]. rewrite mqs_loop_S.
  destruct H as [H|H]; [replace (0 <? mq_sp q) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
  rewrite H. cbn [negb]. rewrite Bool.andb_false_r. reflexivity.
Qed.



(* [comment removed for export] *)
Definition step1F (qoff nb ss j : Z) (s : mss) : Prop :=
  j <> ss ->
  let sb := Z.shiftl ss 8 + j in let ft := s_ft s in
  exists c0 c1, 0 <= c0 <= c1 /\ c1 <= nb /\ ftcell (zget ft sb) c0 /\ ftcell (zget ft (sb + 1)) c1 /\
  (zget ft sb = c0 -> c0 < c1 - 1 ->
   let l := s_mql s in
   let q0 := mpush (MQS (s_a1 s) 0 (ml_slo l) (ml_shi l) (ml_sd l) (ml_nlo l) (ml_nhi l) (ml_nd l) (s_budget s) false) c0 (c1 - 1) BZ_N_RADIX in
   (forall v, let q := mqs_loop v (s_a2 s) qoff nb q0 in 0 < mq_sp q -> mq_exit q = false -> mqsF (s_a2 s) qoff nb q) /\
   (let q := mqs_loop (mqs_fuel c0 (c1 - 1)) (s_a2 s) qoff nb q0 in mq_sp q <= 0 \/ mq_exit q = true)).

Lemma land_setmask_small : forall c, 0 <= c < 2097152 -> Z.land c SETMASK = 0.
Proof.
  intros c Hc. pose proof (has_setmask_small c Hc) as H. unfold has_setmask in H.
  apply Bool.negb_false_iff in H. apply Z.eqb_eq in H. exact H.
Qed.
Lemma lor_setmask : forall c, 0 <= c < 2097152 -> Z.lor c SETMASK = c + 2097152.
Proof.
  intros c Hc. pose proof (Z.add_lor_land c SETMASK) as E. rewrite land_setmask_small in E by lia. unfold SETMASK in *. lia.
Qed.
(* [comment removed for export] *)
Lemma ftcell_cases : forall x c, 0 <= c < 2097152 -> ftcell x c -> x = c \/ x = c + 2097152.
Proof. intros x c Hc [H|H]; [left; exact H| right]. rewrite H. apply lor_setmask. exact Hc. Qed.

(* [comment removed for export] *)
Lemma ms_step1_skip : forall k qoff nb ss j a1 a2 ft bd cs ce b nqs l,
  j = ss ->
  ms_step1 (S k) qoff nb ss j (MSS a1 a2 ft bd cs ce b nqs l false) = ms_step1 k qoff nb ss (j + 1) (MSS a1 a2 ft bd cs ce b nqs l false).
Proof. intros. rewrite ms_step1_S. cbn [s_exit]. replace (j =? ss) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. Qed.

Lemma ms_step1_noq : forall k qoff nb ss j a1 a2 ft bd cs ce b nqs l,
  j <> ss ->
  let sb := Z.shiftl ss 8 + j in
  (has_setmask (zget ft sb) = true \/ clearmask (zget ft (sb + 1)) - 1 <= clearmask (zget ft sb)) ->
  ms_step1 (S k) qoff nb ss j (MSS a1 a2 ft bd cs ce b nqs l false) =
  ms_step1 k qoff nb ss (j + 1) (MSS a1 a2 (zset ft sb (Z.lor (zget ft sb) SETMASK)) bd cs ce b nqs l false).
Proof.
  intros k qoff nb ss j a1 a2 ft bd cs ce b nqs l Hj sb H. rewrite ms_step1_S. cbn [s_exit s_ft s_a1 s_a2 s_bd s_cs s_ce s_budget s_nqs s_mql].
  replace (j =? ss) with false by (symmetry; apply Z.eqb_neq; lia). subst sb.
  destruct H as [H|H]; [rewrite H; cbn [negb]; reflexivity|].
  destruct (has_setmask _); cbn [negb]; [reflexivity|].
  replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma ms_step1_q : forall k qoff nb ss j a1 a2 ft bd cs ce b nqs sl sh sd nl nh nd a1' sp' sl' sh' sd' nl' nh' nd' b' ex',
  j <> ss ->
  let sb := Z.shiftl ss 8 + j in
  let lo := clearmask (zget ft sb) in let hi := clearmask (zget ft (sb + 1)) - 1 in
  has_setmask (zget ft sb) = false -> lo < hi ->
  mqs_loop (mqs_fuel lo hi) a2 qoff nb (MQS a1 1 (zset sl 0 lo) (zset sh 0 hi) (zset sd 0 2) nl nh nd b false) = MQS a1' sp' sl' sh' sd' nl' nh' nd' b' ex' ->
  ms_step1 (S k) qoff nb ss j (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false) =
  if b' <? 0 then MSS a1' a2 ft bd cs ce b' (nqs + (hi - lo + 1)) (MQL sl' sh' sd' nl' nh' nd') true
  else ms_step1 k qoff nb ss (j + 1) (MSS a1' a2 (zset ft sb (Z.lor (zget ft sb) SETMASK)) bd cs ce b' (nqs + (hi - lo + 1)) (MQL sl' sh' sd' nl' nh' nd') false).
Proof.
  intros k qoff nb ss j a1 a2 ft bd cs ce b nqs sl sh sd nl nh nd a1' sp' sl' sh' sd' nl' nh' nd' b' ex' Hj sb lo hi Hm Hlh EQ.
  rewrite ms_step1_S. cbn [s_exit s_ft s_a1 s_a2 s_bd s_cs s_ce s_budget s_nqs s_mql].
  replace (j =? ss) with false by (symmetry; apply Z.eqb_neq; lia). subst sb. rewrite Hm. cbn [negb]. subst lo hi.
  replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold mainQSort3. cbn [ml_slo ml_shi ml_sd ml_nlo ml_nhi ml_nd]. unfold mpush. cbn [mq_a1 mq_sp mq_slo mq_shi mq_sd mq_nlo mq_nhi mq_nd mq_budget mq_exit].
  unfold BZ_N_RADIX. change (0 + 1) with 1. rewrite EQ. cbn [mq_a1 mq_budget mq_slo mq_shi mq_sd mq_nlo mq_nhi mq_nd].
  destruct (b' <? 0); reflexivity.
Qed.

(* [comment removed for export] *)
Definition kwrap (nb t : Z) : Z := if t <? 0 then t + nb else t.
Definition fwdF (a2 bd : zarr) (nb ss : Z) (a1 cs : zarr) (j : Z) : Prop :=
  (forall c, 0 <= c < 256 -> 0 <= zget cs c <= nb) /\
  (j < zget cs ss -> 0 <= j < nb /\
     let c1 := rd8 a2 (kwrap nb (rd32 a1 j - 1)) in zget bd c1 = 0 -> zget cs c1 < nb).
Definition bwdF (a2 bd : zarr) (nb ss : Z) (a1 ce : zarr) (j : Z) : Prop :=
  (forall c, 0 <= c < 256 -> -1 <= zget ce c < nb) /\
  (zget ce ss < j -> 0 <= j < nb /\
     let c1 := rd8 a2 (kwrap nb (rd32 a1 j - 1)) in zget bd c1 = 0 -> 0 <= zget ce c1).

Lemma ms_copy_fwd_S : forall f a1 cs a2 bd nb ss j,
  ms_copy_fwd (S f) a1 cs a2 bd nb ss j =
  (if j <? zget cs ss then
     let k := kwrap nb (rd32 a1 j - 1) in let c1 := rd8 a2 k in
     let '(a1', cs') := (if zget bd c1 =? 0 then (wr32 a1 (zget cs c1) k, zset cs c1 (zget cs c1 + 1)) else (a1, cs)) in
     ms_copy_fwd f a1' cs' a2 bd nb ss (j + 1)
   else (a1, cs, j)).
Proof. reflexivity. Qed.
Lemma ms_copy_fwd_stop : forall f a1 cs a2 bd nb ss j, zget cs ss <= j -> ms_copy_fwd f a1 cs a2 bd nb ss j = (a1, cs, j).
Proof. intros. destruct f; [reflexivity|]. rewrite ms_copy_fwd_S. replace (j <? zget cs ss) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma ms_copy_bwd_S : forall f a1 ce a2 bd nb ss j,
  ms_copy_bwd (S f) a1 ce a2 bd nb ss j =
  (if zget ce ss <? j then
     let k := kwrap nb (rd32 a1 j - 1) in let c1 := rd8 a2 k in
     let '(a1', ce') := (if zget bd c1 =? 0 then (wr32 a1 (zget ce c1) k, zset ce c1 (zget ce c1 - 1)) else (a1, ce)) in
     ms_copy_bwd f a1' ce' a2 bd nb ss (j - 1)
   else (a1, ce, j)).
Proof. reflexivity. Qed.
Lemma ms_copy_bwd_stop : forall f a1 ce a2 bd nb ss j, j <= zget ce ss -> ms_copy_bwd f a1 ce a2 bd nb ss j = (a1, ce, j).
Proof. intros. destruct f; [reflexivity|]. rewrite ms_copy_bwd_S. replace (zget ce ss <? j) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma pr_wr32 : forall nb a1 lo hi i v, nb <= 4294967296 -> pr nb a1 lo hi -> 0 <= v < nb -> pr nb (wr32 a1 i v) lo hi.
Proof.
  intros nb a1 lo hi i v Hnb P Hv x Hx. destruct (Z.eq_dec x i) as [->|NE].
  - rewrite rd32_wr32_same by lia. lia.
  - rewrite rd32_wr32_other by lia. apply P. exact Hx.
Qed.

Lemma lor_setmask_bound : forall x, (0 <= x < 4194304)%Z -> (0 <= Z.lor x 2097152 < 4194304)%Z.
Proof.
  intros x Hx. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|].
  assert (L : (Z.log2 (Z.lor x 2097152) < 22)%Z).
  { rewrite Z.log2_lor by lia. apply Z.max_lub_lt; [apply Z.log2_lt_pow2; lia| cbn; lia]. }
  apply Z.log2_lt_pow2 in L; [exact L|]. pose proof (Z.lor_nonneg x 2097152). 
  destruct (Z.eq_dec (Z.lor x 2097152) 0) as [E|E]; [|lia].
  rewrite Z.lor_eq_0_iff in E. lia.
Qed.

Definition ftv (ft : zarr) : Prop := forall v, 0 <= v <= 65536 -> 0 <= zget ft v < 4194304.
Lemma ftv_mark1 : forall ft x, ftv ft -> 0 <= x <= 65536 -> ftv (zset ft x (Z.lor (zget ft x) SETMASK)).
Proof.
  intros ft x F Hx v Hv. rewrite zget_zset. destruct (Z.eqb_spec v x); [|apply F; lia].
  unfold SETMASK. apply lor_setmask_bound. apply F. lia.
Qed.

Lemma clearmask_mod : forall x, (0 <= x < 4194304)%Z -> clearmask x = (x mod 2097152)%Z.
Proof.
  intros x Hx. unfold clearmask. change 2097152%Z with (2 ^ 21)%Z. rewrite <- Z.land_ones by lia.
  apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases k 21) as [L|G].
  - rewrite Z.ones_spec_low by lia. replace (Z.testbit 4292870143 k) with true; [reflexivity|].
    symmetry. change 4292870143%Z with (Z.lor (Z.ones 21) (Z.shiftl 1023 22)). rewrite Z.lor_spec, Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia.
    destruct (Z.eq_dec k 21) as [->|NE]; [rewrite !Bool.andb_false_r; reflexivity|].
    rewrite (Z.bits_above_log2 x k); [reflexivity| lia|].
    destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. assert (Z.log2 x < 22)%Z by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma clearmask_bounds : forall x, (0 <= x < 4194304)%Z -> (0 <= clearmask x < 2097152)%Z /\ (clearmask x <= x)%Z.
Proof. intros x Hx. rewrite clearmask_mod by lia. Z.div_mod_to_equations. lia. Qed.

