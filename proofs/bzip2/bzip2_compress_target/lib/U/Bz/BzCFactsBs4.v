(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM BzCBlock BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 BzCLemmasMs4 BzCSewF BzCSewH.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Definition setcs (s : mss) (cs' ce' : zarr) : mss :=
  MSS (s_a1 s) (s_a2 s) (s_ft s) (s_bd s) cs' ce' (s_budget s) (s_nqs s) (s_mql s) (s_exit s).

Lemma ms_step1_csce : forall n qoff nb ss j s cs' ce',
  ms_step1 n qoff nb ss j (setcs s cs' ce') = setcs (ms_step1 n qoff nb ss j s) cs' ce'.
Proof.
  induction n as [|n IH]; intros qoff nb ss j s cs' ce'; [reflexivity|].
  destruct s as [a1 a2 ft bd cs ce b nqs mql ex]. unfold setcs at 1. cbn [s_a1 s_a2 s_ft s_bd s_budget s_nqs s_mql s_exit].
  rewrite !ms_step1_S. cbn [s_a1 s_a2 s_ft s_bd s_cs s_ce s_budget s_nqs s_mql s_exit].
  destruct ex; [reflexivity|].
  destruct (j =? ss). { etransitivity; [| apply IH]. reflexivity. }
  cbv zeta.
  destruct (negb (has_setmask (zget ft (Z.shiftl ss 8 + j)))).
  - destruct (clearmask (zget ft (Z.shiftl ss 8 + j)) <? clearmask (zget ft (Z.shiftl ss 8 + j + 1)) - 1).
    + destruct (mainQSort3 _ _ _ _ _ _ _ _ _) as [[a1' budget] mql'].
      destruct (budget <? 0); [reflexivity|].
      cbn [s_a1 s_a2 s_ft s_bd s_cs s_ce s_budget s_nqs s_mql s_exit].
      etransitivity; [| apply IH]. reflexivity.
    + cbn [s_a1 s_a2 s_ft s_bd s_cs s_ce s_budget s_nqs s_mql s_exit]. etransitivity; [| apply IH]. reflexivity.
  - cbn [s_a1 s_a2 s_ft s_bd s_cs s_ce s_budget s_nqs s_mql s_exit]. etransitivity; [| apply IH]. reflexivity.
Qed.

Definition AG256 (a b : zarr) : Prop := forall c, 0 <= c < 256 -> zget a c = zget b c.

Lemma ms_copy_init_AG : forall n cs cs' ce ce' ft ss j, 0 <= j -> j + Z.of_nat n = 256 ->
  (forall c, 0 <= c < j -> zget cs c = zget cs' c /\ zget ce c = zget ce' c) ->
  AG256 (fst (ms_copy_init n cs ce ft ss j)) (fst (ms_copy_init n cs' ce' ft ss j)) /\
  AG256 (snd (ms_copy_init n cs ce ft ss j)) (snd (ms_copy_init n cs' ce' ft ss j)).
Proof.
  induction n as [|n IH]; intros cs cs' ce ce' ft ss j Hj Hn AG.
  - cbn [ms_copy_init fst snd]. cbn in Hn. split; intros c Hc; apply (AG c); lia.
  - rewrite !ms_copy_init_S. apply IH; [lia| lia|].
    intros c Hc. rewrite !zget_zset. destruct (Z.eqb_spec c j); [split; reflexivity|]. apply AG. lia.
Qed.

Lemma ms_copy_fwd_AG : forall f a1 cs cs' a2 bd nb ss j, zbok a2 -> 0 <= ss < 256 -> AG256 cs cs' ->
  let r := ms_copy_fwd f a1 cs a2 bd nb ss j in let r' := ms_copy_fwd f a1 cs' a2 bd nb ss j in
  fst (fst r') = fst (fst r) /\ snd r' = snd r /\ AG256 (snd (fst r)) (snd (fst r')).
Proof.
  induction f as [|f IH]; intros a1 cs cs' a2 bd nb ss j B SS AG; cbv zeta.
  - cbn [ms_copy_fwd fst snd]. repeat split; try reflexivity. exact AG.
  - rewrite !BzCLemmasMs3.ms_copy_fwd_S. rewrite <- (AG ss SS).
    destruct (j <? zget cs ss); [| cbn [fst snd]; repeat split; try reflexivity; exact AG].
    cbv zeta. unfold kwrap. set (k := if rd32 a1 j - 1 <? 0 then rd32 a1 j - 1 + nb else rd32 a1 j - 1).
    pose proof (B k) as Bk. change (zget a2 k) with (rd8 a2 k) in Bk. set (c1 := rd8 a2 k) in *.
    rewrite <- (AG c1 Bk).
    destruct (zget bd c1 =? 0).
    + apply IH; [exact B| exact SS|]. intros c Hc. rewrite !zget_zset. destruct (c =? c1); [reflexivity| apply AG; exact Hc].
    + apply IH; assumption.
Qed.

Lemma ms_copy_bwd_AG : forall f a1 ce ce' a2 bd nb ss j, zbok a2 -> 0 <= ss < 256 -> AG256 ce ce' ->
  let r := ms_copy_bwd f a1 ce a2 bd nb ss j in let r' := ms_copy_bwd f a1 ce' a2 bd nb ss j in
  fst (fst r') = fst (fst r) /\ snd r' = snd r /\ AG256 (snd (fst r)) (snd (fst r')).
Proof.
  induction f as [|f IH]; intros a1 ce ce' a2 bd nb ss j B SS AG; cbv zeta.
  - cbn [ms_copy_bwd fst snd]. repeat split; try reflexivity. exact AG.
  - rewrite !BzCLemmasMs3.ms_copy_bwd_S. rewrite <- (AG ss SS).
    destruct (zget ce ss <? j); [| cbn [fst snd]; repeat split; try reflexivity; exact AG].
    cbv zeta. unfold kwrap. set (k := if rd32 a1 j - 1 <? 0 then rd32 a1 j - 1 + nb else rd32 a1 j - 1).
    pose proof (B k) as Bk. change (zget a2 k) with (rd8 a2 k) in Bk. set (c1 := rd8 a2 k) in *.
    rewrite <- (AG c1 Bk).
    destruct (zget bd c1 =? 0).
    + apply IH; [exact B| exact SS|]. intros c Hc. rewrite !zget_zset. destruct (c =? c1); [reflexivity| apply AG; exact Hc].
    + apply IH; assumption.
Qed.

Lemma ms_step1_a2 : forall n qoff nb ss j s, s_a2 (ms_step1 n qoff nb ss j s) = s_a2 s.
Proof.
  induction n as [|n IH]; intros; [reflexivity|]. rewrite ms_step1_S.
  destruct (s_exit s); [reflexivity|]. destruct (j =? ss); [apply IH|]. cbv zeta.
  destruct (negb _).
  - destruct (_ <? _).
    + destruct (mainQSort3 _ _ _ _ _ _ _ _ _) as [[a1 b] m]. destruct (b <? 0); [reflexivity|]. rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ms_big_csce : forall ro qoff nb i s cs' ce', zbok (s_a2 s) -> 0 <= zget ro i < 256 ->
  exists cs'' ce'', ms_big ro qoff nb i (setcs s cs' ce') = setcs (ms_big ro qoff nb i s) cs'' ce''.
Proof.
  intros ro qoff nb i s cs' ce' B SS. rewrite !ms_big_eq. cbv zeta.
  rewrite ms_step1_csce. set (s1 := ms_step1 256 qoff nb (zget ro i) 0 s).
  assert (B1 : zbok (s_a2 s1)) by (subst s1; rewrite ms_step1_a2; exact B).
  clearbody s1.
  unfold setcs. cbn [s_a1 s_a2 s_ft s_bd s_cs s_ce s_budget s_nqs s_mql s_exit].
  destruct (s_exit s1) eqn:EX.
  { exists cs', ce'. unfold setcs. rewrite EX. reflexivity. }
  pose proof (ms_copy_init_AG 256 (s_cs s1) cs' (s_ce s1) ce' (s_ft s1) (zget ro i) 0 ltac:(lia) ltac:(reflexivity) ltac:(intros; lia)) as [AC AE].
  destruct (ms_copy_init 256 (s_cs s1) (s_ce s1) (s_ft s1) (zget ro i) 0) as [cs0 ce0].
  destruct (ms_copy_init 256 cs' ce' (s_ft s1) (zget ro i) 0) as [cs0' ce0']. cbn [fst snd] in AC, AE.
  pose proof (ms_copy_fwd_AG (S (Z.to_nat nb)) (s_a1 s1) cs0 cs0' (s_a2 s1) (s_bd s1) nb (zget ro i) (clearmask (zget (s_ft s1) (Z.shiftl (zget ro i) 8))) B1 SS AC) as F.
  cbv zeta in F. destruct (ms_copy_fwd _ _ cs0 _ _ _ _ _) as [[af csf] jf]. destruct (ms_copy_fwd _ _ cs0' _ _ _ _ _) as [[af' csf'] jf'].
  cbn [fst snd] in F. cps_destruct F as (-> & -> & ACF).
  pose proof (ms_copy_bwd_AG (S (Z.to_nat nb)) af ce0 ce0' (s_a2 s1) (s_bd s1) nb (zget ro i) (clearmask (zget (s_ft s1) (Z.shiftl (zget ro i + 1) 8)) - 1) B1 SS AE) as Bk.
  cbv zeta in Bk. destruct (ms_copy_bwd _ _ ce0 _ _ _ _ _) as [[ab ceb] jb]. destruct (ms_copy_bwd _ _ ce0' _ _ _ _ _) as [[ab' ceb'] jb'].
  cbn [fst snd] in Bk. cps_destruct Bk as (-> & -> & ACB).
  exists csf', ceb'. unfold setcs. cbn [s_a1 s_a2 s_ft s_bd s_cs s_ce s_budget s_nqs s_mql s_exit]. reflexivity.
Qed.

Lemma ms_bigs_csce : forall n ro qoff nb i s cs' ce', zbok (s_a1 s) -> zbok (s_a2 s) -> (forall k, 0 <= k < 256 -> 0 <= zget ro k < 256) ->
  0 <= i -> i + Z.of_nat n <= 256 ->
  exists cs'' ce'', ms_bigs n ro qoff nb i (setcs s cs' ce') = setcs (ms_bigs n ro qoff nb i s) cs'' ce''.
Proof.
  induction n as [|n IH]; intros ro qoff nb i s cs' ce' B1 B2 RO Hi Hn.
  - exists cs', ce'. reflexivity.
  - rewrite !ms_bigs_S.
    cps_destruct (ms_big_csce ro qoff nb i s cs' ce' B2 (RO i ltac:(lia))) as (cs1 & ce1 & E). rewrite E. clear E.
    destruct (zbok_big ro qoff nb i s B1 B2) as [B1' B2'].
    set (X := ms_big ro qoff nb i s) in *. clearbody X.
    destruct X as [xa1 xa2 xft xbd xcs xce xb xnqs xmql xex]. unfold setcs at 1 2. cbn [s_a1 s_a2 s_ft s_bd s_cs s_ce s_budget s_nqs s_mql s_exit].
    destruct xex.
    + exists cs1, ce1. reflexivity.
    + cps_destruct (IH ro qoff nb (i + 1) (MSS xa1 xa2 xft xbd xcs xce xb xnqs xmql false) cs1 ce1 B1' B2' RO ltac:(lia) ltac:(lia)) as (cs2 & ce2 & E2).
      exists cs2, ce2. unfold setcs in E2 at 1. cbn [s_a1 s_a2 s_ft s_bd s_cs s_ce s_budget s_nqs s_mql s_exit] in E2. exact E2.
Qed.
