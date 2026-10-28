(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCState BzCPermF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM BzCBlock BzCPermM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewF BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 BzCLemmasMs4 BzCLemmasMs5 BzCFactsBs BzCFactsBs2 BzCFactsBs3.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs3.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


Section Main.
  Variables (a2 : zarr) (nb qoff : Z) (ro : zarr) (a2x : zarr).
  Hypothesis BB : forall i, 0 <= rd8 a2 i < 256.
  Hypothesis NB : 34 <= nb <= 899990.
  Hypothesis QO : nb + 34 <= qoff.
  Hypothesis RO : forall i, 0 <= i < 256 -> 0 <= zget ro i < 256.
  Hypothesis ROinj : forall i i', 0 <= i < 256 -> 0 <= i' < 256 -> zget ro i = zget ro i' -> i = i'.
  Hypothesis AX : forall k, 0 <= k < nb -> rd8 a2x k = rd8 a2 k.
  Hypothesis BOV : forall z, nb <= z < nb + 34 -> rd8 a2x z = rd8 a2x (z - nb).
  Local Notation CLM := (ClM a2 nb).
  Lemma NB1' : 1 <= nb <= 2097151. Proof. lia. Qed.
  Lemma NB2' : nb <= 1000000. Proof. lia. Qed.

  (* [comment removed for export] *)
  Lemma step1_nqs : forall n ss j s, 0 <= ss < 256 -> 0 <= j -> j + Z.of_nat n <= 256 -> FT a2 nb (s_ft s) ->
    let s' := ms_step1 n qoff nb ss j s in
    s_nqs s <= s_nqs s' <= s_nqs s + (CLM (256 * ss + j + Z.of_nat n) - CLM (256 * ss + j)).
  Proof.
    induction n as [|n IH]; intros ss j s Hss Hj Hn F; cbv zeta.
    - cbn [ms_step1]. rewrite Z.add_0_r. lia.
    - rewrite ms_step1_S.
      pose proof (ClM_mono a2 nb (256 * ss + j) (256 * ss + j + Z.of_nat (S n)) ltac:(lia)) as M0.
      destruct (s_exit s); [lia|].
      destruct (Z.eqb_spec j ss) as [->|NE].
      { specialize (IH ss (ss + 1) s Hss ltac:(lia) ltac:(lia) F). cbv zeta in IH.
        pose proof (ClM_mono a2 nb (256 * ss + ss) (256 * ss + (ss + 1)) ltac:(lia)).
        replace (256 * ss + (ss + 1) + Z.of_nat n) with (256 * ss + ss + Z.of_nat (S n)) in IH by lia. lia. }
      cbv zeta. rewrite shl8.
      cps_pose (FT_lohi a2 nb NB1' NB2' (s_ft s) (256 * ss + j) F ltac:(lia)) as (C1 & C2 & R1 & R2). rewrite C1, C2.
      set (sb := 256 * ss + j) in *.
      pose proof (ClM_mono a2 nb sb (sb + 1) ltac:(lia)) as M1.
      pose proof (ClM_mono a2 nb (sb + 1) (sb + Z.of_nat (S n)) ltac:(lia)) as M2.
      assert (FM : forall ft, FT a2 nb ft -> FT a2 nb (zset ft sb (Z.lor (zget ft sb) SETMASK))).
      { intros ft F1 v Hv. rewrite zget_zset. destruct (Z.eqb_spec v sb) as [->|NV]; [apply ftcell_mark|]; apply F1; lia. }
      assert (CONT : forall s1, s_ft s1 = s_ft s -> s_nqs s <= s_nqs s1 <= s_nqs s + (CLM (sb + 1) - CLM sb) ->
        let s' := ms_step1 n qoff nb ss (j + 1)
                    (MSS (s_a1 s1) (s_a2 s1) (zset (s_ft s1) sb (Z.lor (zget (s_ft s1) sb) SETMASK)) (s_bd s1) (s_cs s1) (s_ce s1)
                         (s_budget s1) (s_nqs s1) (s_mql s1) false) in
        s_nqs s <= s_nqs s' <= s_nqs s + (CLM (sb + Z.of_nat (S n)) - CLM sb)).
      { intros s1 EF B1. cbv zeta.
        match goal with |- context [ms_step1 n qoff nb ss (j + 1) ?s2] =>
          specialize (IH ss (j + 1) s2 Hss ltac:(lia) ltac:(lia) ltac:(cbn [s_ft]; rewrite EF; apply FM; exact F)) end.
        cbv zeta in IH. cbn [s_nqs] in IH.
        replace (256 * ss + (j + 1) + Z.of_nat n) with (sb + Z.of_nat (S n)) in IH by lia.
        replace (256 * ss + (j + 1)) with (sb + 1) in IH by lia. lia. }
      destruct (negb (has_setmask (zget (s_ft s) sb))).
      + destruct (Z.ltb_spec (CLM sb) (CLM (sb + 1) - 1)) as [LT|GE].
        * destruct (mainQSort3 _ _ _ _ _ _ _ _ _) as [[a1 budget] mql].
          destruct (Z.ltb_spec budget 0) as [BL|BG].
          -- cbn [s_nqs]. lia.
          -- apply (CONT (MSS a1 (s_a2 s) (s_ft s) (s_bd s) (s_cs s) (s_ce s) budget (s_nqs s + (CLM (sb + 1) - 1 - CLM sb + 1)) mql false));
               [reflexivity| cbn [s_nqs]; lia].
        * apply CONT; [reflexivity| lia].
      + apply CONT; [reflexivity| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma big_nqs : forall i s, 0 <= i < 256 -> FT a2 nb (s_ft s) -> s_exit (ms_big ro qoff nb i s) = false ->
    s_nqs s <= s_nqs (ms_big ro qoff nb i s) <= s_nqs s + nb.
  Proof.
    intros i s Hi F. rewrite ms_big_eq. cbv zeta.
    pose proof (RO i Hi) as Hss.
    pose proof (step1_nqs 256 (zget ro i) 0 s Hss ltac:(lia) ltac:(cbn; lia) F) as B. cbv zeta in B.
    pose proof (ClM_range a2 nb ltac:(lia) (256 * zget ro i + 0 + Z.of_nat 256)) as G1.
    pose proof (ClM_range a2 nb ltac:(lia) (256 * zget ro i + 0)) as G0.
    set (s1 := ms_step1 256 qoff nb (zget ro i) 0 s) in *. clearbody s1.
    destruct (s_exit s1) eqn:EX. { rewrite EX. discriminate. }
    destruct (ms_copy_init _ _ _ _ _ _) as [cs ce]. destruct (ms_copy_fwd _ _ _ _ _ _ _ _) as [[a1 cs0] j1].
    destruct (ms_copy_bwd _ _ _ _ _ _ _ _) as [[a3 ce0] j2]. cbn [s_nqs s_exit]. intros _. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bigs_nqs : forall k i s, 0 <= i -> i + Z.of_nat k <= 256 -> MI2 a2 nb qoff ro a2x i s ->
    0 <= s_nqs s <= i * nb ->
    s_exit (ms_bigs k ro qoff nb i s) = false ->
    0 <= s_nqs (ms_bigs k ro qoff nb i s) <= (i + Z.of_nat k) * nb /\
    (i + Z.of_nat k < 256 -> MI2 a2 nb qoff ro a2x (i + Z.of_nat k) (ms_bigs k ro qoff nb i s)).
  Proof.
    induction k as [|k IH]; intros i s Hi Hk M B EX.
    - cbn [ms_bigs] in *. rewrite Z.add_0_r. split; [lia| intros; exact M].
    - rewrite ms_bigs_S in *. cbv zeta in EX. cbv zeta.
      destruct (s_exit (ms_big ro qoff nb i s)) eqn:EXb; [cbn in EX; congruence|].
      pose proof (big_next a2 nb qoff ro a2x BB NB QO RO ROinj AX i s ltac:(lia) M EXb) as M'.
      pose proof (big_nqs i s ltac:(lia) (mi_ft _ _ _ _ _ _ (proj1 M)) EXb) as Bn.
      replace (i + Z.of_nat (S k)) with (i + 1 + Z.of_nat k) by lia.
      apply (IH (i + 1) _ ltac:(lia) ltac:(lia) M'); [lia| exact EX].
  Qed.

  Theorem bigN_ok : forall s, MI2 a2 nb qoff ro a2x 0 s -> s_nqs s = 0 -> forall k, (k < 256)%nat ->
    s_exit (ms_bigs k ro qoff nb 0 s) = false -> bigN qoff nb ro (0 + Z.of_nat k) (ms_bigs k ro qoff nb 0 s).
  Proof.
    intros s M0 N0 k Hk EX.
    destruct (bigs_nqs k 0 s ltac:(lia) ltac:(lia) M0 ltac:(lia) EX) as [B M]. specialize (M ltac:(lia)).
    set (s' := ms_bigs k ro qoff nb 0 s) in *. clearbody s'.
    intros k' Hk'. cbv zeta. intros EX'. unfold step1N.
    pose proof (RO (0 + Z.of_nat k) ltac:(lia)) as Hss.
    pose proof (step1_nqs k' (zget ro (0 + Z.of_nat k)) 0 s' Hss ltac:(lia) ltac:(lia) (mi_ft _ _ _ _ _ _ (proj1 M))) as B'.
    cbv zeta in B'.
    pose proof (ClM_range a2 nb ltac:(lia) (256 * zget ro (0 + Z.of_nat k) + 0 + Z.of_nat k')) as G1.
    pose proof (ClM_range a2 nb ltac:(lia) (256 * zget ro (0 + Z.of_nat k) + 0)) as G0.
    nia.
  Qed.
End Main.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section E.
  Variable e : est.
  Hypothesis BB : zbok (e_arr2 e).
  Hypothesis NB : 34 <= e_nblock e <= 899990.

  Theorem bsB_bigN_ok : forall cs ce nl nh nd k, (k < 256)%nat ->
    let s' := ms_bigs k (bp_ro6 e) (bp_qoff e) (bp_n e) 0
                (MSS (bp_a1r e) (bp_a2o e) (bp_ft4 e) bp_bd5 cs ce (bp_budget0 e) 0 (MQL znew znew znew nl nh nd) false) in
    s_exit s' = false -> bigN (bp_qoff e) (bp_n e) (bp_ro6 e) (0 + Z.of_nat k) s'.
  Proof.
    pose proof (NBq e NB) as NB'. intros cs ce nl nh nd k Hk. cbv zeta. intros EX.
    cps_destruct (pt_ro e) as (BD0 & ROR & ROI). cps_destruct (pt_a2o_facts e BB NB) as (AX & BOV & QOV0).
    exact (bigN_ok (bp_a2 e) (bp_n e) (bp_qoff e) (bp_ro6 e) (bp_a2o e) (BBr e BB) NB' (QO e) ROR ROI AX
             _ (MI2_init e BB NB cs ce nl nh nd) eq_refl k Hk EX).
  Qed.
End E.

End ACeilS1.
