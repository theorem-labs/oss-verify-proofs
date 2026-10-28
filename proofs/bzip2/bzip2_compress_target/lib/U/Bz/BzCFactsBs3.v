(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCPermF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCPermM BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 BzCLemmasMs4 BzCFactsBs BzCFactsBs2 BzCSortPost BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC BzCSewD BzCSewE BzCSewF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewH.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasMs2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCQsortM1 BzCQsortM2.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortPost OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewG OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewH OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2.BzCFactsMs3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qrd_qwr_same0 : forall a qoff i, qrd (qwr a qoff i 0) qoff i = 0.
Proof. intros. unfold qrd, qwr. apply rd16_wr16_same. lia. Qed.
Lemma qrd_qwr_other : forall a qoff i v k, i <> k -> qrd (qwr a qoff i v) qoff k = qrd a qoff k.
Proof. intros a qoff i v k NE. unfold qrd, qwr. apply rd16_wr16_other. lia. Qed.
Lemma qrd_wr8_low : forall a qoff p v k, p < qoff -> 0 <= k -> qrd (wr8 a p v) qoff k = qrd a qoff k.
Proof. intros a qoff p v k Hp Hk. unfold qrd, rd16, wr8. rewrite !zget_zset_other by lia. reflexivity. Qed.
Lemma rd8_wr8 : forall a p v k, rd8 (wr8 a p v) k = if k =? p then v mod 256 else rd8 a k.
Proof. intros. unfold rd8, wr8. apply zget_zset. Qed.
Lemma zbok_rd8_mod : forall a k, zbok a -> rd8 a k mod 256 = rd8 a k.
Proof. intros a k B. apply Z.mod_small. unfold rd8. apply B. Qed.
Lemma rd16_wr16_same_mod' : forall a o v, rd16 (wr16 a o v) o = v mod 65536.
Proof.
  intros a o v. unfold rd16, wr16. rewrite zget_zset_other by lia. rewrite !zget_zset_same.
  rewrite (Z.div_mod v 256) at 3 by lia.
  change 65536 with (256 * 256). rewrite Z.rem_mul_r by lia.
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)). pose proof (Z.mod_pos_bound (v / 256) 256 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma ms_radix1_quad : forall n a ft qoff i j, 0 <= i + 1 - Z.of_nat n ->
  let a' := fst (fst (ms_radix1 n a ft qoff i j)) in
  (forall z, i + 1 - Z.of_nat n <= z <= i -> qrd a' qoff z = 0) /\
  (forall z, 0 <= z -> (z < i + 1 - Z.of_nat n \/ i < z) -> qrd a' qoff z = qrd a qoff z).
Proof.
  induction n as [|n IH]; intros a ft qoff i j Hn; cbv zeta.
  - cbn [ms_radix1 fst]. split; [intros; lia| intros; reflexivity].
  - cbn [ms_radix1]. destruct (IH (qwr a qoff i 0) (zincr ft (Z.lor (Z.shiftr j 8) (Z.shiftl (rd8 (qwr a qoff i 0) i) 8))) qoff (i - 1)
                               (Z.lor (Z.shiftr j 8) (Z.shiftl (rd8 (qwr a qoff i 0) i) 8)) ltac:(lia)) as [Z1 F1].
    split.
    + intros z Hz. destruct (Z.eq_dec z i) as [->|NE].
      * rewrite F1 by lia. apply qrd_qwr_same0.
      * apply Z1. lia.
    + intros z Hz Hz'. rewrite F1 by lia. apply qrd_qwr_other. lia.
Qed.

(* [comment removed for export] *)
Lemma ms_overshoot_spec : forall n a qoff nb i, zbok a -> 0 <= i -> nb + Z.of_nat n + i <= qoff -> Z.of_nat n + i <= nb -> 34 <= nb ->
  let a' := ms_overshoot n a qoff nb i in
  (forall z, i <= z < i + Z.of_nat n -> rd8 a' (nb + z) = rd8 a z /\ qrd a' qoff (nb + z) = 0) /\
  (forall k, 0 <= k < nb -> rd8 a' k = rd8 a k) /\
  (forall z, 0 <= z -> (z < nb + i \/ nb + i + Z.of_nat n <= z) -> qrd a' qoff z = qrd a qoff z) /\
  (forall k, nb <= k < nb + i -> rd8 a' k = rd8 a k).
Proof.
  induction n as [|n IH]; intros a qoff nb i B Hi Hq Hn H34; cbv zeta.
  - cbn [ms_overshoot]. split; [intros; lia|]. split; [intros; reflexivity|]. split; intros; reflexivity.
  - rewrite ms_overshoot_S.
    set (a1 := qwr (wr8 a (nb + i) (rd8 a i)) qoff (nb + i) 0).
    assert (B1 : zbok a1) by (subst a1; apply zbok_qwr, zbok_wr8; exact B).
    cps_destruct (IH a1 qoff nb (i + 1) B1 ltac:(lia) ltac:(lia) ltac:(lia) H34) as (C & L & Q & M).
    assert (La1 : forall k, k < qoff -> k <> nb + i -> rd8 a1 k = rd8 a k).
    { intros k Hk Hk'. subst a1. unfold qwr, rd8, wr16, wr8. rewrite !zget_zset_other by lia. reflexivity. }
    assert (Ha1 : rd8 a1 (nb + i) = rd8 a i).
    { subst a1. unfold qwr, wr16. unfold rd8 at 1. rewrite !zget_zset_other by lia. fold (rd8 (wr8 a (nb + i) (rd8 a i)) (nb + i)).
      rewrite rd8_wr8, Z.eqb_refl. apply zbok_rd8_mod. exact B. }
    assert (Qa1 : forall z, 0 <= z -> z <> nb + i -> qrd a1 qoff z = qrd a qoff z).
    { intros z Hz Hz'. subst a1. rewrite qrd_qwr_other by lia. apply qrd_wr8_low; lia. }
    assert (Qhit : qrd a1 qoff (nb + i) = 0) by (subst a1; apply qrd_qwr_same0).
    split; [| split; [| split]].
    + intros z Hz. destruct (Z.eq_dec z i) as [->|NE].
      * split; [rewrite M by lia; exact Ha1| rewrite Q by lia; exact Qhit].
      * destruct (C z ltac:(lia)) as [C1 C2]. split; [rewrite C1; apply La1; lia| exact C2].
    + intros k Hk. rewrite L by lia. apply La1; lia.
    + intros z Hz Hz'. rewrite Q by lia. apply Qa1; lia.
    + intros k Hk. rewrite M by lia. apply La1; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Main.
  Variables (a2 : zarr) (nb qoff : Z) (ro : zarr) (a2x : zarr).
  Hypothesis BB : forall i, 0 <= rd8 a2 i < 256.
  Hypothesis NB : 34 <= nb <= 899990.
  Hypothesis QO : nb + 34 <= qoff.
  Hypothesis RO : forall i, 0 <= i < 256 -> 0 <= zget ro i < 256.
  Hypothesis ROinj : forall i i', 0 <= i < 256 -> 0 <= i' < 256 -> zget ro i = zget ro i' -> i = i'.
  Hypothesis AX : forall k, 0 <= k < nb -> rd8 a2x k = rd8 a2 k.
  Hypothesis BOV : forall z, nb <= z < nb + 34 -> rd8 a2x z = rd8 a2x (z - nb).

  (* [comment removed for export] *)
  Definition QOV (a : zarr) : Prop := forall z, nb <= z < nb + 34 -> qrd a qoff z = qrd a qoff (z - nb).
  Definition MI2 (i : Z) (s : mss) : Prop := MI a2 nb ro a2x i s /\ QOV (s_a2 s).

  Lemma NB1 : 1 <= nb <= 2097151. Proof. lia. Qed.
  Lemma NB2 : nb <= 1000000. Proof. lia. Qed.
  Local Notation CLM := (ClM a2 nb).

  (* [comment removed for export] *)
  Lemma F1_ok : forall i s, 0 <= i < 256 -> MI2 i s ->
    forall k, (k < 256)%nat -> let s' := ms_step1 k qoff nb (zget ro i) 0 s in s_exit s' = false -> step1F qoff nb (zget ro i) (0 + Z.of_nat k) s'.
  Proof.
    intros i s Hi [IV QV] k Hk. cbv zeta. intros EX.
    pose proof (RO i Hi) as Hss. set (ss := zget ro i) in *.
    pose proof (ms_step1_inv a2 nb qoff BB NB1 NB2 k ss 0 s s Hss ltac:(lia) ltac:(lia)
                  (conj (mi_pinv _ _ _ _ _ _ IV) (conj (mi_ft _ _ _ _ _ _ IV) (conj eq_refl eq_refl)))) as S1.
    set (s' := ms_step1 k qoff nb ss 0 s) in *. cps_destruct S1 as (P1 & FT1 & EA1 & EB1).
    unfold step1F. intros NE. cbv zeta. rewrite shl8.
    set (sb := 256 * ss + (0 + Z.of_nat k)).
    pose proof (ClM_range a2 nb ltac:(lia) sb) as G0. pose proof (ClM_range a2 nb ltac:(lia) (sb + 1)) as G1.
    pose proof (ClM_mono a2 nb sb (sb + 1) ltac:(lia)) as GM.
    exists (CLM sb), (CLM (sb + 1)).
    split; [lia|]. split; [lia|]. split; [apply FT1; lia|]. split; [apply FT1; lia|].
    intros UNM LT. cbv zeta.
    apply (mqs_facts (s_a2 s') qoff nb (CLM sb) (CLM (sb + 1) - 1)); try lia.
    - intros z Hz. rewrite EA1. rewrite !(mi_a2 _ _ _ _ _ _ IV) by lia. apply BOV. exact Hz.
    - intros z Hz. rewrite EA1. apply QV. exact Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma fwd_prefix : forall ss bd P0 a2r, 0 <= ss < 256 -> zget bd ss = 0 -> PINV a2 nb P0 -> NALL a2 nb ss ->
    (forall k, 0 <= k < nb -> rd8 a2r k = rd8 a2 k) ->
    forall k a1 cs j, FWI a2 nb ss bd P0 a1 cs j ->
    let r := ms_copy_fwd k a1 cs a2r bd nb ss j in FWI a2 nb ss bd P0 (fst (fst r)) (snd (fst r)) (snd r).
  Proof.
    intros ss bd P0 a2r SS BD P0X NA AGR.
    induction k as [|k IH]; intros a1 cs j IV; cbv zeta; [exact IV|].
    rewrite BzCLemmasMs3.ms_copy_fwd_S. destruct (Z.ltb_spec j (zget cs ss)) as [LT|GE]; [| exact IV].
    pose proof (FWI_step a2 nb ss bd P0 BB NB1 SS BD P0X NA a1 cs j IV LT) as ST. cbv zeta in ST.
    cps_destruct ST as (Ru & Rk & Rc & Kk & CASE0 & CASE1).
    cbv zeta. unfold kwrap. rewrite (prv_model' nb NB1 (rd32 a1 j) Ru). rewrite (AGR (prv nb (rd32 a1 j)) Rk).
    destruct (Z.eqb_spec (zget bd (rd8 a2 (prv nb (rd32 a1 j)))) 0) as [Bz|Bnz].
    - destruct (CASE0 Bz) as [_ IV']. apply (IH _ _ (j + 1) IV').
    - apply (IH a1 cs (j + 1) (CASE1 Bnz)).
  Qed.

  Lemma fwdF_of_FWI : forall ss bd P0 a2r a1 cs j, 0 <= ss < 256 -> zget bd ss = 0 -> PINV a2 nb P0 -> NALL a2 nb ss ->
    (forall k, 0 <= k < nb -> rd8 a2r k = rd8 a2 k) ->
    FWI a2 nb ss bd P0 a1 cs j -> fwdF a2r bd nb ss a1 cs j.
  Proof.
    intros ss bd P0 a2r a1 cs j SS BD P0X NA AGR IV. split.
    - intros c Hc. pose proof (fw0 _ _ _ _ _ _ _ _ IV c Hc) as [L E]. pose proof (cs0_ge_0 a2 nb ss NB1 c).
      pose proof (ClM_range a2 nb ltac:(lia) (256 * c + ss)) as CR. unfold BzCSewC.cs0 in *.
      destruct (Z.eq_dec (zget bd c) 0) as [Bc|Bc].
      + pose proof (proj2 (fw_bound a2 nb ss bd P0 BB NB1 SS NA a1 cs j IV c Hc Bc)). pose proof (ce1_le_nb a2 nb ss NB1 c). lia.
      + rewrite (E Bc). lia.
    - intros LT. pose proof (fw1 _ _ _ _ _ _ _ _ IV) as J. pose proof (ClM_range a2 nb ltac:(lia) (256 * ss)) as B0R. unfold BzCSewC.B0 in J.
      pose proof (proj2 (fw_bound a2 nb ss bd P0 BB NB1 SS NA a1 cs j IV ss SS BD)). pose proof (ce1_le_nb a2 nb ss NB1 ss).
      split; [lia|]. cbv zeta.
      pose proof (FWI_step a2 nb ss bd P0 BB NB1 SS BD P0X NA a1 cs j IV LT) as ST. cbv zeta in ST.
      cps_destruct ST as (Ru & Rk & Rc & Kk & CASE0 & _).
      unfold kwrap. rewrite (prv_model' nb NB1 (rd32 a1 j) Ru). rewrite (AGR (prv nb (rd32 a1 j)) Rk).
      intros Bz. destruct (CASE0 Bz) as [FIT _]. pose proof (ce1_le_nb a2 nb ss NB1 (rd8 a2 (prv nb (rd32 a1 j)))). lia.
  Qed.

  Lemma bwd_prefix : forall ss bd P0 A0 csA a2r, 0 <= ss < 256 -> zget bd ss = 0 -> PINV a2 nb P0 -> NALL a2 nb ss ->
    FWPOST a2 nb ss bd P0 A0 csA ->
    (forall k, 0 <= k < nb -> rd8 a2r k = rd8 a2 k) ->
    forall k a1 ce j, BWI a2 nb ss bd A0 a1 ce j ->
    let r := ms_copy_bwd k a1 ce a2r bd nb ss j in BWI a2 nb ss bd A0 (fst (fst r)) (snd (fst r)) (snd r).
  Proof.
    intros ss bd P0 A0 csA a2r SS BD P0X NA FW AGR.
    induction k as [|k IH]; intros a1 ce j IV; cbv zeta; [exact IV|].
    rewrite BzCLemmasMs3.ms_copy_bwd_S. destruct (Z.ltb_spec (zget ce ss) j) as [LT|GE]; [| exact IV].
    pose proof (BWI_step a2 nb ss bd P0 A0 csA BB NB1 SS BD P0X NA FW a1 ce j IV LT) as ST. cbv zeta in ST.
    cps_destruct ST as (Ru & Rk & Rc & Kk & CASE0 & CASE1).
    cbv zeta. unfold kwrap. rewrite (prv_model' nb NB1 (rd32 a1 j) Ru). rewrite (AGR (prv nb (rd32 a1 j)) Rk).
    destruct (Z.eqb_spec (zget bd (rd8 a2 (prv nb (rd32 a1 j)))) 0) as [Bz|Bnz].
    - destruct (CASE0 Bz) as [_ IV']. apply (IH _ _ (j - 1) IV').
    - apply (IH a1 ce (j - 1) (CASE1 Bnz)).
  Qed.

  Lemma bwdF_of_BWI : forall ss bd P0 A0 csA a2r a1 ce j, 0 <= ss < 256 -> zget bd ss = 0 -> PINV a2 nb P0 -> NALL a2 nb ss ->
    FWPOST a2 nb ss bd P0 A0 csA ->
    (forall k, 0 <= k < nb -> rd8 a2r k = rd8 a2 k) ->
    BWI a2 nb ss bd A0 a1 ce j -> bwdF a2r bd nb ss a1 ce j.
  Proof.
    intros ss bd P0 A0 csA a2r a1 ce j SS BD P0X NA FW AGR IV. split.
    - intros c Hc. cps_pose (bw0 _ _ _ _ _ _ _ _ IV c Hc) as (L & E & G). pose proof (ce1_le_nb a2 nb ss NB1 c).
      pose proof (csF_le_ce1 a2 nb ss BB NB1 SS NA c Hc). pose proof (cs0_ge_0 a2 nb ss NB1 c).
      destruct (Z.eq_dec (zget bd c) 0) as [Bc|Bc].
      + pose proof (G Bc). lia.
      + rewrite (E Bc). lia.
    - intros LT. pose proof (bw1 _ _ _ _ _ _ _ _ IV) as J. pose proof (ClM_range a2 nb ltac:(lia) (256 * (ss + 1))) as B1R. unfold BzCSewC.B1 in J.
      cps_pose (bw0 _ _ _ _ _ _ _ _ IV ss SS) as (_ & _ & G). pose proof (csF_le_ce1 a2 nb ss BB NB1 SS NA ss SS). pose proof (cs0_ge_0 a2 nb ss NB1 ss).
      split; [pose proof (G BD); lia|]. cbv zeta.
      pose proof (BWI_step a2 nb ss bd P0 A0 csA BB NB1 SS BD P0X NA FW a1 ce j IV LT) as ST. cbv zeta in ST.
      cps_destruct ST as (Ru & Rk & Rc & Kk & CASE0 & _).
      unfold kwrap. rewrite (prv_model' nb NB1 (rd32 a1 j) Ru). rewrite (AGR (prv nb (rd32 a1 j)) Rk).
      intros Bz. destruct (CASE0 Bz) as [FIT _]. pose proof (csF_le_ce1 a2 nb ss BB NB1 SS NA _ Rc). pose proof (cs0_ge_0 a2 nb ss NB1 (rd8 a2 (prv nb (rd32 a1 j)))). lia.
  Qed.

  Lemma ftv_of_FT : forall ft, FT a2 nb ft -> ftv ft.
  Proof.
    intros ft F v Hv. pose proof (F v Hv) as C. pose proof (ClM_range a2 nb ltac:(lia) v).
    destruct C as [E|E]; rewrite E; [lia|]. rewrite lor_setmask by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem bigF_ok : forall i s, 0 <= i < 256 -> MI2 i s -> bigF qoff nb ro i s.
  Proof.
    intros i s Hi M2. pose proof M2 as [IV QV].
    pose proof (RO i Hi) as Hss. unfold bigF. set (ss := zget ro i) in *.
    split; [exact Hss|]. split; [exact (F1_ok i s Hi M2)|].
    pose proof (ms_step1_inv a2 nb qoff BB NB1 NB2 256 ss 0 s s Hss ltac:(lia) ltac:(cbn; lia)
                  (conj (mi_pinv _ _ _ _ _ _ IV) (conj (mi_ft _ _ _ _ _ _ IV) (conj eq_refl eq_refl)))) as S1.
    set (s1 := ms_step1 256 qoff nb ss 0 s) in *. cps_destruct S1 as (P1 & F1 & EA1 & EB1).
    intros EX1.
    pose proof (ms_copy_init_spec a2 nb NB1 NB2 256 (s_cs s1) (s_ce s1) (s_ft s1) ss 0 F1 Hss ltac:(lia) ltac:(cbn; lia)) as CI. cbv zeta in CI.
    destruct (ms_copy_init 256 (s_cs s1) (s_ce s1) (s_ft s1) ss 0) as [cs ce]. cbn [fst snd] in CI. destruct CI as [CI _].
    change (Z.of_nat 256) with 256 in CI. cbn [fst snd].
    assert (BD0 : zget (s_bd s1) ss = 0).
    { rewrite EB1. destruct (mi_bd01 _ _ _ _ _ _ IV ss Hss) as [E|E]; [exact E|]. exfalso.
      cps_destruct (proj1 (mi_bd _ _ _ _ _ _ IV ss Hss) ltac:(rewrite E; lia)) as (i' & Hi' & Ei'). pose proof (ROinj i' i ltac:(lia) Hi Ei'). lia. }
    rewrite ?(shl8 ss), ?(shl8 (ss + 1)). pose proof (FT_lohi a2 nb NB1 NB2 (s_ft s1) (256 * ss) F1 ltac:(lia)) as (C1 & _). rewrite C1.
    assert (C2 : clearmask (zget (s_ft s1) (256 * (ss + 1))) = CLM (256 * (ss + 1))).
    { apply ftcell_clear; [apply ClM_lt; lia| apply F1; lia]. }
    rewrite C2.
    assert (AGR : forall k, 0 <= k < nb -> rd8 (s_a2 s1) k = rd8 a2 k).
    { intros k Hk. rewrite EA1, (mi_a2 _ _ _ _ _ _ IV) by lia. apply AX. exact Hk. }
    assert (Hcs : forall c, 0 <= c < 256 -> zget cs c = BzCSewC.cs0 a2 nb ss c) by (intros c Hc; apply (proj1 (CI c Hc))).
    assert (Hce : forall c, 0 <= c < 256 -> zget ce c = BzCSewC.ce1 a2 nb ss c - 1) by (intros c Hc; unfold BzCSewC.ce1; apply (proj2 (CI c Hc))).
    pose proof (step2_exact a2 nb ss (s_bd s1) (s_a1 s1) (s_a2 s1) BB NB1 Hss BD0 P1 AGR cs ce Hcs Hce) as S2.
    cbv zeta in S2. unfold BzCSewC.B0, BzCSewC.B1 in S2.
    split; [exact BD0|]. split; [apply ftv_of_FT; exact F1|].
    pose proof (ms_mark_spec a2 nb 256 (s_ft s1) ss 0 F1 Hss ltac:(lia) ltac:(cbn; lia)) as FM.
    pose proof (FT_lohi a2 nb NB1 NB2 _ (256 * ss) FM ltac:(lia)) as (D1 & _).
    pose proof (ftcell_clear _ _ (ClM_lt a2 nb NB1 NB2 (256 * (ss + 1))) (FM (256 * (ss + 1)) ltac:(lia))) as D2.
    rewrite D1, D2.
    pose proof (ClM_mono a2 nb (256 * ss) (256 * (ss + 1)) ltac:(lia)) as MONO. pose proof (ClM_range a2 nb ltac:(lia) (256 * (ss + 1))) as RNG1.
    destruct (allss a2 nb ss) eqn:AL.
    - (* [comment removed for export] *)
      pose proof (allss_ClM a2 nb ss BB NB1 Hss AL) as G.
      assert (EB0 : CLM (256 * ss) = 0) by (apply (proj1 (G _)); lia).
      assert (ES0 : zget cs ss = 0) by (rewrite (Hcs ss Hss); unfold BzCSewC.cs0; apply (proj1 (G _)); lia).
      assert (EB1' : CLM (256 * (ss + 1)) = nb) by (apply (proj2 (G _)); lia).
      assert (ES1 : zget ce ss = nb - 1) by (rewrite (Hce ss Hss); unfold BzCSewC.ce1; rewrite (proj2 (G _)) by lia; lia).
      rewrite EB0, EB1' in *.
      assert (FS : forall k, ms_copy_fwd k (s_a1 s1) cs (s_a2 s1) (s_bd s1) nb ss 0 = (s_a1 s1, cs, 0)).
      { intros [|k]; [reflexivity|]. apply BzCLemmasMs3.ms_copy_fwd_stop. lia. }
      assert (BS : forall k, ms_copy_bwd k (s_a1 s1) ce (s_a2 s1) (s_bd s1) nb ss (nb - 1) = (s_a1 s1, ce, nb - 1)).
      { intros [|k]; [reflexivity|]. apply BzCLemmasMs3.ms_copy_bwd_stop. lia. }
      rewrite !FS. cbn [fst snd]. rewrite !BS. cbn [fst snd].
      split. { intros k. rewrite FS. cbn [fst snd]. split; [| intros; lia]. intros c Hc. rewrite (Hcs c Hc). unfold BzCSewC.cs0. apply (ClM_range a2 nb ltac:(lia)). }
      split; [lia|].
      split. { intros k. rewrite BS. cbn [fst snd]. split; [| intros; lia]. intros c Hc. rewrite (Hce c Hc).
               pose proof (ce1_le_nb a2 nb ss NB1 c). pose proof (cs0_le_ce1 a2 nb ss c). pose proof (cs0_ge_0 a2 nb ss NB1 c). lia. }
      split; [lia|]. split; [right; lia|]. intros _. lia.
    - pose proof (allss_false a2 nb ss AL) as NA.
      pose proof (forward_scan a2 nb ss (s_bd s1) (s_a1 s1) BB NB1 Hss BD0 P1 NA (s_a2 s1) AGR cs Hcs) as FS. cbv zeta in FS.
      unfold BzCSewC.B0 in FS.
      destruct (ms_copy_fwd (S (Z.to_nat nb)) _ _ _ _ _ _ _) as [[A0 cs'] jf] eqn:ERF. cbn [fst snd] in *. destruct FS as [FW Jf].
      destruct (ms_copy_bwd (S (Z.to_nat nb)) _ _ _ _ _ _ _) as [[a1 ce'] jb] eqn:ERB. cbn [fst snd] in *.
      cps_destruct S2 as (P2 & MEET & RNG & FRM & Jf' & Jb').
      split.
      { intros k. pose proof (fwd_prefix ss (s_bd s1) (s_a1 s1) (s_a2 s1) Hss BD0 P1 NA AGR k (s_a1 s1) cs (CLM (256 * ss))
                      (FWI_init a2 nb ss (s_bd s1) (s_a1 s1) Hss cs Hcs)) as PF. cbv zeta in PF.
        destruct (ms_copy_fwd k _ _ _ _ _ _ _) as [[ak ck] jk]. cbn [fst snd] in *.
        exact (fwdF_of_FWI ss (s_bd s1) (s_a1 s1) (s_a2 s1) ak ck jk Hss BD0 P1 NA AGR PF). }
      split; [lia|].
      split.
      { intros k. unfold BzCSewC.B1 in *.
        pose proof (bwd_prefix ss (s_bd s1) (s_a1 s1) A0 cs' (s_a2 s1) Hss BD0 P1 NA FW AGR k A0 ce (CLM (256 * (ss + 1)) - 1)
                      (BWI_init a2 nb ss (s_bd s1) A0 BB NB1 Hss NA ce Hce)) as PB. cbv zeta in PB.
        destruct (ms_copy_bwd k _ _ _ _ _ _ _) as [[ak ck] jk]. cbn [fst snd] in *.
        exact (bwdF_of_BWI ss (s_bd s1) (s_a1 s1) A0 cs' (s_a2 s1) ak ck jk Hss BD0 P1 NA FW AGR PB). }
      split; [lia|]. split; [exact MEET|]. intros _. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ms_quad_QOV : forall n b a1 bbStart shifts j,
    (forall x, 0 <= x <= j -> 0 <= rd32 a1 (bbStart + x) < nb) -> j + 1 = Z.of_nat n -> QOV b ->
    QOV (ms_quad n b a1 qoff nb bbStart shifts j).
  Proof.
    induction n as [|n IH]; intros b a1 bbStart shifts j RG Hj QV; [exact QV|].
    rewrite ms_quad_S. cbv zeta. pose proof (RG j ltac:(lia)) as Ru. set (u := rd32 a1 (bbStart + j)) in *.
    set (v := Z.shiftr j shifts).
    apply IH; [intros; apply RG; lia| lia|].
    intros z Hz. destruct (Z.ltb_spec u BZ_N_OVERSHOOT) as [LT|GE].
    - unfold BZ_N_OVERSHOOT in LT. destruct (Z.eq_dec (z - nb) u) as [E|NE].
      + rewrite <- E.
        assert (L1 : qrd (qwr (qwr b qoff (z - nb) v) qoff (z - nb + nb) v) qoff z = v mod 65536).
        { unfold qrd, qwr. replace (qoff + 2 * z) with (qoff + 2 * (z - nb + nb)) by lia. apply rd16_wr16_same_mod'. }
        rewrite L1. rewrite qrd_qwr_other by lia. unfold qrd, qwr. rewrite rd16_wr16_same_mod'. reflexivity.
      + rewrite !qrd_qwr_other by lia. apply QV. exact Hz.
    - unfold BZ_N_OVERSHOOT in GE. rewrite !qrd_qwr_other by lia. apply QV. exact Hz.
  Qed.

  Theorem big_next : forall i s, 0 <= i < 256 -> MI2 i s -> s_exit (ms_big ro qoff nb i s) = false -> MI2 (i + 1) (ms_big ro qoff nb i s).
  Proof.
    intros i s Hi [IV QV] EX.
    pose proof (ms_big_MI a2 nb qoff ro BB NB1 NB2 QO RO ROinj a2x AX i s Hi IV) as MB. cbv zeta in MB.
    destruct MB as [[EX' _]|IV']; [rewrite EX' in EX; discriminate|].
    split; [exact IV'|].
    pose proof (PINV_perm a2 nb BB NB1 _ (mi_pinv _ _ _ _ _ _ IV')) as [RG _].
    revert EX IV' RG. unfold ms_big. cbv zeta.
    pose proof (RO i Hi) as Hss. set (ss := zget ro i) in *.
    pose proof (ms_step1_inv a2 nb qoff BB NB1 NB2 256 ss 0 s s Hss ltac:(lia) ltac:(cbn; lia)
                  (conj (mi_pinv _ _ _ _ _ _ IV) (conj (mi_ft _ _ _ _ _ _ IV) (conj eq_refl eq_refl)))) as S1.
    set (s1 := ms_step1 256 qoff nb ss 0 s) in *. cps_destruct S1 as (P1 & F1 & EA1 & EB1).
    destruct (s_exit s1) eqn:EX1; [intros EX; rewrite EX1 in EX; discriminate|].
    destruct (ms_copy_init 256 (s_cs s1) (s_ce s1) (s_ft s1) ss 0) as [cs ce].
    destruct (ms_copy_fwd _ _ _ _ _ _ _ _) as [[af csf] jf].
    destruct (ms_copy_bwd _ _ _ _ _ _ _ _) as [[ab ceb] jb]. cbn [s_a1 s_a2 s_exit].
    intros _ IV' RG.
    destruct (Z.ltb_spec i 255) as [L|L]; [| rewrite EA1; exact QV].
    pose proof (ms_mark_spec a2 nb 256 (s_ft s1) ss 0 F1 Hss ltac:(lia) ltac:(cbn; lia)) as FM.
    rewrite ?(shl8 ss), ?(shl8 (ss + 1)).
    pose proof (FT_lohi a2 nb NB1 NB2 _ (256 * ss) FM ltac:(lia)) as (D1 & _).
    pose proof (ftcell_clear _ _ (ClM_lt a2 nb NB1 NB2 (256 * (ss + 1))) (FM (256 * (ss + 1)) ltac:(lia))) as D2.
    rewrite D1, D2.
    pose proof (ClM_mono a2 nb (256 * ss) (256 * (ss + 1)) ltac:(lia)) as MONO.
    pose proof (ClM_range a2 nb ltac:(lia) (256 * (ss + 1))) as RNG1. pose proof (ClM_range a2 nb ltac:(lia) (256 * ss)) as RNG0.
    apply ms_quad_QOV; [| lia| rewrite EA1; exact QV].
    intros x Hx. apply RG. lia.
  Qed.

  Theorem bigs_ok : forall s, MI2 0 s -> forall k, (k < 256)%nat ->
    s_exit (ms_bigs k ro qoff nb 0 s) = false -> bigF qoff nb ro (0 + Z.of_nat k) (ms_bigs k ro qoff nb 0 s) /\ MI2 (0 + Z.of_nat k) (ms_bigs k ro qoff nb 0 s).
  Proof.
    intros s M0.
    assert (GEN : forall k i s0, 0 <= i -> i + Z.of_nat k < 256 -> MI2 i s0 ->
              s_exit (ms_bigs k ro qoff nb i s0) = false -> bigF qoff nb ro (i + Z.of_nat k) (ms_bigs k ro qoff nb i s0) /\ MI2 (i + Z.of_nat k) (ms_bigs k ro qoff nb i s0)).
    { induction k as [|k IH]; intros i s0 Hi Hk M EX.
      - cbn [ms_bigs] in *. replace (i + Z.of_nat 0) with i by lia. split; [apply bigF_ok; [lia| exact M]| exact M].
      - rewrite ms_bigs_S in *. cbv zeta in EX. cbv zeta.
        destruct (s_exit (ms_big ro qoff nb i s0)) eqn:EXb; [cbn in EX; congruence|].
        pose proof (big_next i s0 ltac:(lia) M EXb) as M'.
        replace (i + Z.of_nat (S k)) with (i + 1 + Z.of_nat k) by lia.
        apply (IH (i + 1) _ ltac:(lia) ltac:(lia) M'). exact EX. }
    intros k Hk. apply GEN; [lia| lia| exact M0].
  Qed.
End Main.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section E.
  Variable e : est.
  Hypothesis BB : zbok (e_arr2 e).
  Hypothesis NB : 34 <= e_nblock e <= 899990.

  Lemma NBq : 34 <= bp_n e <= 899990. Proof. exact NB. Qed.

  Lemma pt_a2r_quad : forall z, 0 <= z < bp_n e -> qrd (bp_a2r e) (bp_qoff e) z = 0.
  Proof.
    pose proof NBq as NB'. intros z Hz. rewrite E_a2r, E_r1.
    pose proof (ms_radix1_quad (Z.to_nat (bp_n e)) (bp_a2 e) (bp_ft0 e) (bp_qoff e) (bp_n e - 1) (bp_j0 e) ltac:(lia)) as [Q _].
    apply Q. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pt_a2o_facts :
    (forall k, 0 <= k < bp_n e -> rd8 (bp_a2o e) k = rd8 (bp_a2 e) k) /\
    (forall z, bp_n e <= z < bp_n e + 34 -> rd8 (bp_a2o e) z = rd8 (bp_a2o e) (z - bp_n e)) /\
    (forall z, bp_n e <= z < bp_n e + 34 -> qrd (bp_a2o e) (bp_qoff e) z = qrd (bp_a2o e) (bp_qoff e) (z - bp_n e)).
  Proof.
    pose proof NBq as NB'. pose proof (QO e) as QO'.
    assert (Br : zbok (bp_a2r e)) by (rewrite E_a2r, E_r1; apply zbok_radix1; unfold bp_a2; exact BB).
    pose proof (ms_overshoot_spec 34 (bp_a2r e) (bp_qoff e) (bp_n e) 0 Br ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as OV.
    cbv zeta in OV. rewrite <- E_a2o in OV. cps_destruct OV as (C & L & Q & _). change (Z.of_nat 34) with 34 in *.
    split; [exact (pt_a2o e BB ltac:(lia))|]. split.
    - intros z Hz. destruct (C (z - bp_n e) ltac:(lia)) as [C1 _]. replace (bp_n e + (z - bp_n e)) with z in C1 by lia.
      rewrite C1. symmetry. apply L. lia.
    - intros z Hz. destruct (C (z - bp_n e) ltac:(lia)) as [_ C2]. replace (bp_n e + (z - bp_n e)) with z in C2 by lia.
      rewrite C2. rewrite Q by lia. symmetry. apply pt_a2r_quad. lia.
  Qed.

  Lemma pt_KpM : forall i, 0 <= i < bp_n e -> rd32 (bp_a1r e) (KpM (bp_a2 e) (bp_n e) i) = i.
  Proof.
    pose proof NBq as NB'.
    pose proof (ms_radix_perm (bp_a2 e) (bp_n e) (BBr e BB) ltac:(lia) (bp_a1 e) (bp_a2o e) (bp_ft3 e) (pt_a2o e BB ltac:(lia)) (pt_ft3 e BB ltac:(lia))) as R.
    cbv zeta in R. rewrite <- E_s0, <- E_r4, <- E_a1r in R. exact (proj1 (proj2 R)).
  Qed.

  Lemma pt_ro : (forall c, 0 <= c < 256 -> zget bp_bd5 c = 0) /\
                (forall i, 0 <= i < 256 -> 0 <= zget (bp_ro6 e) i < 256) /\
                (forall i i', 0 <= i < 256 -> 0 <= i' < 256 -> zget (bp_ro6 e) i = zget (bp_ro6 e) i' -> i = i').
  Proof.
    pose proof (runningOrder_perm znew znew (bp_ft4 e)) as R. unfold bp_bd5, bp_ro6, bp_ro5.
    destruct (ms_ro_init 256 znew znew 0) as [bd ro]. cbn [fst snd]. exact R.
  Qed.

  Theorem MI2_init : forall cs ce nl nh nd,
    MI2 (bp_a2 e) (bp_n e) (bp_qoff e) (bp_ro6 e) (bp_a2o e) 0
        (MSS (bp_a1r e) (bp_a2o e) (bp_ft4 e) bp_bd5 cs ce (bp_budget0 e) 0 (MQL znew znew znew nl nh nd) false).
  Proof.
    pose proof NBq as NB'. intros cs ce nl nh nd. cps_destruct pt_ro as (BD0 & ROR & ROI). cps_destruct pt_a2o_facts as (AX & BOV & QOV0).
    split.
    - constructor; cbn [s_a1 s_a2 s_ft s_bd s_exit].
      + apply (PINV_of_KpM (bp_a2 e) (bp_n e) ltac:(lia)). exact pt_KpM.
      + intros; reflexivity.
      + intros v Hv. left. apply (pt_ft4 e BB ltac:(lia)). exact Hv.
      + intros c Hc. left. apply BD0. exact Hc.
      + intros c Hc. rewrite BD0 by exact Hc. split; [intros X; exfalso; exact (X eq_refl)| cps_intros (i' & Hi' & _); lia].
      + reflexivity.
    - cbn [s_a2]. exact QOV0.
  Qed.

  (* [comment removed for export] *)
  Theorem bsB_bigF_ok : forall cs ce nl nh nd k, (k < 256)%nat ->
    let s' := ms_bigs k (bp_ro6 e) (bp_qoff e) (bp_n e) 0
                (MSS (bp_a1r e) (bp_a2o e) (bp_ft4 e) bp_bd5 cs ce (bp_budget0 e) 0 (MQL znew znew znew nl nh nd) false) in
    s_exit s' = false -> bigF (bp_qoff e) (bp_n e) (bp_ro6 e) (0 + Z.of_nat k) s'.
  Proof.
    pose proof NBq as NB'. intros cs ce nl nh nd k Hk. cbv zeta. intros EX.
    cps_destruct pt_ro as (BD0 & ROR & ROI). cps_destruct pt_a2o_facts as (AX & BOV & QOV0).
    exact (proj1 (bigs_ok (bp_a2 e) (bp_n e) (bp_qoff e) (bp_ro6 e) (bp_a2o e) (BBr e BB) NB' (QO e) ROR ROI AX BOV
                   _ (MI2_init cs ce nl nh nd) k Hk EX)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End E.

End ACeilS1.
