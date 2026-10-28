(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzLemmasT BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCPermF BzCPermF2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCPermM BzCQsortM1 BzCQsortM2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC BzCSewD BzCSewE BzCSewF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewH BzCSortPost BzCFactsBs3. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR2Theory BzR3aPre BzR3aFs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzR3gtu BzR3bMq.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzR3cSew.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzR3cSew.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA.BzCBudget OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewG OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewH OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortPost OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsBs3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2Theory OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR3aPre OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR3aFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzR3gtu OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzR3bMq OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzR3cSew.BzR3cOrd OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzR3cSew.
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

(* [comment removed for export] *)
Lemma ms_mark_get : forall n ft ss j0 v, 0 <= j0 ->
  zget (ms_mark n ft ss j0) v = zget ft v \/
  (zget (ms_mark n ft ss j0) v = Z.lor (zget ft v) SETMASK /\ exists j, j0 <= j < j0 + Z.of_nat n /\ v = 256 * j + ss).
Proof.
  induction n as [|n IH]; intros ft ss j0 v Hj0; [left; reflexivity|].
  rewrite ms_mark_S. cbv zeta. rewrite shl8.
  destruct (IH (zset ft (256 * j0 + ss) (Z.lor (zget ft (256 * j0 + ss)) SETMASK)) ss (j0 + 1) v ltac:(lia)) as [E|[E (j & Hj & Ev)]];
    rewrite E, zget_zset.
  - destruct (Z.eqb_spec v (256 * j0 + ss)) as [->|NE]; [| left; reflexivity].
    right. split; [reflexivity|]. exists j0. split; [lia| reflexivity].
  - destruct (Z.eqb_spec v (256 * j0 + ss)) as [->|NE]; [exfalso; lia|].
    right. split; [reflexivity|]. exists j. split; [lia| exact Ev].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ms_quad_spec : forall nb qoff, 34 <= nb -> nb + 34 <= qoff -> forall n b a1 bbStart shifts j,
  (forall x, 0 <= x <= j -> 0 <= rd32 a1 (bbStart + x) < nb) ->
  (forall x x', 0 <= x <= j -> 0 <= x' <= j -> rd32 a1 (bbStart + x) = rd32 a1 (bbStart + x') -> x = x') ->
  (forall x, 0 <= x <= j -> 0 <= Z.shiftr x shifts < 65536) ->
  j + 1 = Z.of_nat n ->
  let b' := ms_quad n b a1 qoff nb bbStart shifts j in
  (forall x, 0 <= x <= j -> qrd b' qoff (rd32 a1 (bbStart + x)) = Z.shiftr x shifts) /\
  (forall p, 0 <= p < nb -> (forall x, 0 <= x <= j -> rd32 a1 (bbStart + x) <> p) -> qrd b' qoff p = qrd b qoff p) /\
  ((forall i, 0 <= i < 34 -> qrd b qoff (nb + i) = qrd b qoff i) -> forall i, 0 <= i < 34 -> qrd b' qoff (nb + i) = qrd b' qoff i).
Proof.
  intros nb qoff N34 QO. induction n as [|n IH]; intros b a1 bbStart shifts j RG INJ SH Hj; cbv zeta.
  - cbn [ms_quad]. split; [intros; lia|]. split; [intros; reflexivity| intros H; exact H].
  - rewrite ms_quad_S. cbv zeta. pose proof (RG j ltac:(lia)) as Ru. pose proof (SH j ltac:(lia)) as Sv.
    set (u := rd32 a1 (bbStart + j)) in *. set (v := Z.shiftr j shifts) in *.
    set (b1 := if u <? BZ_N_OVERSHOOT then qwr (qwr b qoff u v) qoff (u + nb) v else qwr b qoff u v).
    assert (Q1 : forall p, 0 <= p < nb -> p <> u -> qrd b1 qoff p = qrd b qoff p).
    { intros p Hp NE. subst b1. unfold BZ_N_OVERSHOOT. destruct (Z.ltb_spec u 34); rewrite ?qrd_qwr_other by lia; reflexivity. }
    assert (Qu : qrd b1 qoff u = v).
    { subst b1. unfold BZ_N_OVERSHOOT. destruct (Z.ltb_spec u 34); rewrite ?(qrd_qwr_other _ qoff (u + nb)) by lia;
        unfold qrd, qwr; rewrite rd16_wr16_same_mod'; apply Z.mod_small; lia. }
    assert (Qm : (forall i, 0 <= i < 34 -> qrd b qoff (nb + i) = qrd b qoff i) -> forall i, 0 <= i < 34 -> qrd b1 qoff (nb + i) = qrd b1 qoff i).
    { intros M i Hi. subst b1. unfold BZ_N_OVERSHOOT. destruct (Z.ltb_spec u 34) as [L|L].
      - destruct (Z.eq_dec i u) as [->|NE].
        + replace (nb + u) with (u + nb) by lia. unfold qrd, qwr. rewrite rd16_wr16_same_mod'.
          rewrite rd16_wr16_other by lia. rewrite rd16_wr16_same_mod'. reflexivity.
        + rewrite !qrd_qwr_other by lia. apply M. exact Hi.
      - rewrite !qrd_qwr_other by lia. apply M. exact Hi. }
    cps_destruct (IH b1 a1 bbStart shifts (j - 1) ltac:(intros; apply RG; lia) ltac:(intros; apply INJ; lia) ltac:(intros; apply SH; lia) ltac:(lia))
      as (V1 & F1 & M1).
    split; [| split].
    + intros x Hx. destruct (Z.eq_dec x j) as [->|NE]; [| apply V1; lia].
      fold u v. rewrite F1; [exact Qu| exact Ru|]. intros x' Hx' E. pose proof (INJ x' j ltac:(lia) ltac:(lia) E). lia.
    + intros p Hp NP. rewrite F1; [| exact Hp| intros; apply NP; lia]. apply Q1; [exact Hp|]. intros ->. exact (NP j ltac:(lia) eq_refl).
    + intros M. apply M1. apply Qm. exact M.
Qed.

Lemma shiftr_mono : forall x x' s, 0 <= s -> x <= x' -> Z.shiftr x s <= Z.shiftr x' s.
Proof. intros x x' s Hs H. rewrite !Z.shiftr_div_pow2 by lia. apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia| exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Main.
  Variables (a2 : zarr) (nb qoff : Z) (ro a2x : zarr).
  Hypothesis BB : forall i, 0 <= rd8 a2 i < 256.
  Hypothesis NB : 34 <= nb <= 900000.
  Hypothesis QO : nb + 34 <= qoff.
  Hypothesis RO : forall i, 0 <= i < 256 -> 0 <= zget ro i < 256.
  Hypothesis ROinj : forall i i', 0 <= i < 256 -> 0 <= i' < 256 -> zget ro i = zget ro i' -> i = i'.
  (* [comment removed for export] *)
  Hypothesis AX : forall k, 0 <= k < nb -> rd8 a2x k = rd8 a2 k.
  Hypothesis BOV : forall i, 0 <= i < 34 -> rd8 a2x (nb + i) = rd8 a2x i.

  Lemma NB1 : 1 <= nb <= 2097151. Proof. lia. Qed.
  Lemma NB2 : nb <= 1000000. Proof. lia. Qed.
  Lemma N34 : 34 <= nb. Proof. lia. Qed.

  Local Notation KEY := (BzCPermM.key a2 nb).
  Local Notation CLM := (ClM a2 nb).
  Local Notation NXT := (BzCPermM.nxt nb).
  Local Notation ROT p := (rot (blk a2 nb) (Z.to_nat p)).
  Local Notation LE x y := (lexle (rot (blk a2 nb) (Z.to_nat x)) (rot (blk a2 nb) (Z.to_nat y))).
  Local Notation SBa := (SB a2 nb).
  Local Notation MIx := (MI a2 nb ro a2x).
  Local Notation FTx := (FT a2 nb).

  (* [comment removed for export] *)
  Definition LIVE (b : zarr) : Prop := forall k, 0 <= k < nb + 34 -> rd8 b k = rd8 a2x k.
  (* [comment removed for export] *)
  Definition QSND (b : zarr) : Prop := forall p p', 0 <= p < nb -> 0 <= p' < nb -> rd8 a2 p = rd8 a2 p' ->
    qrd b qoff p < qrd b qoff p' -> LE p p'.
  Definition QMIR (b : zarr) : Prop := forall i, 0 <= i < 34 -> qrd b qoff (nb + i) = qrd b qoff i.

  Lemma live_bytes : forall b, LIVE b -> forall k, 0 <= k < nb -> rd8 b k = rd8 a2 k.
  Proof. intros b L k Hk. rewrite L by lia. apply AX. exact Hk. Qed.
  Lemma live_OVB : forall b, LIVE b -> forall i, 0 <= i < 34 -> rd8 b (nb + i) = rd8 b i.
  Proof. intros b L i Hi. rewrite !L by lia. apply BOV. exact Hi. Qed.
  Lemma live_blk : forall b, LIVE b -> blk b nb = blk a2 nb.
  Proof.
    intros b L. unfold blk. apply map_ext_in. intros k Hk. apply in_seq in Hk. unfold N in Hk. apply (live_bytes b L). lia.
  Qed.
  Lemma live_QIw : forall b, LIVE b -> QSND b -> forall p p', 0 <= p < nb -> 0 <= p' < nb -> rd8 b p = rd8 b p' ->
    qrd b qoff p < qrd b qoff p' -> lexle (rot (blk b nb) (Z.to_nat p)) (rot (blk b nb) (Z.to_nat p')).
  Proof.
    intros b L Q p p' Hp Hp' E LT. rewrite (live_blk b L). apply Q; [exact Hp| exact Hp'| | exact LT].
    rewrite <- !(live_bytes b L) by assumption. exact E.
  Qed.

  (* [comment removed for export] *)
  Lemma EQB2_of_key : forall b p p', LIVE b -> 0 <= p < nb -> 0 <= p' < nb -> KEY p = KEY p' -> EQB b nb p p' 2.
  Proof.
    intros b p p' L Hp Hp' K jj Hjj. unfold bt.
    pose proof (key_range a2 nb BB p) as KR.
    assert (D : KEY p' = 256 * (KEY p / 256) + (KEY p mod 256)) by (rewrite <- K; apply Z.div_mod; lia).
    assert (D0 : KEY p = 256 * (KEY p / 256) + (KEY p mod 256)) by (apply Z.div_mod; lia).
    pose proof (Z.mod_pos_bound (KEY p) 256 ltac:(lia)) as MR.
    apply (proj1 (key_chars a2 nb BB p _ _ MR)) in D0. apply (proj1 (key_chars a2 nb BB p' _ _ MR)) in D.
    destruct D0 as [A0 B0']. destruct D as [A1 B1'].
    assert (jj = 0 \/ jj = 1) as [->| ->] by lia.
    - rewrite !Z.add_0_r, !Z.mod_small by lia. rewrite !(live_bytes b L) by lia. congruence.
    - rewrite <- !(nxt_mod a2 nb NB1 N34) by lia.
      rewrite !(live_bytes b L) by (apply (nxt_range nb NB1); lia). congruence.
  Qed.

  (* [comment removed for export] *)
  Record OI (s : mss) : Prop := {
    oi_q : QSND (s_a2 s);
    oi_ov : QMIR (s_a2 s);
    oi_sb : forall c1 c2, 0 <= c1 < 256 -> 0 <= c2 < 256 -> (zget (s_bd s) c1 <> 0 \/ zget (s_bd s) c2 <> 0) -> SBa (s_a1 s) (256 * c1 + c2);
    oi_fl : forall c1 c2, 0 <= c1 < 256 -> 0 <= c2 < 256 -> has_setmask (zget (s_ft s) (256 * c1 + c2)) = true ->
            zget (s_bd s) c1 <> 0 \/ zget (s_bd s) c2 <> 0 }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Record S1S (s0 : mss) (ss j : Z) (s : mss) : Prop := {
    s1_pinv : PINV a2 nb (s_a1 s);
    s1_ftv : FTx (s_ft s);
    s1_a2 : s_a2 s = s_a2 s0;
    s1_bd : s_bd s = s_bd s0;
    s1_keep : s_exit s = false -> forall v, 0 <= v < 65536 -> SBa (s_a1 s0) v -> SBa (s_a1 s) v;
    s1_done : s_exit s = false -> forall j', 0 <= j' < j -> j' <> ss -> SBa (s_a1 s) (256 * ss + j');
    s1_fl : forall v, has_setmask (zget (s_ft s) v) = true -> has_setmask (zget (s_ft s0) v) = true \/ 256 * ss <= v < 256 * ss + j }.

  Lemma S1S_init : forall s0 ss, PINV a2 nb (s_a1 s0) -> FTx (s_ft s0) -> S1S s0 ss 0 s0.
  Proof.
    intros s0 ss P F. constructor; [exact P| exact F| reflexivity| reflexivity| intros _ v _ H; exact H| intros; lia| intros v H; left; exact H].
  Qed.

  Lemma SB_frame : forall a a' v lo hi, SBa a v -> frame_out a a' lo hi ->
    (forall p, CLM v <= p < CLM (v + 1) -> p < lo \/ hi < p) -> SBa a' v.
  Proof. intros a a' v lo hi S FR OUT. apply (SB_ext a2 nb NB1 N34 a a' v S). intros p Hp. apply FR. apply OUT. exact Hp. Qed.

  Lemma step1_sorted : forall s0 ss, 0 <= ss < 256 -> zget (s_bd s0) ss = 0 -> LIVE (s_a2 s0) -> OI s0 ->
    forall n j s, 0 <= j -> j + Z.of_nat n <= 256 -> S1S s0 ss j s -> S1S s0 ss (j + Z.of_nat n) (ms_step1 n qoff nb ss j s).
  Proof.
    intros s0 ss Hss BD0 L0 OI0.
    pose proof (live_OVB _ L0) as OVB0. pose proof (oi_ov _ OI0) as OVQ0. pose proof (live_QIw _ L0 (oi_q _ OI0)) as QIW0.
    induction n as [|n IH]; intros j s Hj Hn IV.
    { cbn [ms_step1]. replace (j + Z.of_nat 0) with j by lia. exact IV. }
    rewrite ms_step1_S.
    assert (WK : forall j2 s2, j2 <= j + Z.of_nat (S n) -> S1S s0 ss j2 s2 -> s_exit s2 = true -> S1S s0 ss (j + Z.of_nat (S n)) s2).
    { intros j2 s2 Hj2 X EX. destruct X as [XP XF XA XB XK XD XL]. constructor; [exact XP| exact XF| exact XA| exact XB| | |].
      - intros E. rewrite EX in E. discriminate.
      - intros E. rewrite EX in E. discriminate.
      - intros v Hv. destruct (XL v Hv) as [A|A]; [left; exact A| right; lia]. }
    destruct (s_exit s) eqn:EXs; [apply (WK j s ltac:(lia) IV EXs)|].
    destruct (Z.eqb_spec j ss) as [->|NE].
    { replace (ss + Z.of_nat (S n)) with (ss + 1 + Z.of_nat n) by lia. apply IH; [lia| lia|].
      destruct IV as [XP XF XA XB XK XD XL]. constructor; [exact XP| exact XF| exact XA| exact XB| exact XK| |].
      - intros E j' Hj' Nj'. apply (XD E); lia.
      - intros v Hv. destruct (XL v Hv) as [A|A]; [left; exact A| right; lia]. }
    cbv zeta. rewrite shl8.
    cps_pose (FT_lohi a2 nb NB1 NB2 (s_ft s) (256 * ss + j) (s1_ftv _ _ _ _ IV) ltac:(lia)) as (C1 & C2 & R1 & R2). rewrite C1, C2.
    set (sb := 256 * ss + j) in *.
    pose proof (ClM_lt a2 nb NB1 NB2 sb) as CL1. pose proof (ClM_range a2 nb ltac:(lia) (sb + 1)) as CL2.
    pose proof (ClM_mono a2 nb sb (sb + 1) ltac:(lia)) as CL3.
    (* [comment removed for export] *)
    assert (MARK : forall s1, S1S s0 ss j s1 -> s_exit s1 = false -> SBa (s_a1 s1) sb ->
      S1S s0 ss (j + 1) (MSS (s_a1 s1) (s_a2 s1) (zset (s_ft s1) sb (Z.lor (zget (s_ft s1) sb) SETMASK)) (s_bd s1) (s_cs s1) (s_ce s1) (s_budget s1) (s_nqs s1) (s_mql s1) false)).
    { intros s1 X EX1 SBj. destruct X as [XP XF XA XB XK XD XL]. constructor; cbn [s_a1 s_a2 s_ft s_bd s_exit]; [exact XP| | exact XA| exact XB| | |].
      - intros v Hv. rewrite zget_zset. destruct (Z.eqb_spec v sb) as [->|NV]; [apply ftcell_mark|]; apply XF; lia.
      - intros _. exact (XK EX1).
      - intros _ j' Hj' Nj'. destruct (Z.eq_dec j' j) as [->|NJ]; [exact SBj|]. apply (XD EX1); lia.
      - intros v. rewrite zget_zset. destruct (Z.eqb_spec v sb) as [->|NV]; [intros _; right; subst sb; lia|].
        intros Hv. destruct (XL v Hv) as [A|A]; [left; exact A| right; lia]. }
    replace (j + Z.of_nat (S n)) with (j + 1 + Z.of_nat n) by lia.
    destruct (has_setmask (zget (s_ft s) sb)) eqn:HS; cbn [negb].
    - (* [comment removed for export] *)
      apply IH; [lia| lia|]. apply (MARK s IV EXs).
      destruct (s1_fl _ _ _ _ IV sb HS) as [A|A]; [| exfalso; subst sb; lia].
      apply (s1_keep _ _ _ _ IV EXs sb ltac:(lia)).
      destruct (oi_fl _ OI0 ss j Hss ltac:(lia) A) as [C|C]; [exfalso; exact (C BD0)|].
      apply (oi_sb _ OI0 ss j Hss ltac:(lia)). right. exact C.
    - destruct (Z.ltb_spec (CLM sb) (CLM (sb + 1) - 1)) as [LT|GE].
      + (* [comment removed for export] *)
        rewrite (s1_a2 _ _ _ _ IV).
        pose proof (PINV_perm a2 nb BB NB1 _ (s1_pinv _ _ _ _ IV)) as PM.
        assert (EQ2 : forall x y, CLM sb <= x <= CLM (sb + 1) - 1 -> CLM sb <= y <= CLM (sb + 1) - 1 ->
                  EQB (s_a2 s0) nb (rd32 (s_a1 s) x) (rd32 (s_a1 s) y) 2).
        { intros x y Hx Hy. pose proof (key_range a2 nb BB 0).
          destruct (s1_pinv _ _ _ _ IV sb ltac:(lia)) as [V _].
          destruct (V x ltac:(lia)) as [Rx Kx]. destruct (V y ltac:(lia)) as [Ry Ky].
          apply EQB2_of_key; [exact L0| exact Rx| exact Ry| congruence]. }
        pose proof (mainQSort3_sorted (s_a2 s0) qoff nb N34 ltac:(lia) OVB0 OVQ0 QIW0 (CLM sb) (CLM (sb + 1) - 1) BZ_N_RADIX
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold BZ_N_RADIX; lia) (s_a1 s) (s_budget s) (s_mql s) PM
                      ltac:(change (21 * 2 ^ 16) with 1376256; lia) EQ2) as MQ.
        cbv zeta in MQ. destruct (mainQSort3 _ _ _ _ _ _ _ _ _) as [[a1 budget] mql]. cbn [fst snd] in MQ.
        cps_destruct MQ as (_ & PM' & FR' & SRT).
        assert (P' : PINV a2 nb a1).
        { apply (PINV_perm_frame a2 nb BB NB1 (s_a1 s) a1 sb (s1_pinv _ _ _ _ IV) ltac:(pose proof (key_range a2 nb BB 0); lia) PM' FR'). }
        assert (KEEP : forall v, 0 <= v < 65536 -> v <> sb -> SBa (s_a1 s) v -> SBa a1 v).
        { intros v Hv NV S. apply (SB_frame _ _ v _ _ S FR'). intros p Hp.
          pose proof (R_disjoint a2 nb v sb p NV Hp). lia. }
        assert (X1 : forall ex, (ex = true <-> budget < 0) ->
                  S1S s0 ss j (MSS a1 (s_a2 s0) (s_ft s) (s_bd s) (s_cs s) (s_ce s) budget (s_nqs s + (CLM (sb + 1) - 1 - CLM sb + 1)) mql ex)).
        { intros ex Hex. pose proof IV as X. destruct X as [XP XF XA XB XK XD XL].
          constructor; cbn [s_a1 s_a2 s_ft s_bd s_exit]; [exact P'| exact XF| reflexivity| exact XB| | | exact XL].
          - intros EX v Hv S. destruct (Z.eq_dec v sb) as [->|NV].
            + intros p p' A B C. rewrite <- (live_blk _ L0).
              rewrite <- !(rotz_small (s_a2 s0) nb) by (pose proof (proj1 PM' p ltac:(lia)); pose proof (proj1 PM' p' ltac:(lia)); lia).
              apply SRT; [| lia| lia| lia]. destruct ex; [discriminate|]. destruct (Z.lt_ge_cases budget 0) as [Bn|Bn]; [| exact Bn].
              exfalso. destruct Hex as [_ H2]. specialize (H2 Bn). discriminate.
            + apply KEEP; [exact Hv| exact NV|]. apply (s1_keep _ _ _ _ IV EXs v Hv S).
          - intros EX j' Hj' Nj'. apply KEEP; [lia| subst sb; lia|]. apply (s1_done _ _ _ _ IV EXs j' Hj' Nj'). }
        destruct (Z.ltb_spec budget 0) as [Bneg|Bpos].
        * (* [comment removed for export] *) replace (j + 1 + Z.of_nat n) with (j + Z.of_nat (S n)) by lia.
          apply (WK j); [lia| apply X1; split; [intros _; exact Bneg| reflexivity]| reflexivity].
        * apply IH; [lia| lia|]. apply MARK; [apply X1; split; [discriminate| intros; lia]| reflexivity|].
          cbn [s_a1]. intros p p' A B C.
          rewrite <- (live_blk _ L0).
          rewrite <- !(rotz_small (s_a2 s0) nb) by (pose proof (proj1 PM' p ltac:(lia)); pose proof (proj1 PM' p' ltac:(lia)); lia).
          apply SRT; lia.
      + (* [comment removed for export] *) apply IH; [lia| lia|]. apply (MARK s IV EXs). apply (SB_small a2 nb NB1 N34). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma in_big : forall ss v p, 0 <= ss < 256 -> CLM v <= p < CLM (v + 1) ->
    CLM (256 * ss) <= p < CLM (256 * (ss + 1)) -> 256 * ss <= v < 256 * (ss + 1).
  Proof.
    intros ss v p Hss Rp Bp. split.
    - destruct (Z.lt_ge_cases v (256 * ss)) as [L|G]; [| exact G]. pose proof (ClM_mono a2 nb (v + 1) (256 * ss) ltac:(lia)). lia.
    - destruct (Z.lt_ge_cases v (256 * (ss + 1))) as [L|G]; [exact L|]. pose proof (ClM_mono a2 nb (256 * (ss + 1)) v G). lia.
  Qed.

  Lemma sorted_of_big : forall a ss, PINV a2 nb a -> 0 <= ss < 256 -> (forall c, 0 <= c < 256 -> SBa a (256 * ss + c)) ->
    forall q q', CLM (256 * ss) <= q -> q <= q' -> q' < CLM (256 * (ss + 1)) -> LE (rd32 a q) (rd32 a q').
  Proof.
    intros a ss PV Hss SBS q q' Hq Hqq Hq'.
    pose proof (ClM_range a2 nb ltac:(lia) (256 * ss)). pose proof (ClM_range a2 nb ltac:(lia) (256 * (ss + 1))).
    cps_destruct (bucket_of a2 nb BB NB1 q ltac:(lia)) as (v & Hv & Rq). cps_destruct (bucket_of a2 nb BB NB1 q' ltac:(lia)) as (w & Hw & Rq').
    pose proof (in_big ss v q Hss Rq ltac:(lia)) as Bv. pose proof (in_big ss w q' Hss Rq' ltac:(lia)) as Bw.
    destruct (Z.eq_dec v w) as [->|NE].
    - pose proof (SBS (w - 256 * ss) ltac:(lia)) as S. replace (256 * ss + (w - 256 * ss)) with w in S by lia. apply S; lia.
    - destruct (PV v Hv) as [Vv _]. destruct (PV w Hw) as [Vw _].
      destruct (Vv q Rq) as [R1 K1]. destruct (Vw q' Rq') as [R2 K2].
      assert (v < w). { destruct (Z.lt_ge_cases v w) as [|G]; [assumption|]. exfalso. pose proof (ClM_mono a2 nb (w + 1) v ltac:(lia)). lia. }
      left. apply (key_lt_rot a2 nb BB NB1 N34); [exact R1| exact R2|]. rewrite K1, K2. assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma big_rows : forall a ss q, PINV a2 nb a -> 0 <= ss < 256 -> CLM (256 * ss) <= q < CLM (256 * (ss + 1)) ->
    0 <= rd32 a q < nb /\ rd8 a2 (rd32 a q) = ss.
  Proof.
    intros a ss q PV Hss Hq.
    pose proof (ClM_range a2 nb ltac:(lia) (256 * ss)). pose proof (ClM_range a2 nb ltac:(lia) (256 * (ss + 1))).
    cps_destruct (bucket_of a2 nb BB NB1 q ltac:(lia)) as (v & Hv & Rq). pose proof (in_big ss v q Hss Rq Hq) as Bv.
    destruct (proj1 (PV v Hv) q Rq) as [R K]. split; [exact R|].
    pose proof (proj1 (key_chars a2 nb BB (rd32 a q) ss (v - 256 * ss) ltac:(lia)) ltac:(rewrite K; lia)) as [E _]. exact E.
  Qed.
  Lemma big_cover : forall a ss p, PINV a2 nb a -> 0 <= ss < 256 -> 0 <= p < nb -> rd8 a2 p = ss ->
    exists q, CLM (256 * ss) <= q < CLM (256 * (ss + 1)) /\ rd32 a q = p.
  Proof.
    intros a ss p PV Hss Hp Ep. pose proof (key_range a2 nb BB p) as KR.
    cps_destruct (BEX_cover a2 nb NB1 a (KEY p) (PV (KEY p) KR) p Hp eq_refl) as (q & Hq & Eq).
    exists q. split; [| exact Eq].
    assert (K : 256 * ss <= KEY p < 256 * (ss + 1)). { rewrite (key_split a2 nb p), Ep. pose proof (BB (NXT p)). lia. }
    pose proof (ClM_mono a2 nb (256 * ss) (KEY p) ltac:(lia)). pose proof (ClM_mono a2 nb (KEY p + 1) (256 * (ss + 1)) ltac:(lia)). lia.
  Qed.

  Lemma allss_rot : forall ss, 0 <= ss < 256 -> allss a2 nb ss = true -> forall p p', 0 <= p < nb -> 0 <= p' < nb -> ROT p = ROT p'.
  Proof.
    intros ss Hss AS p p' Hp Hp'. rewrite !(rot_pre a2 nb NB1 N34) by assumption. unfold pre. apply map_ext_in. intros k Hk.
    rewrite !(ch_blk a2 nb NB1 N34) by lia. rewrite !(allss_true a2 nb ss AS) by (apply Z.mod_pos_bound; lia). reflexivity.
  Qed.

  Lemma mod256_of : forall c c2, 0 <= c2 < 256 -> (256 * c + c2) mod 256 = c2.
  Proof. intros c c2 H. replace (256 * c + c2) with (c2 + c * 256) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. exact H. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem ms_big_OI : forall i s, 0 <= i < 256 -> MIx i s -> OI s ->
    let s' := ms_big ro qoff nb i s in s_exit s' = true \/ (MIx (i + 1) s' /\ OI s').
  Proof.
    intros i s Hi IV OV. cbv zeta.
    pose proof (ms_big_MI a2 nb qoff ro BB NB1 NB2 QO RO ROinj a2x AX i s Hi IV) as MB. cbv zeta in MB.
    destruct (s_exit (ms_big ro qoff nb i s)) eqn:EX; [left; reflexivity| right].
    destruct MB as [[EX' _]|IV']; [rewrite EX' in EX; discriminate|]. split; [exact IV'|].
    pose proof (mi_pinv _ _ _ _ _ _ IV') as PVf. pose proof (PINV_perm a2 nb BB NB1 _ PVf) as PMf.
    revert EX PVf PMf. unfold ms_big. cbv zeta.
    pose proof (RO i Hi) as Hss. set (ss := zget ro i) in *.
    assert (BD0 : zget (s_bd s) ss = 0).
    { destruct (mi_bd01 _ _ _ _ _ _ IV ss Hss) as [E|E]; [exact E|]. exfalso.
      cps_destruct (proj1 (mi_bd _ _ _ _ _ _ IV ss Hss) ltac:(rewrite E; lia)) as (i' & Hi' & Ei'). pose proof (ROinj i' i ltac:(lia) Hi Ei'). lia. }
    assert (L0 : LIVE (s_a2 s)) by (intros k Hk; apply (mi_a2 _ _ _ _ _ _ IV); exact Hk).
    pose proof (step1_sorted s ss Hss BD0 L0 OV 256 0 s ltac:(lia) ltac:(cbn; lia) (S1S_init s ss (mi_pinv _ _ _ _ _ _ IV) (mi_ft _ _ _ _ _ _ IV))) as S1.
    change (0 + Z.of_nat 256) with 256 in S1.
    set (s1 := ms_step1 256 qoff nb ss 0 s) in *.
    destruct S1 as [P1 F1 EA1 EB1 KEEP1 DONE1 FL1].
    destruct (s_exit s1) eqn:EX1; [intros EX; rewrite EX1 in EX; discriminate|].
    specialize (KEEP1 eq_refl). specialize (DONE1 eq_refl).
    (* [comment removed for export] *)
    pose proof (ms_copy_init_spec a2 nb NB1 NB2 256 (s_cs s1) (s_ce s1) (s_ft s1) ss 0 F1 Hss ltac:(lia) ltac:(cbn; lia)) as CI. cbv zeta in CI.
    destruct (ms_copy_init 256 (s_cs s1) (s_ce s1) (s_ft s1) ss 0) as [cs ce]. cbn [fst snd] in CI. destruct CI as [CI _].
    change (Z.of_nat 256) with 256 in CI.
    rewrite ?(shl8 ss), ?(shl8 (ss + 1)). pose proof (FT_lohi a2 nb NB1 NB2 (s_ft s1) (256 * ss) F1 ltac:(lia)) as (C1 & _). rewrite C1.
    replace (256 * (ss + 1)) with (256 * ss + 255 + 1) by lia.
    cps_pose (FT_lohi a2 nb NB1 NB2 (s_ft s1) (256 * ss + 255) F1 ltac:(lia)) as (_ & C2 & _). rewrite C2.
    replace (256 * ss + 255 + 1) with (256 * (ss + 1)) by lia.
    assert (L1 : LIVE (s_a2 s1)) by (intros k Hk; rewrite EA1; apply L0; exact Hk).
    pose proof (live_bytes _ L1) as AGR.
    assert (BD1 : zget (s_bd s1) ss = 0) by (rewrite EB1; exact BD0).
    pose proof (step2_exact a2 nb ss (s_bd s1) (s_a1 s1) (s_a2 s1) BB NB1 Hss BD1 P1 AGR cs ce
                  ltac:(intros c Hc; apply (proj1 (CI c Hc))) ltac:(intros c Hc; apply (proj2 (CI c Hc)))) as S2.
    cbv zeta in S2. unfold BzCSewC.B0, BzCSewC.B1 in S2.
    assert (SBS : forall c, 0 <= c < 256 ->
      SBa (fst (fst (ms_copy_bwd (S (Z.to_nat nb)) (fst (fst (ms_copy_fwd (S (Z.to_nat nb)) (s_a1 s1) cs (s_a2 s1) (s_bd s1) nb ss (CLM (256 * ss)))))
                        ce (s_a2 s1) (s_bd s1) nb ss (CLM (256 * (ss + 1)) - 1)))) (256 * c + ss)).
    { destruct (allss a2 nb ss) eqn:AS.
      - destruct S2 as [P2 _]. pose proof (PINV_perm a2 nb BB NB1 _ P2) as [RG2 _].
        intros c Hc p p' A B C. pose proof (ClM_range a2 nb ltac:(lia) (256 * c + ss)). pose proof (ClM_range a2 nb ltac:(lia) (256 * c + ss + 1)).
        rewrite (allss_rot ss Hss AS (rd32 _ p) (rd32 _ p')) by (apply RG2; lia). right; reflexivity.
      - pose proof (step2_sorted a2 nb ss (s_bd s1) (s_a1 s1) BB NB1 N34 Hss BD1 P1 (allss_false a2 nb ss AS) (s_a2 s1) AGR
                      ltac:(intros c Hc Nc; apply DONE1; lia) cs ce ltac:(intros c Hc; apply (proj1 (CI c Hc))) ltac:(intros c Hc; apply (proj2 (CI c Hc)))
                      ltac:(intros c Hc Bc; apply KEEP1; [lia|]; apply (oi_sb _ OV c ss Hc Hss); left; rewrite <- EB1; exact Bc)) as SS.
        cbv zeta in SS. unfold BzCSewC.B0, BzCSewC.B1 in SS. exact SS. }
    destruct (ms_copy_fwd _ _ _ _ _ _ _ _) as [[af csf] jf]. cbn [fst snd] in S2, SBS.
    destruct (ms_copy_bwd _ _ _ _ _ _ _ _) as [[ab ceb] jb]. cbn [fst snd] in S2, SBS.
    cps_destruct S2 as (P2 & MEET & RNG & FRM & _ & _).
    cbn [s_a1 s_a2 s_ft s_bd s_exit]. intros _ PVf PMf.
    (* [comment removed for export] *)
    assert (UNT : forall v, 0 <= v < 65536 -> v mod 256 <> ss -> forall p, CLM v <= p < CLM (v + 1) -> rd32 ab p = rd32 (s_a1 s1) p).
    { intros v Hv Nv p Hp. apply FRM. intros c Hc _ R. apply (R_disjoint a2 nb v (256 * c + ss) p); [| exact Hp| exact R].
      intros ->. apply Nv. apply mod256_of. exact Hss. }
    assert (BIG : forall c, 0 <= c < 256 -> SBa ab (256 * ss + c)).
    { intros c Hc. destruct (Z.eq_dec c ss) as [->|Nc]; [apply SBS; exact Hss|].
      apply (SB_ext a2 nb NB1 N34 (s_a1 s1) ab); [apply DONE1; lia|]. apply UNT; [lia|]. rewrite mod256_of; lia. }
    (* [comment removed for export] *)
    match goal with |- OI (MSS _ ?b _ _ _ _ _ _ _ _) => assert (Q3 : QSND b /\ QMIR b) end.
    { destruct (Z.ltb_spec i 255) as [L|L]; [| rewrite EA1; split; [exact (oi_q _ OV)| exact (oi_ov _ OV)]].
      pose proof (ms_mark_spec a2 nb 256 (s_ft s1) ss 0 F1 Hss ltac:(lia) ltac:(cbn; lia)) as FM.
      rewrite ?(shl8 ss), ?(shl8 (ss + 1)).
      pose proof (FT_lohi a2 nb NB1 NB2 _ (256 * ss) FM ltac:(lia)) as (D1 & _).
      pose proof (ftcell_clear _ _ (ClM_lt a2 nb NB1 NB2 (256 * (ss + 1))) (FM (256 * (ss + 1)) ltac:(lia))) as D2.
      rewrite D1, D2.
      pose proof (ClM_mono a2 nb (256 * ss) (256 * (ss + 1)) ltac:(lia)) as MONO.
      pose proof (ClM_range a2 nb ltac:(lia) (256 * (ss + 1))) as RNG1. pose proof (ClM_range a2 nb ltac:(lia) (256 * ss)) as RNG0.
      set (bS := CLM (256 * ss)) in *. set (bE := CLM (256 * (ss + 1))) in *.
      pose proof (ms_shifts_main (bE - bS) ltac:(lia)) as SHM. cbv zeta in SHM. cps_destruct SHM as (_ & _ & _ & SH).
      set (sh := ms_shifts 40 (bE - bS) 0) in *.
      cps_pose (ms_quad_spec nb qoff N34 QO (Z.to_nat (bE - bS)) (s_a2 s1) ab bS sh (bE - bS - 1)
                    ltac:(intros x Hx; apply (proj1 PMf); lia)
                    ltac:(intros x x' Hx Hx' E; enough (bS + x = bS + x') by lia; apply (proj2 PMf); [lia| lia| exact E])
                    ltac:(intros x Hx; pose proof (SH x ltac:(lia)); lia) ltac:(lia)) as (QV & QF & QM). 
      unfold QSND, QMIR. split; [| apply QM; rewrite EA1; exact (oi_ov _ OV)].
      intros p p' Hp Hp' E LT.
      destruct (Z.eq_dec (rd8 a2 p) ss) as [Ep|Np].
      - (* [comment removed for export] *)
        cps_destruct (big_cover ab ss p PVf Hss Hp Ep) as (q & Hq & Eq). cps_destruct (big_cover ab ss p' PVf Hss Hp' ltac:(congruence)) as (q' & Hq' & Eq').
        rewrite <- Eq, <- Eq' in LT |- *.
        replace q with (bS + (q - bS)) in LT by lia. replace q' with (bS + (q' - bS)) in LT by lia. rewrite !QV in LT by lia.
        assert (q < q'). { destruct (Z.lt_ge_cases q q') as [|G]; [assumption|]. exfalso. pose proof (shiftr_mono (q' - bS) (q - bS) sh ltac:(pose proof (ms_shifts_main (bE - bS) ltac:(lia)) as X; cbv zeta in X; lia) ltac:(lia)). lia. }
        apply (sorted_of_big ab ss PVf Hss BIG); lia.
      - (* [comment removed for export] *)
        assert (NR : forall p0, rd8 a2 p0 <> ss -> forall x, 0 <= x <= bE - bS - 1 -> rd32 ab (bS + x) <> p0).
        { intros p0 Np0 x Hx Ex. apply Np0. rewrite <- Ex. apply (big_rows ab ss); [exact PVf| exact Hss| lia]. }
        rewrite !QF in LT; [| exact Hp'| apply NR; congruence| exact Hp| apply NR; exact Np].
        rewrite EA1 in LT. exact (oi_q _ OV p p' Hp Hp' E LT). }
    destruct Q3 as [Q3a Q3b].
    constructor; cbn [s_a1 s_a2 s_ft s_bd].
    - exact Q3a.
    - exact Q3b.
    - intros c1 c2 Hc1 Hc2. rewrite !zget_zset, EB1. intros OR.
      destruct (Z.eq_dec c2 ss) as [->|N2]; [apply SBS; exact Hc1|].
      destruct (Z.eq_dec c1 ss) as [->|N1].
      + apply (SB_ext a2 nb NB1 N34 (s_a1 s1) ab); [apply DONE1; lia|]. apply UNT; [lia|]. rewrite mod256_of; lia.
      + destruct (Z.eqb_spec c1 ss); [lia|]. destruct (Z.eqb_spec c2 ss); [lia|].
        apply (SB_ext a2 nb NB1 N34 (s_a1 s1) ab); [| apply UNT; [lia| rewrite mod256_of; lia]].
        apply KEEP1; [lia|]. apply (oi_sb _ OV c1 c2 Hc1 Hc2 OR).
    - intros c1 c2 Hc1 Hc2 HS. rewrite !zget_zset, EB1.
      destruct (ms_mark_get 256 (s_ft s1) ss 0 (256 * c1 + c2) ltac:(lia)) as [E|[E (j & Hj & Ev)]]; rewrite E in HS.
      + destruct (FL1 _ HS) as [A|A].
        * destruct (oi_fl _ OV c1 c2 Hc1 Hc2 A) as [C|C]; [left; destruct (Z.eqb_spec c1 ss); [lia| exact C]| right; destruct (Z.eqb_spec c2 ss); [lia| exact C]].
        * left. destruct (Z.eqb_spec c1 ss); lia.
      + right. destruct (Z.eqb_spec c2 ss); lia.
  Qed.

  Theorem ms_bigs_OI : forall n i s, 0 <= i -> i + Z.of_nat n <= 256 -> MIx i s -> OI s ->
    let s' := ms_bigs n ro qoff nb i s in s_exit s' = true \/ (MIx (i + Z.of_nat n) s' /\ OI s').
  Proof.
    induction n as [|n IH]; intros i s Hi Hn IV OV; cbv zeta.
    - cbn [ms_bigs]. right. replace (i + Z.of_nat 0) with i by lia. split; [exact IV| exact OV].
    - rewrite ms_bigs_S. cbv zeta. destruct (ms_big_OI i s ltac:(lia) IV OV) as [EX|[IV' OV']].
      + rewrite EX. left. exact EX.
      + rewrite (mi_exit _ _ _ _ _ _ IV'). replace (i + Z.of_nat (S n)) with (i + 1 + Z.of_nat n) by lia. apply IH; [lia| lia| exact IV'| exact OV'].
  Qed.
End Main.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MainSort.
  Variables (a1 a2 ft ro0 bd0 cs ce sl sh sd : zarr) (qoff nb budget : Z).
  Hypothesis B2 : zbok a2.
  Hypothesis NB : 34 <= nb <= 900000.
  Hypothesis QO : nb + 34 <= qoff.

  Let BBr : forall i, 0 <= rd8 a2 i < 256. Proof. intros i. unfold rd8. apply B2. Qed.

  Theorem mainSort_sorted :
    let m := mainSort a1 a2 ft ro0 bd0 cs ce sl sh sd qoff nb budget in
    mr_budget m <? 0 = false ->
    PINV a2 nb (mr_ptr m) /\
    forall i j, 0 <= i -> i <= j -> j < nb -> lexle (rot (blk a2 nb) (Z.to_nat (rd32 (mr_ptr m) i))) (rot (blk a2 nb) (Z.to_nat (rd32 (mr_ptr m) j))).
  Proof.
    apply mainSort_shape. intros a2a ft2 x1 a1a ft4 x2 bd ro st E1 E2 E3 Est.
    cbn [mr_ptr mr_block mr_budget].
    pose proof (radix1_ft a2 nb qoff BBr ltac:(lia) ltac:(lia) a2 ft ltac:(intros; reflexivity)) as R1.
    cbv zeta in R1. rewrite E1 in R1. cbn [fst snd] in R1. destruct R1 as [AG1 FT2].
    pose proof (zbok_radix1 (Z.to_nat nb) a2 (mft1 ft) qoff (nb-1) (Z.shiftl (rd8 a2 0) 8) B2) as ZB2a.
    rewrite E1 in ZB2a. cbn [fst snd] in ZB2a.
    pose proof (ms_radix1_quad (Z.to_nat nb) a2 (mft1 ft) qoff (nb - 1) (Z.shiftl (rd8 a2 0) 8) ltac:(lia)) as RQ.
    cbv zeta in RQ. rewrite E1 in RQ. cbn [fst snd] in RQ. destruct RQ as [RQ _].
    replace (nb - 1 + 1 - Z.of_nat (Z.to_nat nb)) with 0 in RQ by lia.
    clear E1.
    pose proof (ms_overshoot_spec 34 a2a qoff nb 0 ZB2a ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as OS. cbv zeta in OS.
    change (Z.of_nat 34) with 34 in OS. cps_destruct OS as (OS1 & OS2 & OS3 & _).
    set (a2b := ms_overshoot 34 a2a qoff nb 0) in *.
    assert (AG2 : forall k, 0 <= k < nb -> rd8 a2b k = rd8 a2 k) by (intros k Hk; rewrite OS2 by exact Hk; apply AG1; exact Hk).
    assert (BOV : forall i, 0 <= i < 34 -> rd8 a2b (nb + i) = rd8 a2b i).
    { intros i Hi. rewrite (proj1 (OS1 i ltac:(lia))). symmetry. apply OS2. lia. }
    assert (Q0 : forall z, 0 <= z < nb + 34 -> qrd a2b qoff z = 0).
    { intros z Hz. destruct (Z.lt_ge_cases z nb) as [L|G].
      - rewrite OS3 by lia. apply RQ. lia.
      - replace z with (nb + (z - nb)) by lia. apply (proj2 (OS1 (z - nb) ltac:(lia))). }
    assert (ZB2b : zbok a2b) by (subst a2b; apply zbok_overshoot; exact ZB2a).
    pose proof (ms_accum_ft a2 nb BBr ltac:(lia) ft2 FT2) as FT3.
    set (ft3 := ms_accum 65536 ft2 1) in *.
    pose proof (ms_radix_perm a2 nb BBr ltac:(lia) a1 a2b ft3 AG2 FT3) as R2. cbv zeta in R2.
    rewrite E2 in R2. cbn [fst snd] in R2. cps_destruct R2 as (FT4 & KP & PM1 & FR1). clear E2.
    pose proof (runningOrder_perm bd0 ro0 ft4) as ROP. rewrite E3 in ROP. cbv beta iota zeta in ROP.
    cps_destruct ROP as (BD0 & ROR & ROI). clear E3.
    set (ro1 := ms_shell 8 ro ft4 364) in *.
    set (s0 := MSS a1a a2b ft4 bd cs ce budget 0 (MQL sl sh sd sl sh sd) false) in *.
    assert (MI0 : MI a2 nb ro1 a2b 0 s0).
    { constructor; subst s0; cbn [s_a1 s_a2 s_ft s_bd s_exit].
      - apply (PINV_of_KpM a2 nb ltac:(lia)). exact KP.
      - intros; reflexivity.
      - intros v Hv. left. apply FT4. exact Hv.
      - intros c Hc. left. apply BD0. exact Hc.
      - intros c Hc. rewrite BD0 by exact Hc. split; [intros X; exfalso; exact (X eq_refl)| cps_intros (i' & Hi' & _); lia].
      - reflexivity. }
    assert (OI0 : OI a2 nb qoff s0).
    { constructor; subst s0; cbn [s_a1 s_a2 s_ft s_bd].
      - intros p p' Hp Hp' _ LT. rewrite !Q0 in LT by lia. lia.
      - intros i Hi. rewrite !Q0 by lia. reflexivity.
      - intros c1 c2 Hc1 Hc2. rewrite !BD0 by assumption. intros [X|X]; exfalso; apply X; reflexivity.
      - intros c1 c2 Hc1 Hc2 HS. exfalso. rewrite (FT4 (256 * c1 + c2)) in HS by lia.
        rewrite has_setmask_small in HS; [discriminate|]. pose proof (ClM_range a2 nb ltac:(lia) (256 * c1 + c2)). lia. }
    pose proof (ms_bigs_OI a2 nb qoff ro1 a2b BBr NB QO ROR ROI AG2 BOV 256 0 s0 ltac:(lia) ltac:(cbn; lia) MI0 OI0) as MB.
    cbv zeta in MB. rewrite <- Est in MB. change (0 + Z.of_nat 256) with 256 in MB.
    pose proof (bigs_exit 256 ro1 qoff nb 0 s0 eq_refl) as EXB. rewrite <- Est in EXB.
    intros NEG. destruct MB as [EX|[MIf OIf]].
    { exfalso. pose proof (EXB EX). apply Z.ltb_ge in NEG. lia. }
    pose proof (mi_pinv _ _ _ _ _ _ MIf) as PV. split; [exact PV|].
    apply (sorted_of_buckets a2 nb BBr ltac:(lia) ltac:(lia) _ PV).
    intros v Hv. pose proof (Z.mod_pos_bound v 256 ltac:(lia)) as MR.
    replace v with (256 * (v / 256) + v mod 256) by (symmetry; apply Z.div_mod; lia).
    apply (oi_sb _ _ _ _ OIf); [lia| exact MR|].
    left. apply (proj2 (mi_bd _ _ _ _ _ _ MIf (v / 256) ltac:(lia))).
    cps_destruct (inj_onto (fun i => zget ro1 i) 256 ROR ROI (v / 256) ltac:(lia)) as (i' & Hi' & E). exists i'. split; [exact Hi'| exact E].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End MainSort.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.
