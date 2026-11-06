(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCSortF BzCLemmasFs BzCFactsFs.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCSortF BzCLemmasFs BzCFactsFs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzCQsortF.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

Section Part.
  Variables (ec : zarr) (med lo hi : Z).

  (* [comment removed for export] *)
  Fixpoint cnt (fm : zarr) (a : Z) (n : nat) : Z :=
    match n with
    | O => 0
    | S n' => (if rd32 ec (rd32 fm a) =? med then 1 else 0) + cnt fm (a + 1) n'
    end.

  Lemma cnt_nonneg : forall n fm a, 0 <= cnt fm a n.
  Proof. induction n; intros; cbn; [lia|]. specialize (IHn fm (a+1)). destruct (_ =? _); lia. Qed.

  Lemma cnt_ext : forall n fm fm' a,
    (forall k, a <= k < a + Z.of_nat n -> rd32 fm' k = rd32 fm k) -> cnt fm' a n = cnt fm a n.
  Proof.
    induction n as [|n IH]; intros fm fm' a H; cbn; [reflexivity|].
    rewrite (H a) by lia. rewrite (IH fm fm' (a+1)); [reflexivity|]. intros k Hk. apply H. lia.
  Qed.

  Lemma cnt_head : forall n fm a, cnt fm a (S n) = (if rd32 ec (rd32 fm a) =? med then 1 else 0) + cnt fm (a+1) n.
  Proof. reflexivity. Qed.

  Lemma cnt_snoc : forall n fm a, cnt fm a (S n) = cnt fm a n + (if rd32 ec (rd32 fm (a + Z.of_nat n)) =? med then 1 else 0).
  Proof.
    induction n as [|n IH]; intros fm a.
    - cbn. replace (a + 0) with a by lia. lia.
    - rewrite cnt_head. rewrite (IH fm (a+1)). rewrite cnt_head.
      replace (a + 1 + Z.of_nat n) with (a + Z.of_nat (S n)) by lia. lia.
  Qed.

  Lemma cnt_pos_at : forall n fm a x, a <= x < a + Z.of_nat n -> rd32 ec (rd32 fm x) = med -> 1 <= cnt fm a n.
  Proof.
    induction n as [|n IH]; intros fm a x Hx Hm; [lia|].
    rewrite cnt_head. pose proof (cnt_nonneg n fm (a+1)).
    destruct (Z.eq_dec x a) as [->|NE].
    - rewrite Hm, Z.eqb_refl. lia.
    - assert (1 <= cnt fm (a+1) n) by (apply (IH fm (a+1) x); lia). destruct (_ =? _); lia.
  Qed.

  (* [comment removed for export] *)
  Definition PI (p : fpart) : Prop :=
    lo <= fp_ltLo p /\ fp_ltLo p <= fp_unLo p /\ fp_unLo p <= fp_unHi p + 1 /\
    fp_unHi p <= fp_gtHi p /\ fp_gtHi p <= hi /\
    1 <= (fp_ltLo p - lo) + (hi - fp_gtHi p) + cnt (fp_fm p) (fp_unLo p) (Z.to_nat (fp_unHi p - fp_unLo p + 1)).

  Definition key (fm : zarr) (i : Z) : Z := rd32 ec (rd32 fm i).


  Lemma qs_lo_ok : forall f p,
    PI p -> (Z.to_nat (fp_unHi p - fp_unLo p + 1) < f)%nat ->
    PI (fpart_lo f ec med p) /\ fp_unHi (fpart_lo f ec med p) = fp_unHi p /\ fp_gtHi (fpart_lo f ec med p) = fp_gtHi p /\
    fp_ltLo p <= fp_ltLo (fpart_lo f ec med p) /\ fp_unLo p <= fp_unLo (fpart_lo f ec med p) /\
    (fp_unHi (fpart_lo f ec med p) < fp_unLo (fpart_lo f ec med p) \/ med < key (fp_fm (fpart_lo f ec med p)) (fp_unLo (fpart_lo f ec med p))).
  Proof.
    induction f as [|f IH]; intros p HP Hf; [lia|].
    rewrite fpart_lo_S. cbn zeta.
    destruct (Z.ltb_spec (fp_unHi p) (fp_unLo p)) as [LT|GE].
    { repeat split; try apply HP; first [lia | left; lia]. }
    cps_destruct HP as (A & B & C & D & E & F).
    assert (HN : Z.to_nat (fp_unHi p - fp_unLo p + 1) = S (Z.to_nat (fp_unHi p - (fp_unLo p + 1) + 1))) by lia.
    rewrite HN, cnt_head in F.
    destruct (Z.eqb_spec (rd32 ec (rd32 (fp_fm p) (fp_unLo p)) - med) 0) as [EQ|NE].
    - match goal with |- PI (fpart_lo f ec med ?q) /\ _ => specialize (IH q) end.
      cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in IH.
      cps_destruct IH as (P1 & P2 & P3 & P5 & P6 & P4); [| lia |].
      { unfold PI; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]. repeat split; try lia.
        rewrite (cnt_ext _ (fp_fm p)).
        2:{ intros k Hk. unfold fswap. rewrite !rd32_wr32_other by lia. reflexivity. }
        replace (rd32 ec (rd32 (fp_fm p) (fp_unLo p)) =? med) with true in F by (symmetry; apply Z.eqb_eq; lia). lia. }
      repeat split; try apply P1; try lia.
    - destruct (Z.ltb_spec 0 (rd32 ec (rd32 (fp_fm p) (fp_unLo p)) - med)) as [GT|LE].
      + split. { unfold PI. repeat split; try lia. rewrite HN, cnt_head. exact F. }
        split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. right; unfold key; lia.
      + match goal with |- PI (fpart_lo f ec med ?q) /\ _ => specialize (IH q) end.
        cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in IH.
        cps_destruct IH as (P1 & P2 & P3 & P5 & P6 & P4); [| lia |].
        { unfold PI; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]. repeat split; try lia.
          replace (rd32 ec (rd32 (fp_fm p) (fp_unLo p)) =? med) with false in F by (symmetry; apply Z.eqb_neq; lia). lia. }
        repeat split; try apply P1; try lia.
  Qed.

  Lemma qs_hi_ok : forall f p,
    PI p -> (Z.to_nat (fp_unHi p - fp_unLo p + 1) < f)%nat ->
    (fp_unHi p < fp_unLo p \/ med < key (fp_fm p) (fp_unLo p)) ->
    PI (fpart_hi f ec med p) /\ fp_unLo (fpart_hi f ec med p) = fp_unLo p /\ fp_ltLo (fpart_hi f ec med p) = fp_ltLo p /\
    fp_gtHi (fpart_hi f ec med p) <= fp_gtHi p /\ fp_unHi (fpart_hi f ec med p) <= fp_unHi p /\
    (fp_unHi (fpart_hi f ec med p) < fp_unLo (fpart_hi f ec med p) \/
     (key (fp_fm (fpart_hi f ec med p)) (fp_unHi (fpart_hi f ec med p)) < med /\
      med < key (fp_fm (fpart_hi f ec med p)) (fp_unLo (fpart_hi f ec med p)))).
  Proof.
    induction f as [|f IH]; intros p HP Hf HK; [lia|].
    rewrite fpart_hi_S. cbn zeta.
    destruct (Z.ltb_spec (fp_unHi p) (fp_unLo p)) as [LT|GE].
    { repeat split; try apply HP; first [lia | left; lia]. }
    destruct HK as [HK|HK]; [lia|].
    cps_destruct HP as (A & B & C & D & E & F).
    assert (HN : Z.to_nat (fp_unHi p - fp_unLo p + 1) = S (Z.to_nat (fp_unHi p - 1 - fp_unLo p + 1))) by lia.
    rewrite HN, cnt_snoc in F.
    replace (fp_unLo p + Z.of_nat (Z.to_nat (fp_unHi p - 1 - fp_unLo p + 1))) with (fp_unHi p) in F by lia.
    destruct (Z.eqb_spec (rd32 ec (rd32 (fp_fm p) (fp_unHi p)) - med) 0) as [EQ|NE].
    - assert (NEQ : fp_unLo p <> fp_unHi p).
      { intros X. unfold key in HK. rewrite X in HK. lia. }
      match goal with |- PI (fpart_hi f ec med ?q) /\ _ => specialize (IH q) end.
      cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in IH.
      cps_destruct IH as (P1 & P2 & P3 & P5 & P6 & P4); [| lia | |].
      { unfold PI; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]. repeat split; try lia.
        rewrite (cnt_ext _ (fp_fm p)).
        2:{ intros k Hk. unfold fswap. rewrite !rd32_wr32_other by lia. reflexivity. }
        replace (rd32 ec (rd32 (fp_fm p) (fp_unHi p)) =? med) with true in F by (symmetry; apply Z.eqb_eq; lia). lia. }
      { right. unfold key in *. unfold fswap. rewrite !rd32_wr32_other by lia. exact HK. }
      repeat split; try apply P1; try lia.
    - destruct (Z.ltb_spec (rd32 ec (rd32 (fp_fm p) (fp_unHi p)) - med) 0) as [LTm|GEm].
      + split. { unfold PI. repeat split; try lia. rewrite HN, cnt_snoc.
                 replace (fp_unLo p + Z.of_nat (Z.to_nat (fp_unHi p - 1 - fp_unLo p + 1))) with (fp_unHi p) by lia. exact F. }
        split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. right; unfold key in *; lia.
      + match goal with |- PI (fpart_hi f ec med ?q) /\ _ => specialize (IH q) end.
        cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in IH.
        cps_destruct IH as (P1 & P2 & P3 & P5 & P6 & P4); [| lia | |].
        { unfold PI; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]. repeat split; try lia.
          replace (rd32 ec (rd32 (fp_fm p) (fp_unHi p)) =? med) with false in F by (symmetry; apply Z.eqb_neq; lia). lia. }
        { right. exact HK. }
        repeat split; try apply P1; try lia.
  Qed.

  Lemma qs_loop_ok : forall f sz p,
    PI p -> (Z.to_nat (fp_unHi p - fp_unLo p + 1) <= sz)%nat -> (Z.to_nat (fp_unHi p - fp_unLo p + 1) < 2 * f)%nat ->
    PI (fpart_loop f sz ec med p) /\ fp_unLo (fpart_loop f sz ec med p) = fp_unHi (fpart_loop f sz ec med p) + 1 /\
    fp_ltLo p <= fp_ltLo (fpart_loop f sz ec med p) /\ fp_gtHi (fpart_loop f sz ec med p) <= fp_gtHi p.
  Proof.
    induction f as [|f IH]; intros sz p HP Hsz Hf; [lia|].
    rewrite fpart_loop_S. cbn zeta.
    cps_pose (qs_lo_ok (S sz) p HP ltac:(lia)) as (L1 & L2 & L3 & L5 & L6 & L4).
    set (p1 := fpart_lo (S sz) ec med p) in *.
    assert (S1 : (Z.to_nat (fp_unHi p1 - fp_unLo p1 + 1) < S sz)%nat).
    { cps_destruct L1 as (_ & _ & C1 & _). rewrite L2. cps_destruct HP as (_ & B0 & _). lia. }
    cps_pose (qs_hi_ok (S sz) p1 L1 S1 L4) as (M1 & M2 & M3 & M5 & M6 & M4).
    set (p2 := fpart_hi (S sz) ec med p1) in *.
    destruct (Z.ltb_spec (fp_unHi p2) (fp_unLo p2)) as [LT|GE].
    { split; [exact M1|]. cps_destruct M1 as (_ & _ & C2 & _). repeat split; lia. }
    destruct M4 as [M4|[K1 K2]]; [lia|].
    assert (NE : fp_unLo p2 < fp_unHi p2).
    { destruct (Z.eq_dec (fp_unLo p2) (fp_unHi p2)) as [X|X]; [|lia]. rewrite X in K2. lia. }
    cps_destruct M1 as (A & B & C & D & E & F).
    match goal with |- PI (fpart_loop f sz ec med ?q) /\ _ => specialize (IH sz q) end.
    cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in IH.
    cps_destruct IH as (P1 & P2 & P3 & P4); [| lia | lia |].
    { unfold PI; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]. repeat split; try lia.
      assert (HN : Z.to_nat (fp_unHi p2 - fp_unLo p2 + 1) = S (S (Z.to_nat (fp_unHi p2 - 1 - (fp_unLo p2 + 1) + 1)))) by lia.
      rewrite HN, cnt_head, cnt_snoc in F.
      replace (fp_unLo p2 + 1 + Z.of_nat (Z.to_nat (fp_unHi p2 - 1 - (fp_unLo p2 + 1) + 1))) with (fp_unHi p2) in F by lia.
      unfold key in K1, K2.
      replace (rd32 ec (rd32 (fp_fm p2) (fp_unLo p2)) =? med) with false in F by (symmetry; apply Z.eqb_neq; lia).
      replace (rd32 ec (rd32 (fp_fm p2) (fp_unHi p2)) =? med) with false in F by (symmetry; apply Z.eqb_neq; lia).
      rewrite (cnt_ext _ (fp_fm p2)); [lia|].
      intros k Hk. unfold fswap. rewrite !rd32_wr32_other by lia. reflexivity. }
    repeat split; try apply P1; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma qs_part : forall fm x,
    lo <= x <= hi -> med = key fm x ->
    let sz := Z.to_nat (hi - lo + 1) in
    let p := fpart_loop (S sz) sz ec med (FP fm lo hi lo hi) in
    lo <= fp_ltLo p /\ fp_ltLo p <= fp_unLo p /\ fp_unLo p = fp_unHi p + 1 /\ fp_unHi p <= fp_gtHi p /\ fp_gtHi p <= hi /\
    1 <= (fp_ltLo p - lo) + (hi - fp_gtHi p).
  Proof.
    intros fm x Hx Hm. cbn zeta.
    assert (P0 : PI (FP fm lo hi lo hi)).
    { unfold PI; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]. repeat split; try lia.
      pose proof (cnt_pos_at (Z.to_nat (hi - lo + 1)) fm lo x ltac:(lia) ltac:(unfold key in Hm; congruence)). lia. }
    cps_pose (qs_loop_ok (S (Z.to_nat (hi - lo + 1))) (Z.to_nat (hi - lo + 1)) (FP fm lo hi lo hi) P0
                  ltac:(cbn [fp_unLo fp_unHi]; lia) ltac:(cbn [fp_unLo fp_unHi]; lia)) as (P1 & P2 & P3 & P4).
    cbn [fp_ltLo fp_gtHi] in P3, P4.
    cps_destruct P1 as (A & B & C & D & E & F).
    replace (Z.to_nat (fp_unHi _ - fp_unLo _ + 1)) with 0%nat in F by lia. cbn [cnt] in F.
    repeat split; lia.
  Qed.
End Part.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stack.
  Variables (ec : zarr) (nb W : Z).

  Definition elo (q : fqs) (i : Z) : Z := zget (fq_slo q) i.
  Definition ehi (q : fqs) (i : Z) : Z := zget (fq_shi q) i.
  (* [comment removed for export] *)
  Definition ew (q : fqs) (i : Z) : Z := ehi q i - elo q i + 2.

  Definition SINV (q : fqs) : Prop :=
    0 <= fq_sp q /\
    (forall i, 0 <= i < fq_sp q -> 0 <= elo q i /\ elo q i <= ehi q i + 1 /\ ehi q i < nb) /\
    (forall i, 0 <= i -> i + 1 < fq_sp q -> ew q (i + 1) <= ew q i) /\
    (forall i, 0 <= i -> i + 2 < fq_sp q -> ew q (i + 2) <= ew q i / 2) /\
    (0 < fq_sp q -> ew q 0 <= W).

  (* [comment removed for export] *)
  Fixpoint phi_n (q : fqs) (n : nat) : Z :=
    match n with
    | O => 0
    | S n' => phi_n q n' + (2 * (ew q (Z.of_nat n') - 1) + 1)
    end.
  Definition phi (q : fqs) : Z := phi_n q (Z.to_nat (fq_sp q)).

  Lemma phi_n_ext : forall n q q', (forall i, 0 <= i < Z.of_nat n -> ew q' i = ew q i) -> phi_n q' n = phi_n q n.
  Proof.
    induction n as [|n IH]; intros q q' H; cbn [phi_n]; [reflexivity|].
    rewrite (IH q q') by (intros; apply H; lia). rewrite H by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)

  Lemma pop_ok : forall q q',
    SINV q -> 0 < fq_sp q -> fq_sp q' = fq_sp q - 1 ->
    (forall i, 0 <= i < fq_sp q - 1 -> elo q' i = elo q i /\ ehi q' i = ehi q i) ->
    SINV q' /\ phi q' <= phi q - 1.
  Proof.
    (intros q q'; cps_intros (S0 & S1 & S2 & S3 & S4); intros Hsp Hsp' HE).
    assert (EW : forall i, 0 <= i < fq_sp q - 1 -> ew q' i = ew q i).
    { intros i Hi. unfold ew. destruct (HE i Hi) as [-> ->]. reflexivity. }
    split.
    - unfold SINV. rewrite Hsp'. repeat split.
      + lia.
      + destruct (HE i ltac:(lia)) as [-> _]. apply S1; lia.
      + destruct (HE i ltac:(lia)) as [-> ->]. apply S1; lia.
      + destruct (HE i ltac:(lia)) as [_ ->]. apply S1; lia.
      + intros i Hi Hi2. rewrite !EW by lia. apply S2; lia.
      + intros i Hi Hi2. rewrite !EW by lia. apply S3; lia.
      + intros Hp. rewrite EW by lia. apply S4. lia.
    - unfold phi. rewrite Hsp'.
      replace (Z.to_nat (fq_sp q)) with (S (Z.to_nat (fq_sp q - 1))) by lia. cbn [phi_n].
      rewrite (phi_n_ext (Z.to_nat (fq_sp q - 1)) q q') by (intros; apply EW; lia).
      assert (1 <= ew q (Z.of_nat (Z.to_nat (fq_sp q - 1)))).
      { unfold ew. cps_destruct (S1 (Z.of_nat (Z.to_nat (fq_sp q - 1))) ltac:(lia)) as (_ & B & _). lia. }
      lia.
  Qed.

  Lemma push2_ok : forall q q',
    SINV q -> 0 < fq_sp q -> fq_sp q' = fq_sp q + 1 ->
    (forall i, 0 <= i < fq_sp q - 1 -> elo q' i = elo q i /\ ehi q' i = ehi q i) ->
    let t := fq_sp q - 1 in
    0 <= elo q' t -> elo q' t <= ehi q' t + 1 -> ehi q' t < nb ->
    0 <= elo q' (t + 1) -> elo q' (t + 1) <= ehi q' (t + 1) + 1 -> ehi q' (t + 1) < nb ->
    ew q' (t + 1) <= ew q' t ->
    (ew q' t - 1) + (ew q' (t + 1) - 1) <= (ew q t - 1) - 1 ->
    SINV q' /\ phi q' <= phi q - 1.
  Proof.
    (intros q q'; cps_intros (S0 & S1 & S2 & S3 & S4); intros Hsp Hsp' HE t A1 A2 A3 B1 B2 B3 MON SUM).
    assert (EW : forall i, 0 <= i < fq_sp q - 1 -> ew q' i = ew q i).
    { intros i Hi. unfold ew. destruct (HE i Hi) as [-> ->]. reflexivity. }
    assert (Wt : 1 <= ew q' (t + 1)) by (unfold ew in *; lia).
    split.
    - unfold SINV. rewrite Hsp'. split; [lia|]. split.
      { intros i Hi. destruct (Z.lt_ge_cases i t) as [L|G].
        - destruct (HE i ltac:(lia)) as [-> ->]. apply S1; lia.
        - destruct (Z.eq_dec i t) as [->|N1]; [repeat split; assumption|].
          replace i with (t + 1) by lia. repeat split; assumption. }
      split.
      { intros i Hi Hi2. destruct (Z.lt_ge_cases (i + 1) t) as [L|G].
        - rewrite !EW by lia. apply S2; lia.
        - destruct (Z.eq_dec (i + 1) t) as [E|N1].
          + (* [comment removed for export] *)
            assert (M0 : ew q (i + 1) <= ew q i) by (apply S2; lia).
            rewrite E in *. rewrite (EW i) by lia. lia.
          + replace i with t by lia. exact MON. }
      split.
      { intros i Hi Hi2. destruct (Z.lt_ge_cases (i + 2) t) as [L|G].
        - rewrite !EW by lia. apply S3; lia.
        - destruct (Z.eq_dec (i + 2) t) as [E|N1].
          + assert (M0 : ew q (i + 2) <= ew q i / 2) by (apply S3; lia).
            rewrite E in *. rewrite (EW i) by lia. lia.
          + (* [comment removed for export] *)
            assert (E : i + 1 = t) by lia.
            assert (M0 : ew q (i + 1) <= ew q i) by (apply S2; lia).
            rewrite E in *. replace (i + 2) with (t + 1) by lia. rewrite (EW i) by lia.
            assert (M1 : ew q' (t + 1) <= ew q t / 2) by (apply Z.div_le_lower_bound; lia).
            eapply Z.le_trans; [exact M1|]. apply Z.div_le_mono; lia. }
      { intros Hp. destruct (Z.eq_dec t 0) as [E|N1].
        - rewrite <- E. assert (ew q t <= W) by (rewrite E; apply S4; lia). lia.
        - rewrite EW by lia. apply S4. lia. }
    - unfold phi. rewrite Hsp'.
      replace (Z.to_nat (fq_sp q + 1)) with (S (S (Z.to_nat t))) by lia.
      replace (Z.to_nat (fq_sp q)) with (S (Z.to_nat t)) by lia. cbn [phi_n].
      rewrite (phi_n_ext (Z.to_nat t) q q') by (intros; apply EW; lia).
      replace (Z.of_nat (S (Z.to_nat t))) with (t + 1) by lia.
      replace (Z.of_nat (Z.to_nat t)) with t by lia. lia.
  Qed.
End Stack.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section It.
  Variables (ec : zarr) (nb W : Z).

  Lemma zz1 : forall a i v w, zget (zset (zset a i v) (i+1) w) i = v.
  Proof. intros. rewrite zget_zset_other by lia. apply zget_zset_same. Qed.
  Lemma zz2 : forall a i v w, zget (zset (zset a i v) (i+1) w) (i+1) = w.
  Proof. intros. apply zget_zset_same. Qed.
  Lemma zz0 : forall a i v w j, j < i -> zget (zset (zset a i v) (i+1) w) j = zget a j.
  Proof. intros. rewrite !zget_zset_other by lia. reflexivity. Qed.

  Lemma qs_iter_ok : forall q, SINV nb W q -> 0 < fq_sp q -> SINV nb W (fqs_iter ec q) /\ phi (fqs_iter ec q) <= phi q - 1.
  Proof.
    intros q SI Hsp.
    cps_pose SI as (S0 & S1 & S2 & S3 & S4).
    cps_destruct (S1 (fq_sp q - 1) ltac:(lia)) as (E1 & E2 & E3). unfold elo, ehi in E1, E2, E3.
    unfold fqs_iter.
    set (lo := zget (fq_slo q) (fq_sp q - 1)) in *. set (hi := zget (fq_shi q) (fq_sp q - 1)) in *.
    destruct (Z.ltb_spec (hi - lo) 10) as [SM|BIG].
    { apply pop_ok; [exact SI | exact Hsp | reflexivity |]. intros i Hi. unfold elo, ehi. cbn [fq_slo fq_shi]. split; reflexivity. }
    set (r3 := ((fq_r q * 7621 + 1) mod 32768) mod 3).
    set (med := if r3 =? 0 then _ else _).
    assert (HX : exists x, lo <= x <= hi /\ med = key ec (fq_fm q) x).
    { subst med. destruct (r3 =? 0). { exists lo. split; [lia|reflexivity]. }
      destruct (r3 =? 1). 2:{ exists hi. split; [lia|reflexivity]. }
      exists (Z.shiftr (lo + hi) 1). split; [|reflexivity].
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
      split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
    cps_destruct HX as (x & Hx & Hmed).
    pose proof (qs_part ec med lo hi (fq_fm q) x Hx Hmed) as PP. cbn zeta in PP.
    set (p := fpart_loop _ _ ec med _) in *.
    cps_destruct PP as (A & B & C & D & E & F).
    destruct (Z.ltb_spec (fp_gtHi p) (fp_ltLo p)) as [NOP|PUSH].
    { apply pop_ok; [exact SI | exact Hsp | reflexivity |]. intros i Hi. unfold elo, ehi. cbn [fq_slo fq_shi]. split; reflexivity. }
    set (fm2 := fvswap _ _ _ _ _).
    set (a := fp_unLo p - fp_ltLo p). set (c := fp_gtHi p - fp_unHi p).
    assert (AC : 0 <= a /\ 0 <= c /\ a + c <= hi - lo) by (subst a c; lia).
    replace (lo + fp_unLo p - fp_ltLo p - 1) with (lo + a - 1) by lia.
    set (q2 := {| fq_fm := fm2; fq_sp := fq_sp q - 1; fq_slo := fq_slo q; fq_shi := fq_shi q; fq_r := _ |}).
    assert (GEN : forall l1 h1 l2 h2, 0 <= l1 -> l1 <= h1 + 1 -> h1 < nb -> 0 <= l2 -> l2 <= h2 + 1 -> h2 < nb ->
              h2 - l2 <= h1 - l1 -> (h1 - l1 + 1) + (h2 - l2 + 1) <= (hi - lo + 1) - 1 ->
              SINV nb W (fpush (fpush q2 l1 h1) l2 h2) /\ phi (fpush (fpush q2 l1 h1) l2 h2) <= phi q - 1).
    { intros l1 h1 l2 h2 G1 G2 G3 G4 G5 G6 G7 G8.
      apply push2_ok; try assumption; unfold ew, elo, ehi; cbn [fpush fq_sp fq_slo fq_shi q2];
        rewrite ?zz1, ?zz2; try lia.
      intros i Hi. rewrite !zz0 by lia. split; reflexivity. }
    destruct (Z.ltb_spec (hi - (hi - c + 1)) (lo + a - 1 - lo)) as [L|G]; apply GEN; lia.
  Qed.

  Lemma qs_loop_inv : forall v q, SINV nb W q -> SINV nb W (fqs_loop v ec q).
  Proof.
    induction v as [|v IH]; intros q SI; [exact SI|].
    rewrite fqs_loop_S. destruct (Z.ltb_spec 0 (fq_sp q)); [|exact SI].
    apply IH. apply qs_iter_ok; assumption.
  Qed.

  Lemma phi_ge_sp : forall q, SINV nb W q -> fq_sp q <= phi q.
  Proof.
    (intros q; cps_intros (S0 & S1 & _)). unfold phi.
    assert (G : forall n, Z.of_nat n <= fq_sp q -> Z.of_nat n <= phi_n q n).
    { induction n as [|n IH]; intros Hn; cbn [phi_n]; [lia|].
      assert (1 <= ew q (Z.of_nat n)). { unfold ew. cps_destruct (S1 (Z.of_nat n) ltac:(lia)) as (_ & X & _). lia. }
      specialize (IH ltac:(lia)). lia. }
    specialize (G (Z.to_nat (fq_sp q)) ltac:(lia)). lia.
  Qed.

  Lemma qs_loop_term : forall f q, SINV nb W q -> phi q <= Z.of_nat f -> fq_sp (fqs_loop f ec q) <= 0.
  Proof.
    induction f as [|f IH]; intros q SI Hphi.
    - cbn [fqs_loop]. pose proof (phi_ge_sp q SI). lia.
    - rewrite fqs_loop_S. destruct (Z.ltb_spec 0 (fq_sp q)); [|lia].
      destruct (qs_iter_ok q SI ltac:(lia)) as [SI' PH]. apply IH; [exact SI'|lia].
  Qed.

  Lemma qs_depth_chain : forall q, SINV nb W q -> 0 <= W -> forall k : nat,
    (2 * Z.of_nat k < fq_sp q -> ew q (2 * Z.of_nat k) <= W / 2 ^ Z.of_nat k) /\
    (2 * Z.of_nat k + 1 < fq_sp q -> ew q (2 * Z.of_nat k + 1) <= W / 2 ^ Z.of_nat k).
  Proof.
    (intros q; cps_intros (S0 & S1 & S2 & S3 & S4); intros HW). induction k as [|k IH].
    - cbn [Z.of_nat Z.pow Z.mul Z.add]. rewrite Z.div_1_r. split; intros Hk.
      + apply S4. lia.
      + pose proof (S2 0 ltac:(lia) ltac:(lia)) as M. cbn [Z.add] in M. specialize (S4 ltac:(lia)). lia.
    - destruct IH as [IH1 IH2].
      replace (2 ^ Z.of_nat (S k)) with (2 ^ Z.of_nat k * 2) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
      assert (PK : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
      split; intros Hk.
      + specialize (IH1 ltac:(lia)). pose proof (S3 (2 * Z.of_nat k) ltac:(lia) ltac:(lia)) as M.
        replace (2 * Z.of_nat (S k)) with (2 * Z.of_nat k + 2) by lia.
        rewrite <- Z.div_div by lia. eapply Z.le_trans; [exact M|]. apply Z.div_le_mono; lia.
      + specialize (IH2 ltac:(lia)). pose proof (S3 (2 * Z.of_nat k + 1) ltac:(lia) ltac:(lia)) as M.
        replace (2 * Z.of_nat (S k) + 1) with (2 * Z.of_nat k + 1 + 2) by lia.
        rewrite <- Z.div_div by lia. eapply Z.le_trans; [exact M|]. apply Z.div_le_mono; lia.
  Qed.

  Lemma qs_depth : forall q, SINV nb W q -> 0 <= W < 2 ^ 49 -> fq_sp q <= 98.
  Proof.
    intros q SI HW. destruct (Z.le_gt_cases (fq_sp q) 98) as [|GT]; [assumption|exfalso].
    destruct (qs_depth_chain q SI ltac:(lia) 49%nat) as [C1 _].
    specialize (C1 ltac:(cbn; lia)).
    rewrite Z.div_small in C1 by (cbn in HW |- *; lia).
    cps_destruct SI as (S0 & S1 & _). cps_destruct (S1 (2 * Z.of_nat 49) ltac:(cbn; lia)) as (_ & X & _).
    unfold ew in C1. lia.
  Qed.
End It.

(* [comment removed for export] *)
Theorem qsort_ok_intro : forall nb fm ec slo shi l r,
  0 <= l -> l <= r + 1 -> r < nb -> nb <= 2 ^ 40 -> qsort_ok nb fm ec slo shi l r.
Proof.
  intros nb fm ec slo shi l r Hl Hlr Hr Hnb. unfold qsort_ok. cbn zeta.
  set (q0 := {| fq_fm := fm; fq_sp := 1; fq_slo := zset slo 0 l; fq_shi := zset shi 0 r; fq_r := 0 |}).
  assert (SI : SINV nb (r - l + 2) q0).
  { unfold SINV, ew, elo, ehi; cbn [fq_sp fq_slo fq_shi q0]. split; [lia|]. split.
    { intros i Hi. replace i with 0 by lia. rewrite !zget_zset_same. lia. }
    split; [intros; lia|]. split; [intros; lia|]. intros _. rewrite !zget_zset_same. lia. }
  split.
  - intros v Hsp. pose proof (qs_loop_inv ec nb (r - l + 2) v q0 SI) as SI'.
    split; [apply (qs_depth nb (r - l + 2)); [exact SI'|lia]|].
    cps_destruct SI' as (_ & S1 & _). cps_destruct (S1 (fq_sp (fqs_loop v ec q0) - 1) ltac:(lia)) as (X1 & X2 & X3).
    unfold elo, ehi in *. lia.
  - apply (qs_loop_term ec nb (r - l + 2)); [exact SI|].
    unfold phi, fqs_fuel. cbn [fq_sp q0]. change (Z.to_nat 1) with 1%nat. cbn [phi_n].
    unfold ew, elo, ehi; cbn [fq_slo fq_shi q0]. rewrite !zget_zset_same. lia.
Qed.
End BzCQsortF.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCPermF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2.BzCQsortF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Definition frame_out (fm fm' : zarr) (lo hi : Z) : Prop := forall x, x < lo \/ hi < x -> rd32 fm' x = rd32 fm x.

Lemma frame_out_refl : forall fm lo hi, frame_out fm fm lo hi.
Proof. intros fm lo hi x _. reflexivity. Qed.
Lemma frame_out_trans : forall f1 f2 f3 lo hi, frame_out f1 f2 lo hi -> frame_out f2 f3 lo hi -> frame_out f1 f3 lo hi.
Proof. intros f1 f2 f3 lo hi A B x Hx. rewrite B, A by exact Hx. reflexivity. Qed.
Lemma frame_out_widen : forall f1 f2 lo hi lo' hi', frame_out f1 f2 lo hi -> lo' <= lo -> hi <= hi' -> frame_out f1 f2 lo' hi'.
Proof. intros f1 f2 lo hi lo' hi' A B C x Hx. apply A. lia. Qed.
Lemma frame_out_fswap : forall fm a b lo hi, lo <= a <= hi -> lo <= b <= hi -> frame_out fm (fswap fm a b) lo hi.
Proof. intros fm a b lo hi Ha Hb x Hx. unfold fswap. rewrite !rd32_wr32_other by lia. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fvswap_perm_frame : forall f fm nb p1 p2 n lo hi,
  fm_perm fm nb -> nb <= 4294967296 -> 0 <= lo -> hi < nb ->
  lo <= p1 -> p1 + n <= hi + 1 -> lo <= p2 -> p2 + n <= hi + 1 ->
  fm_perm (fvswap f fm p1 p2 n) nb /\ frame_out fm (fvswap f fm p1 p2 n) lo hi.
Proof.
  induction f as [|f IH]; intros fm nb p1 p2 n lo hi PM NB Hlo Hhi A1 A2 B1 B2.
  - cbn [fvswap]. split; [exact PM | apply frame_out_refl].
  - rewrite fvswap_S. destruct (Z.ltb_spec 0 n) as [Hn|Hn]; [|split; [exact PM | apply frame_out_refl]].
    destruct (IH (fswap fm p1 p2) nb (p1 + 1) (p2 + 1) (n - 1) lo hi) as [P F];
      [apply fm_perm_fswap; try assumption; lia | lia | lia | lia | lia | lia | lia | lia |].
    split; [exact P|]. eapply frame_out_trans; [|exact F]. apply frame_out_fswap; lia.
Qed.

(* [comment removed for export] *)
Section FSS.
  Variables (ec : zarr) (nb : Z).
  Hypothesis NB : nb <= 4294967296.

  (* [comment removed for export] *)
  Lemma hole_step : forall fm j step tmp,
    0 < step -> 0 <= tmp < 4294967296 -> 0 <= rd32 fm j < 4294967296 ->
    forall x, rd32 (wr32 (wr32 fm (j - step) (rd32 fm j)) j tmp) x = rd32 (fswap (wr32 fm (j - step) tmp) (j - step) j) x.
  Proof.
    intros fm j step tmp Hs Ht Hj x. unfold fswap.
    rewrite (rd32_wr32_other fm (j - step) tmp j) by lia. rewrite rd32_wr32_same by lia.
    destruct (Z.eq_dec x j) as [->|NJ].
    - rewrite !rd32_wr32_same by lia. reflexivity.
    - rewrite (rd32_wr32_other _ j tmp x) by lia. rewrite (rd32_wr32_other _ j tmp x) by lia.
      destruct (Z.eq_dec x (j - step)) as [->|NH].
      + rewrite !rd32_wr32_same by lia. reflexivity.
      + rewrite !rd32_wr32_other by lia. reflexivity.
  Qed.

  Lemma fss_in_hole : forall fuel fm et j hi step tmp lo fm0,
    0 < step -> 0 <= lo -> hi < nb -> lo <= j - step <= hi -> 0 <= tmp < 4294967296 ->
    fm_perm (wr32 fm (j - step) tmp) nb -> frame_out fm0 (wr32 fm (j - step) tmp) lo hi ->
    let r := fss_in fuel fm ec et j hi step in
    lo <= snd r - step <= hi /\ fm_perm (wr32 (fst r) (snd r - step) tmp) nb /\ frame_out fm0 (wr32 (fst r) (snd r - step) tmp) lo hi.
  Proof.
    induction fuel as [|fuel IH]; intros fm et j hi step tmp lo fm0 Hs Hlo Hhi Hj Ht PM FR; cbn zeta.
    - cbn [fss_in fst snd]. split; [lia|]. split; [exact PM | exact FR].
    - rewrite fss_in_S. destruct (Sumbool.sumbool_of_bool ((j <=? hi) && (rd32 ec (rd32 fm j) <? et))) as [C|C]; rewrite C.
      + apply andb_prop in C. destruct C as [C1 _]. apply Z.leb_le in C1.
        assert (RJ : 0 <= rd32 fm j < nb).
        { rewrite <- (rd32_wr32_other fm (j - step) tmp j) by lia. apply (proj1 PM). lia. }
        specialize (IH (wr32 fm (j - step) (rd32 fm j)) et (j + step) hi step tmp lo fm0 Hs Hlo Hhi).
        replace (j + step - step) with j in IH by lia.
        apply IH; [lia | lia | |].
        * eapply fm_perm_ext. { apply (fm_perm_fswap _ nb (j - step) j PM NB); lia. }
          intros x Hx. apply hole_step; lia.
        * eapply frame_out_trans; [exact FR|]. intros x Hx. rewrite hole_step by lia. apply (frame_out_fswap _ (j - step) j lo hi); lia.
      + cbn [fst snd]. split; [lia|]. split; [exact PM | exact FR].
  Qed.

  Lemma fss_iter_perm_frame : forall fm i hi step lo,
    0 < step -> 0 <= lo -> hi < nb -> lo <= i <= hi -> fm_perm fm nb ->
    fm_perm (fss_iter fm ec i hi step) nb /\ frame_out fm (fss_iter fm ec i hi step) lo hi.
  Proof.
    intros fm i hi step lo Hs Hlo Hhi Hi PM. unfold fss_iter.
    assert (Ri : 0 <= rd32 fm i < nb) by (apply (proj1 PM); lia).
    pose proof (fss_in_hole (S (Z.to_nat (hi - i))) fm (rd32 ec (rd32 fm i)) (i + step) hi step (rd32 fm i) lo fm Hs Hlo Hhi) as H.
    replace (i + step - step) with i in H by lia.
    assert (ID : forall x, rd32 (wr32 fm i (rd32 fm i)) x = rd32 fm x).
    { intros x. destruct (Z.eq_dec x i) as [->|N]; [apply rd32_wr32_same; lia | apply rd32_wr32_other; lia]. }
    cps_destruct H as (A & B & C); [lia | lia | | |].
    - eapply fm_perm_ext; [exact PM|]. intros x Hx. apply ID.
    - intros x Hx. apply ID.
    - destruct (fss_in _ fm ec _ (i + step) hi step) as [fm1 j]. cbn [fst snd] in *. split; assumption.
  Qed.

  Lemma fss_outer_perm_frame : forall n fm i hi step lo,
    0 < step -> 0 <= lo -> hi < nb -> i <= hi -> lo <= i - Z.of_nat n + 1 -> fm_perm fm nb ->
    fm_perm (fss_outer n fm ec i hi step) nb /\ frame_out fm (fss_outer n fm ec i hi step) lo hi.
  Proof.
    induction n as [|n IH]; intros fm i hi step lo Hs Hlo Hhi Hi Hn PM.
    - cbn [fss_outer]. split; [exact PM | apply frame_out_refl].
    - rewrite fss_outer_S.
      destruct (fss_iter_perm_frame fm i hi step lo Hs Hlo Hhi ltac:(lia) PM) as [P1 F1].
      destruct (IH (fss_iter fm ec i hi step) (i - 1) hi step lo Hs Hlo Hhi ltac:(lia) ltac:(lia) P1) as [P2 F2].
      split; [exact P2 | eapply frame_out_trans; eassumption].
  Qed.

  Lemma fss_perm_frame : forall fm lo hi,
    0 <= lo -> hi < nb -> fm_perm fm nb ->
    fm_perm (fallbackSimpleSort fm ec lo hi) nb /\ frame_out fm (fallbackSimpleSort fm ec lo hi) lo hi.
  Proof.
    intros fm lo hi Hlo Hhi PM. unfold fallbackSimpleSort.
    destruct (Z.eqb_spec lo hi) as [E|NE]; [split; [exact PM|apply frame_out_refl]|].
    destruct (Z.le_gt_cases lo hi) as [LE|GT].
    - assert (M : fm_perm (if 3 <? hi - lo then fss_outer (Z.to_nat (hi - 4 - lo + 1)) fm ec (hi - 4) hi 4 else fm) nb /\
                  frame_out fm (if 3 <? hi - lo then fss_outer (Z.to_nat (hi - 4 - lo + 1)) fm ec (hi - 4) hi 4 else fm) lo hi).
      { destruct (Z.ltb_spec 3 (hi - lo)); [apply fss_outer_perm_frame; lia || assumption | split; [exact PM|apply frame_out_refl]]. }
      destruct M as [P1 F1].
      destruct (fss_outer_perm_frame (Z.to_nat (hi - 1 - lo + 1)) _ (hi - 1) hi 1 lo ltac:(lia) Hlo Hhi ltac:(lia) ltac:(lia) P1) as [P2 F2].
      split; [exact P2 | eapply frame_out_trans; eassumption].
    - (* [comment removed for export] *)
      replace (Z.to_nat (hi - 1 - lo + 1)) with 0%nat by lia.
      destruct (Z.ltb_spec 3 (hi - lo)); [lia|]. cbn [fss_outer]. split; [exact PM|apply frame_out_refl].
  Qed.
End FSS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section QS.
  Variables (ec : zarr) (nb : Z).
  Hypothesis NB : nb <= 4294967296.

  (* [comment removed for export] *)
  Definition PB (lo hi : Z) (p : fpart) : Prop :=
    lo <= fp_ltLo p /\ fp_ltLo p <= fp_unLo p /\ fp_unHi p <= fp_gtHi p /\ fp_gtHi p <= hi.

  Definition PF (fm0 : zarr) (lo hi : Z) (p : fpart) : Prop :=
    PB lo hi p /\ fm_perm (fp_fm p) nb /\ frame_out fm0 (fp_fm p) lo hi.

  Lemma pf_lo : forall f fm0 lo hi med p, 0 <= lo -> hi < nb -> PF fm0 lo hi p ->
    PF fm0 lo hi (fpart_lo f ec med p) /\ fp_unHi (fpart_lo f ec med p) = fp_unHi p /\ fp_gtHi (fpart_lo f ec med p) = fp_gtHi p.
  Proof.
    induction f as [|f IH]; intros fm0 lo hi med p Hlo Hhi HP.
    - cbn [fpart_lo]. split; [exact HP|split; reflexivity].
    - rewrite fpart_lo_S. cbn zeta. destruct (Z.ltb_spec (fp_unHi p) (fp_unLo p)) as [LT|GE]; [split; [exact HP|split; reflexivity]|].
      cps_destruct HP as ((A & B & D & E) & PM & FR).
      destruct (Z.eqb_spec (rd32 ec (rd32 (fp_fm p) (fp_unLo p)) - med) 0) as [EQ|NE].
      + match goal with |- PF _ _ _ (fpart_lo f ec med ?q) /\ _ => destruct (IH fm0 lo hi med q Hlo Hhi) as (P1 & P2 & P3) end.
        { split; [unfold PB; cbn; lia|]. cbn [fp_fm]. split.
          - apply fm_perm_fswap; try assumption; lia.
          - eapply frame_out_trans; [exact FR|]. apply frame_out_fswap; lia. }
        cbn [fp_unHi fp_gtHi] in P2, P3. split; [exact P1|split; assumption].
      + destruct (Z.ltb_spec 0 (rd32 ec (rd32 (fp_fm p) (fp_unLo p)) - med)) as [GT|LE].
        * split; [|split; reflexivity]. split; [unfold PB; lia|]. split; assumption.
        * match goal with |- PF _ _ _ (fpart_lo f ec med ?q) /\ _ => destruct (IH fm0 lo hi med q Hlo Hhi) as (P1 & P2 & P3) end.
          { split; [unfold PB; cbn; lia|]. cbn [fp_fm]. split; assumption. }
          cbn [fp_unHi fp_gtHi] in P2, P3. split; [exact P1|split; assumption].
  Qed.

  Lemma pf_hi : forall f fm0 lo hi med p, 0 <= lo -> hi < nb -> PF fm0 lo hi p ->
    PF fm0 lo hi (fpart_hi f ec med p) /\ fp_unLo (fpart_hi f ec med p) = fp_unLo p /\ fp_ltLo (fpart_hi f ec med p) = fp_ltLo p.
  Proof.
    induction f as [|f IH]; intros fm0 lo hi med p Hlo Hhi HP.
    - cbn [fpart_hi]. split; [exact HP|split; reflexivity].
    - rewrite fpart_hi_S. cbn zeta. destruct (Z.ltb_spec (fp_unHi p) (fp_unLo p)) as [LT|GE]; [split; [exact HP|split; reflexivity]|].
      cps_destruct HP as ((A & B & D & E) & PM & FR).
      destruct (Z.eqb_spec (rd32 ec (rd32 (fp_fm p) (fp_unHi p)) - med) 0) as [EQ|NE].
      + match goal with |- PF _ _ _ (fpart_hi f ec med ?q) /\ _ => destruct (IH fm0 lo hi med q Hlo Hhi) as (P1 & P2 & P3) end.
        { split; [unfold PB; cbn; lia|]. cbn [fp_fm]. split.
          - apply fm_perm_fswap; try assumption; lia.
          - eapply frame_out_trans; [exact FR|]. apply frame_out_fswap; lia. }
        cbn [fp_unLo fp_ltLo] in P2, P3. split; [exact P1|split; assumption].
      + destruct (Z.ltb_spec (rd32 ec (rd32 (fp_fm p) (fp_unHi p)) - med) 0) as [LTm|GEm].
        * split; [|split; reflexivity]. split; [unfold PB; lia|]. split; assumption.
        * match goal with |- PF _ _ _ (fpart_hi f ec med ?q) /\ _ => destruct (IH fm0 lo hi med q Hlo Hhi) as (P1 & P2 & P3) end.
          { split; [unfold PB; cbn; lia|]. cbn [fp_fm]. split; assumption. }
          cbn [fp_unLo fp_ltLo] in P2, P3. split; [exact P1|split; assumption].
  Qed.

  Lemma pf_loop : forall f sz fm0 lo hi med p, 0 <= lo -> hi < nb -> PF fm0 lo hi p -> PF fm0 lo hi (fpart_loop f sz ec med p).
  Proof.
    induction f as [|f IH]; intros sz fm0 lo hi med p Hlo Hhi HP.
    - cbn [fpart_loop]. exact HP.
    - rewrite fpart_loop_S. cbn zeta.
      cps_destruct (pf_lo (S sz) fm0 lo hi med p Hlo Hhi HP) as (P1 & _ & _).
      cps_destruct (pf_hi (S sz) fm0 lo hi med _ Hlo Hhi P1) as (P2 & _ & _).
      set (p2 := fpart_hi (S sz) ec med (fpart_lo (S sz) ec med p)) in *. clearbody p2.
      destruct (Z.ltb_spec (fp_unHi p2) (fp_unLo p2)) as [LT|GE]; [exact P2|].
      apply IH; [exact Hlo | exact Hhi |].
      cps_destruct P2 as ((A & B & D & E) & PM & FR).
      split; [unfold PB; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]; lia|]. cbn [fp_fm]. split.
      + apply fm_perm_fswap; try assumption; lia.
      + eapply frame_out_trans; [exact FR|]. apply frame_out_fswap; lia.
  Qed.

  (* [comment removed for export] *)
  Definition RINV (l r : Z) (q : fqs) : Prop := forall i, 0 <= i < fq_sp q -> l <= elo q i /\ ehi q i <= r.

  Lemma qs_iter_pf : forall W l r q, 0 <= l -> r < nb ->
    SINV nb W q -> RINV l r q -> 0 < fq_sp q -> fm_perm (fq_fm q) nb ->
    RINV l r (fqs_iter ec q) /\ fm_perm (fq_fm (fqs_iter ec q)) nb /\ frame_out (fq_fm q) (fq_fm (fqs_iter ec q)) l r.
  Proof.
    intros W l r q Hl Hr SI RI Hsp PM.
    cps_pose SI as (S0 & S1 & S2 & S3 & S4).
    cps_destruct (S1 (fq_sp q - 1) ltac:(lia)) as (E1 & E2 & E3). destruct (RI (fq_sp q - 1) ltac:(lia)) as [R1 R2].
    unfold elo, ehi in E1, E2, E3, R1, R2.
    unfold fqs_iter.
    set (lo := zget (fq_slo q) (fq_sp q - 1)) in *. set (hi := zget (fq_shi q) (fq_sp q - 1)) in *.
    destruct (Z.ltb_spec (hi - lo) 10) as [SM|BIG].
    { cbn [fq_fm fq_sp fq_slo fq_shi]. destruct (fss_perm_frame ec nb NB (fq_fm q) lo hi ltac:(lia) ltac:(lia) PM) as [P F].
      split; [|split; [exact P | eapply frame_out_widen; [exact F|lia|lia]]].
      intros i Hi. unfold elo, ehi; cbn [fq_slo fq_shi fq_sp] in *. apply RI. lia. }
    set (r3 := ((fq_r q * 7621 + 1) mod 32768) mod 3).
    set (med := if r3 =? 0 then _ else _).
    assert (HX : exists x, lo <= x <= hi /\ med = key ec (fq_fm q) x).
    { subst med. destruct (r3 =? 0). { exists lo. split; [lia|reflexivity]. }
      destruct (r3 =? 1). 2:{ exists hi. split; [lia|reflexivity]. }
      exists (Z.shiftr (lo + hi) 1). split; [|reflexivity].
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
      split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
    cps_destruct HX as (x & Hx & Hmed).
    pose proof (qs_part ec med lo hi (fq_fm q) x Hx Hmed) as PP. cbn zeta in PP.
    pose proof (pf_loop (S (Z.to_nat (hi - lo + 1))) (Z.to_nat (hi - lo + 1)) (fq_fm q) lo hi med (FP (fq_fm q) lo hi lo hi) ltac:(lia) ltac:(lia)) as PFL.
    set (p := fpart_loop _ _ ec med _) in *.
    cps_destruct PFL as (_ & PMp & FRp). { split; [unfold PB; cbn; lia|]. cbn [fp_fm]. split; [exact PM | apply frame_out_refl]. }
    cps_destruct PP as (A & B & C & D & E & F).
    destruct (Z.ltb_spec (fp_gtHi p) (fp_ltLo p)) as [NOP|PUSH].
    { cbn [fq_fm fq_sp fq_slo fq_shi]. split; [|split; [exact PMp | eapply frame_out_widen; [exact FRp|lia|lia]]].
      intros i Hi. unfold elo, ehi; cbn [fq_slo fq_shi fq_sp] in *. apply RI. lia. }
    (* [comment removed for export] *)
    set (n1 := fmin (fp_ltLo p - lo) (fp_unLo p - fp_ltLo p)).
    assert (Hn1 : 0 <= n1 /\ n1 <= fp_ltLo p - lo /\ n1 <= fp_unLo p - fp_ltLo p) by (subst n1; unfold fmin; destruct (_ <? _) eqn:X; [apply Z.ltb_lt in X|apply Z.ltb_ge in X]; lia).
    destruct (fvswap_perm_frame (S (Z.to_nat n1)) (fp_fm p) nb lo (fp_unLo p - n1) n1 lo hi PMp NB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [PM1 FR1].
    set (fm1 := fvswap (S (Z.to_nat n1)) (fp_fm p) lo (fp_unLo p - n1) n1) in *.
    set (m1 := fmin (hi - fp_gtHi p) (fp_gtHi p - fp_unHi p)).
    assert (Hm1 : 0 <= m1 /\ m1 <= hi - fp_gtHi p /\ m1 <= fp_gtHi p - fp_unHi p) by (subst m1; unfold fmin; destruct (_ <? _) eqn:X; [apply Z.ltb_lt in X|apply Z.ltb_ge in X]; lia).
    destruct (fvswap_perm_frame (S (Z.to_nat m1)) fm1 nb (fp_unLo p) (hi - m1 + 1) m1 lo hi PM1 NB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [PM2 FR2].
    set (fm2 := fvswap (S (Z.to_nat m1)) fm1 (fp_unLo p) (hi - m1 + 1) m1) in *.
    assert (FRall : frame_out (fq_fm q) fm2 l r).
    { eapply frame_out_widen; [|exact R1|exact R2]. eapply frame_out_trans; [exact FRp|]. eapply frame_out_trans; [exact FR1|exact FR2]. }
    assert (GEN : forall l1 h1 l2 h2, lo <= l1 -> h1 <= hi -> lo <= l2 -> h2 <= hi ->
      let q' := fpush (fpush {| fq_fm := fm2; fq_sp := fq_sp q - 1; fq_slo := fq_slo q; fq_shi := fq_shi q; fq_r := (fq_r q * 7621 + 1) mod 32768 |} l1 h1) l2 h2 in
      RINV l r q' /\ fm_perm (fq_fm q') nb /\ frame_out (fq_fm q) (fq_fm q') l r).
    { intros l1 h1 l2 h2 G1 G2 G3 G4. cbn zeta. cbn [fq_fm fpush]. split; [|split; [exact PM2 | exact FRall]].
      intros i Hi. unfold elo, ehi; cbn [fpush fq_sp fq_slo fq_shi] in *.
      destruct (Z.lt_ge_cases i (fq_sp q - 1)) as [L|G].
      - rewrite !zz0 by lia. apply RI. lia.
      - destruct (Z.eq_dec i (fq_sp q - 1)) as [->|N1]; [rewrite !zz1; lia|].
        replace i with (fq_sp q - 1 + 1) by lia. rewrite !zz2. lia. }
    destruct (Z.ltb_spec (hi - (hi - (fp_gtHi p - fp_unHi p) + 1)) (lo + fp_unLo p - fp_ltLo p - 1 - lo)) as [L|G]; apply GEN; lia.
  Qed.

  Lemma qs_loop_pf : forall W l r v q, 0 <= l -> r < nb ->
    SINV nb W q -> RINV l r q -> fm_perm (fq_fm q) nb ->
    RINV l r (fqs_loop v ec q) /\ fm_perm (fq_fm (fqs_loop v ec q)) nb /\ frame_out (fq_fm q) (fq_fm (fqs_loop v ec q)) l r.
  Proof.
    intros W l r v. induction v as [|v IH]; intros q Hl Hr SI RI PM.
    - cbn [fqs_loop]. split; [exact RI|split; [exact PM|apply frame_out_refl]].
    - rewrite fqs_loop_S. destruct (Z.ltb_spec 0 (fq_sp q)) as [P|NP]; [|split; [exact RI|split; [exact PM|apply frame_out_refl]]].
      cps_destruct (qs_iter_pf W l r q Hl Hr SI RI P PM) as (R1 & P1 & F1).
      cps_destruct (IH (fqs_iter ec q) Hl Hr (proj1 (qs_iter_ok ec nb W q SI P)) R1 P1) as (R2 & P2 & F2).
      split; [exact R2|split; [exact P2|eapply frame_out_trans; eassumption]].
  Qed.
End QS.

(* [comment removed for export] *)
Theorem fqs_perm_frame : forall ec nb fm slo shi l r v,
  fm_perm fm nb -> 0 <= l -> l <= r + 1 -> r < nb -> nb <= 4294967296 ->
  let q := fqs_loop v ec {| fq_fm := fm; fq_sp := 1; fq_slo := zset slo 0 l; fq_shi := zset shi 0 r; fq_r := 0 |} in
  fm_perm (fq_fm q) nb /\ frame_out fm (fq_fm q) l r.
Proof.
  intros ec nb fm slo shi l r v PM Hl Hlr Hr NB. cbn zeta.
  set (q0 := {| fq_fm := fm; fq_sp := 1; fq_slo := zset slo 0 l; fq_shi := zset shi 0 r; fq_r := 0 |}).
  assert (SI : SINV nb (r - l + 2) q0).
  { unfold SINV, ew, elo, ehi; cbn [fq_sp fq_slo fq_shi q0]. split; [lia|]. split.
    { intros i Hi. replace i with 0 by lia. rewrite !zget_zset_same. lia. }
    split; [intros; lia|]. split; [intros; lia|]. intros _. rewrite !zget_zset_same. lia. }
  assert (RI : RINV l r q0).
  { intros i Hi. unfold elo, ehi; cbn [fq_sp fq_slo fq_shi q0] in *. replace i with 0 by lia. rewrite !zget_zset_same. lia. }
  cps_destruct (qs_loop_pf ec nb NB (r - l + 2) l r v q0 Hl Hr SI RI PM) as (_ & P & F). split; assumption.
Qed.

