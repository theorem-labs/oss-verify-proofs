(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCSortF BzCLemmasFs BzCFactsFs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCPermF2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCPermF BzCPermF2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2.BzCQsortF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sorted_by (ec fm : zarr) (lo hi : Z) : Prop :=
  forall i j, lo <= i -> i <= j -> j <= hi -> key ec fm i <= key ec fm j.

Lemma sorted_by_empty : forall ec fm lo hi, hi <= lo -> sorted_by ec fm lo hi.
Proof. intros ec fm lo hi H i j A B C. assert (i = j) by lia. subst. lia. Qed.

(* [comment removed for export] *)

Lemma rd32_fswap_a : forall fm a b, 0 <= rd32 fm a < 4294967296 -> 0 <= rd32 fm b < 4294967296 ->
  rd32 (fswap fm a b) a = rd32 fm b.
Proof.
  intros fm a b Ha Hb. unfold fswap. destruct (Z.eq_dec a b) as [<-|NE].
  - rewrite rd32_wr32_same; lia.
  - rewrite rd32_wr32_other by lia. rewrite rd32_wr32_same; lia.
Qed.
Lemma rd32_fswap_b : forall fm a b, 0 <= rd32 fm a < 4294967296 -> rd32 (fswap fm a b) b = rd32 fm a.
Proof. intros fm a b Ha. unfold fswap. rewrite rd32_wr32_same; lia. Qed.

(* [comment removed for export] *)
Lemma perm_frame_src : forall fm fm' nb lo hi,
  fm_perm fm nb -> fm_perm fm' nb -> frame_out fm fm' lo hi -> 0 <= lo -> hi < nb ->
  forall x, lo <= x <= hi -> exists x', lo <= x' <= hi /\ rd32 fm' x = rd32 fm x'.
Proof.
  intros fm fm' nb lo hi [P1 P2] [Q1 Q2] FR Hlo Hhi x Hx.
  cps_destruct (fm_perm_onto fm nb (conj P1 P2) (rd32 fm' x) ltac:(apply Q1; lia)) as (x' & R' & E').
  destruct (Z.lt_ge_cases x' lo) as [L|G]; [|destruct (Z.lt_ge_cases hi x') as [L2|G2]].
  - exfalso. pose proof (FR x' ltac:(lia)) as F. rewrite <- F in E'.
    pose proof (Q2 x x' ltac:(lia) ltac:(lia) ltac:(symmetry; exact E')). lia.
  - exfalso. pose proof (FR x' ltac:(lia)) as F. rewrite <- F in E'.
    pose proof (Q2 x x' ltac:(lia) ltac:(lia) ltac:(symmetry; exact E')). lia.
  - exists x'. split; [lia | symmetry; exact E'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fvswap_blocks : forall f fm nb p1 p2 n,
  fm_perm fm nb -> nb <= 4294967296 -> (Z.to_nat n < f)%nat -> 0 <= n ->
  0 <= p1 -> p1 + n <= p2 -> p2 + n <= nb ->
  (forall k, 0 <= k < n -> rd32 (fvswap f fm p1 p2 n) (p1 + k) = rd32 fm (p2 + k) /\
                           rd32 (fvswap f fm p1 p2 n) (p2 + k) = rd32 fm (p1 + k)) /\
  (forall x, ~ (p1 <= x < p1 + n) -> ~ (p2 <= x < p2 + n) -> rd32 (fvswap f fm p1 p2 n) x = rd32 fm x).
Proof.
  induction f as [|f IH]; intros fm nb p1 p2 n PM NB Hf Hn H1 H2 H3; [lia|].
  rewrite fvswap_S. destruct (Z.ltb_spec 0 n) as [POS|Z0].
  2:{ split; [intros; lia | intros; reflexivity]. }
  assert (PM' : fm_perm (fswap fm p1 p2) nb) by (apply fm_perm_fswap; try assumption; lia).
  destruct (IH (fswap fm p1 p2) nb (p1 + 1) (p2 + 1) (n - 1) PM' NB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [A B].
  assert (R1 : 0 <= rd32 fm p1 < 4294967296) by (pose proof (proj1 PM p1 ltac:(lia)); lia).
  assert (R2 : 0 <= rd32 fm p2 < 4294967296) by (pose proof (proj1 PM p2 ltac:(lia)); lia).
  split.
  - intros k Hk. destruct (Z.eq_dec k 0) as [->|NZ].
    + rewrite !Z.add_0_r. rewrite !B by lia. split; [apply rd32_fswap_a; assumption | apply rd32_fswap_b; assumption].
    + destruct (A (k - 1) ltac:(lia)) as [A1 A2].
      replace (p1 + 1 + (k - 1)) with (p1 + k) in A1, A2 by lia. replace (p2 + 1 + (k - 1)) with (p2 + k) in A1, A2 by lia.
      rewrite A1, A2. rewrite !rd32_fswap_other by lia. split; reflexivity.
  - intros x X1 X2. rewrite B by lia. apply rd32_fswap_other; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FSS1.
  Variables (ec : zarr) (nb : Z).
  Hypothesis NB : nb <= 4294967296.

  (* [comment removed for export] *)
  Lemma fss_in1_spec : forall fuel fm et j hi,
    (Z.to_nat (hi + 1 - j) < fuel)%nat -> 1 <= j -> j <= hi + 1 -> hi < nb -> fm_range fm nb ->
    let r := fss_in fuel fm ec et j hi 1 in
    j <= snd r <= hi + 1 /\
    (forall x, j <= x < snd r -> key ec fm x < et) /\
    (snd r <= hi -> et <= key ec fm (snd r)) /\
    (forall x, j - 1 <= x < snd r - 1 -> rd32 (fst r) x = rd32 fm (x + 1)) /\
    (forall x, x < j - 1 \/ snd r - 1 <= x -> rd32 (fst r) x = rd32 fm x) /\
    fm_range (fst r) nb.
  Proof.
    induction fuel as [|fuel IH]; intros fm et j hi Hf Hj Hjh Hhi FR; [lia|]. cbn zeta.
    rewrite fss_in_S. destruct (Z.leb_spec j hi) as [LE|GT]; cbn [andb].
    2:{ cbn [fst snd]. split; [lia|]. split; [intros; lia|]. split; [intros; lia|]. split; [intros; lia|]. split; [intros; reflexivity|exact FR]. }
    destruct (Z.ltb_spec (rd32 ec (rd32 fm j)) et) as [LT|GE].
    2:{ cbn [fst snd]. split; [lia|]. split; [intros; lia|]. split; [intros; unfold key; lia|]. split; [intros; lia|]. split; [intros; reflexivity|exact FR]. }
    set (fm1 := wr32 fm (j - 1) (rd32 fm j)).
    assert (V : 0 <= rd32 fm j < nb) by (apply (proj2 FR); lia).
    assert (E1 : forall x, x <> j - 1 -> rd32 fm1 x = rd32 fm x) by (intros x Hx; subst fm1; apply rd32_wr32_other; lia).
    assert (E0 : rd32 fm1 (j - 1) = rd32 fm j) by (subst fm1; apply rd32_wr32_same; lia).
    assert (FR1 : fm_range fm1 nb) by (subst fm1; apply fm_range_wr32; [exact FR|exact V]).
    specialize (IH fm1 et (j + 1) hi ltac:(lia) ltac:(lia) ltac:(lia) Hhi FR1). cbn zeta in IH.
    cps_destruct IH as (A & B & C & D & E & F).
    set (r := fss_in fuel fm1 ec et (j + 1) hi 1) in *.
    split; [lia|]. split.
    { intros x Hx. destruct (Z.eq_dec x j) as [->|NE]; [unfold key; exact LT|].
      specialize (B x ltac:(lia)). unfold key in B |- *. rewrite E1 in B by lia. exact B. }
    split.
    { intros Hs. specialize (C Hs). unfold key in C |- *. rewrite E1 in C by lia. exact C. }
    split.
    { intros x Hx. destruct (Z.eq_dec x (j - 1)) as [->|NE].
      - rewrite E by lia. replace (j - 1 + 1) with j by lia. exact E0.
      - rewrite D by lia. apply E1. lia. }
    split; [|exact F].
    intros x Hx. rewrite E by lia. apply E1. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fss_iter1_sorted : forall fm i hi,
    0 <= i -> i < hi -> hi < nb -> fm_range fm nb -> sorted_by ec fm (i + 1) hi ->
    sorted_by ec (fss_iter fm ec i hi 1) i hi /\ fm_range (fss_iter fm ec i hi 1) nb.
  Proof.
    intros fm i hi Hi Hih Hhi FR SO. unfold fss_iter.
    set (tmp := rd32 fm i). set (et := rd32 ec tmp).
    pose proof (fss_in1_spec (S (Z.to_nat (hi - i))) fm et (i + 1) hi ltac:(lia) ltac:(lia) ltac:(lia) Hhi FR) as SP.
    cbn zeta in SP. destruct (fss_in _ fm ec et (i + 1) hi 1) as [fm1 J]. cbn [fst snd] in SP.
    cps_destruct SP as (A & B & C & D & E & F).
    replace (i + 1 - 1) with i in D, E by lia.
    assert (Vt : 0 <= tmp < nb) by (subst tmp; apply (proj2 FR); lia).
    set (r := wr32 fm1 (J - 1) tmp).
    assert (RJ : rd32 r (J - 1) = tmp) by (subst r; apply rd32_wr32_same; lia).
    assert (RO : forall x, x <> J - 1 -> rd32 r x = rd32 fm1 x) by (intros x Hx; subst r; apply rd32_wr32_other; lia).
    assert (RA : forall x, i <= x < J - 1 -> rd32 r x = rd32 fm (x + 1)) by (intros x Hx; rewrite RO by lia; apply D; lia).
    assert (RC : forall x, J <= x -> rd32 r x = rd32 fm x) by (intros x Hx; rewrite RO by lia; apply E; lia).
    (* [comment removed for export] *)
    assert (KA : forall x, i <= x < J - 1 -> key ec r x < et) by (intros x Hx; unfold key; rewrite RA by lia; apply B; lia).
    assert (KC : forall x, J <= x <= hi -> et <= key ec r x).
    { intros x Hx. unfold key. rewrite RC by lia. specialize (C ltac:(lia)).
      eapply Z.le_trans; [exact C|]. apply SO; lia. }
    split.
    - intros x y X1 X2 X3.
      destruct (Z.lt_ge_cases x (J - 1)) as [XA|XBC]; destruct (Z.lt_ge_cases y (J - 1)) as [YA|YBC].
      + unfold key. rewrite !RA by lia. apply SO; lia.
      + destruct (Z.eq_dec y (J - 1)) as [->|YC].
        * unfold key at 2. rewrite RJ. fold et. pose proof (KA x ltac:(lia)). lia.
        * unfold key. rewrite RA by lia. rewrite (RC y) by lia. apply SO; lia.
      + lia.
      + destruct (Z.eq_dec x (J - 1)) as [->|XC].
        * destruct (Z.eq_dec y (J - 1)) as [->|YC]; [lia|].
          unfold key at 1. rewrite RJ. fold et. apply KC. lia.
        * unfold key. rewrite !RC by lia. apply SO; lia.
    - subst r. apply fm_range_wr32; [exact F|exact Vt].
  Qed.

  (* [comment removed for export] *)
  Lemma fss_outer1_sorted : forall n fm i hi,
    i < hi -> hi < nb -> 0 <= i - Z.of_nat n + 1 -> fm_range fm nb -> sorted_by ec fm (i + 1) hi ->
    sorted_by ec (fss_outer n fm ec i hi 1) (i - Z.of_nat n + 1) hi /\ fm_range (fss_outer n fm ec i hi 1) nb.
  Proof.
    induction n as [|n IH]; intros fm i hi Hih Hhi Hn FR SO.
    - cbn [fss_outer]. replace (i - Z.of_nat 0 + 1) with (i + 1) by lia. split; assumption.
    - rewrite fss_outer_S. destruct (fss_iter1_sorted fm i hi ltac:(lia) Hih Hhi FR SO) as [S1 F1].
      destruct (IH (fss_iter fm ec i hi 1) (i - 1) hi ltac:(lia) Hhi ltac:(lia) F1) as [S2 F2].
      { replace (i - 1 + 1) with i by lia. exact S1. }
      replace (i - Z.of_nat (S n) + 1) with (i - 1 - Z.of_nat n + 1) by lia. split; assumption.
  Qed.

  Lemma fm_perm_range : forall fm, fm_perm fm nb -> fm_range fm nb.
  Proof. intros fm [P _]. split; [exact NB | exact P]. Qed.

  Theorem fss_sorted : forall fm lo hi,
    0 <= lo -> hi < nb -> fm_perm fm nb -> sorted_by ec (fallbackSimpleSort fm ec lo hi) lo hi.
  Proof.
    intros fm lo hi Hlo Hhi PM. unfold fallbackSimpleSort.
    destruct (Z.eqb_spec lo hi) as [E|NE]. { subst. intros i j A B C. assert (i = j) by lia. subst. lia. }
    destruct (Z.le_gt_cases lo hi) as [LE|GT].
    2:{ replace (Z.to_nat (hi - 1 - lo + 1)) with 0%nat by lia. cbn [fss_outer]. apply sorted_by_empty. lia. }
    set (fm1 := if 3 <? hi - lo then _ else _).
    assert (P1 : fm_perm fm1 nb).
    { subst fm1. destruct (Z.ltb_spec 3 (hi - lo)); [|exact PM].
      refine (proj1 (fss_outer_perm_frame ec nb NB _ fm (hi - 4) hi 4 lo _ Hlo Hhi _ _ PM)); lia. }
    destruct (fss_outer1_sorted (Z.to_nat (hi - 1 - lo + 1)) fm1 (hi - 1) hi ltac:(lia) Hhi ltac:(lia) (fm_perm_range fm1 P1)) as [S _].
    { apply sorted_by_empty. lia. }
    replace (hi - 1 - Z.of_nat (Z.to_nat (hi - 1 - lo + 1)) + 1) with lo in S by lia. exact S.
  Qed.
End FSS1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section QK.
  Variables (ec : zarr) (nb med lo hi : Z).
  Hypothesis NB : nb <= 4294967296.
  Hypothesis Hlo : 0 <= lo.
  Hypothesis Hhi : hi < nb.

  Definition PK (p : fpart) : Prop :=
    lo <= fp_ltLo p /\ fp_ltLo p <= fp_unLo p /\ fp_unLo p <= fp_unHi p + 1 /\ fp_unHi p <= fp_gtHi p /\ fp_gtHi p <= hi /\
    fm_perm (fp_fm p) nb /\
    (forall x, lo <= x < fp_ltLo p -> key ec (fp_fm p) x = med) /\
    (forall x, fp_ltLo p <= x < fp_unLo p -> key ec (fp_fm p) x < med) /\
    (forall x, fp_unHi p < x <= fp_gtHi p -> med < key ec (fp_fm p) x) /\
    (forall x, fp_gtHi p < x <= hi -> key ec (fp_fm p) x = med).

  Lemma key_fswap_a : forall fm a b, fm_perm fm nb -> 0 <= a < nb -> 0 <= b < nb -> key ec (fswap fm a b) a = key ec fm b.
  Proof. intros fm a b PM Ha Hb. unfold key. rewrite rd32_fswap_a; [reflexivity| |]; [pose proof (proj1 PM a Ha) | pose proof (proj1 PM b Hb)]; lia. Qed.
  Lemma key_fswap_b : forall fm a b, fm_perm fm nb -> 0 <= a < nb -> key ec (fswap fm a b) b = key ec fm a.
  Proof. intros fm a b PM Ha. unfold key. rewrite rd32_fswap_b; [reflexivity|]. pose proof (proj1 PM a Ha). lia. Qed.
  Lemma key_fswap_o : forall fm a b x, x <> a -> x <> b -> key ec (fswap fm a b) x = key ec fm x.
  Proof. intros. unfold key. rewrite rd32_fswap_other by assumption. reflexivity. Qed.

  Lemma pk_lo : forall f p,
    PK p -> (Z.to_nat (fp_unHi p - fp_unLo p + 1) < f)%nat ->
    let p' := fpart_lo f ec med p in
    PK p' /\ fp_unHi p' = fp_unHi p /\ fp_gtHi p' = fp_gtHi p /\ fp_unLo p <= fp_unLo p' /\
    (fp_unHi p' < fp_unLo p' \/ med < key ec (fp_fm p') (fp_unLo p')).
  Proof.
    induction f as [|f IH]; intros p HP Hf; [lia|]. cbn zeta.
    rewrite fpart_lo_S. cbn zeta.
    destruct (Z.ltb_spec (fp_unHi p) (fp_unLo p)) as [LT|GE].
    { split; [exact HP|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. left; exact LT. }
    cps_destruct HP as (A & B & C & D & E & PM & K1 & K2 & K3 & K4).
    destruct (Z.eqb_spec (rd32 ec (rd32 (fp_fm p) (fp_unLo p)) - med) 0) as [EQ|NE].
    - match goal with |- PK (fpart_lo f ec med ?q) /\ _ => specialize (IH q) end.
      cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in IH.
      cps_destruct IH as (P1 & P2 & P3 & P5 & P4); [| lia |].
      { unfold PK; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [apply fm_perm_fswap; try assumption; lia|].
        split. { intros x Hx. destruct (Z.eq_dec x (fp_ltLo p)) as [->|NX].
                 - rewrite key_fswap_b by (try assumption; lia). unfold key; lia.
                 - rewrite key_fswap_o by lia. apply K1. lia. }
        split. { intros x Hx. destruct (Z.eq_dec x (fp_unLo p)) as [->|NX].
                 - (* [comment removed for export] *)
                   destruct (Z.eq_dec (fp_ltLo p) (fp_unLo p)) as [E0|N0]; [lia|].
                   rewrite key_fswap_a by (try assumption; lia). apply K2. lia.
                 - rewrite key_fswap_o by lia. apply K2. lia. }
        split. { intros x Hx. rewrite key_fswap_o by lia. apply K3. lia. }
        intros x Hx. rewrite key_fswap_o by lia. apply K4. lia. }
      cbn [fp_unLo] in P5. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|exact P4].
    - destruct (Z.ltb_spec 0 (rd32 ec (rd32 (fp_fm p) (fp_unLo p)) - med)) as [GT|LE].
      + split. { unfold PK. repeat (split; [first [lia|assumption]|]). assumption. }
        split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. right. unfold key. lia.
      + match goal with |- PK (fpart_lo f ec med ?q) /\ _ => specialize (IH q) end.
        cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in IH.
        cps_destruct IH as (P1 & P2 & P3 & P5 & P4); [| lia |].
        { unfold PK; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          split; [exact PM|]. split; [exact K1|].
          split. { intros x Hx. destruct (Z.eq_dec x (fp_unLo p)) as [->|NX]; [unfold key; lia|]. apply K2. lia. }
          split; [exact K3|exact K4]. }
        cbn [fp_unLo] in P5. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|exact P4].
  Qed.

  Lemma pk_hi : forall f p,
    PK p -> (Z.to_nat (fp_unHi p - fp_unLo p + 1) < f)%nat ->
    (fp_unHi p < fp_unLo p \/ med < key ec (fp_fm p) (fp_unLo p)) ->
    let p' := fpart_hi f ec med p in
    PK p' /\ fp_unLo p' = fp_unLo p /\ fp_ltLo p' = fp_ltLo p /\ fp_unHi p' <= fp_unHi p /\
    (fp_unHi p' < fp_unLo p' \/ (key ec (fp_fm p') (fp_unHi p') < med /\ med < key ec (fp_fm p') (fp_unLo p'))).
  Proof.
    induction f as [|f IH]; intros p HP Hf HK; [lia|]. cbn zeta.
    rewrite fpart_hi_S. cbn zeta.
    destruct (Z.ltb_spec (fp_unHi p) (fp_unLo p)) as [LT|GE].
    { split; [exact HP|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. left; exact LT. }
    destruct HK as [HK|HK]; [lia|].
    cps_destruct HP as (A & B & C & D & E & PM & K1 & K2 & K3 & K4).
    destruct (Z.eqb_spec (rd32 ec (rd32 (fp_fm p) (fp_unHi p)) - med) 0) as [EQ|NE].
    - assert (NEQ : fp_unLo p <> fp_unHi p) by (intros X; unfold key in HK; rewrite X in HK; lia).
      match goal with |- PK (fpart_hi f ec med ?q) /\ _ => specialize (IH q) end.
      cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in IH.
      cps_destruct IH as (P1 & P2 & P3 & P5 & P4); [| lia | |].
      { unfold PK; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [apply fm_perm_fswap; try assumption; lia|].
        split. { intros x Hx. rewrite key_fswap_o by lia. apply K1. lia. }
        split. { intros x Hx. rewrite key_fswap_o by lia. apply K2. lia. }
        split. { intros x Hx. destruct (Z.eq_dec x (fp_unHi p)) as [->|NX].
                 - destruct (Z.eq_dec (fp_gtHi p) (fp_unHi p)) as [E0|N0]; [lia|].
                   rewrite key_fswap_a by (try assumption; lia). apply K3. lia.
                 - rewrite key_fswap_o by lia. apply K3. lia. }
        intros x Hx. destruct (Z.eq_dec x (fp_gtHi p)) as [->|NX].
        - rewrite key_fswap_b by (try assumption; lia). unfold key; lia.
        - rewrite key_fswap_o by lia. apply K4. lia. }
      { right. rewrite key_fswap_o by lia. exact HK. }
      cbn [fp_unHi] in P5. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|exact P4].
    - destruct (Z.ltb_spec (rd32 ec (rd32 (fp_fm p) (fp_unHi p)) - med) 0) as [LTm|GEm].
      + split. { unfold PK. repeat (split; [first [lia|assumption]|]). assumption. }
        split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. right. unfold key in *. lia.
      + match goal with |- PK (fpart_hi f ec med ?q) /\ _ => specialize (IH q) end.
        cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in IH.
        cps_destruct IH as (P1 & P2 & P3 & P5 & P4); [| lia | |].
        { unfold PK; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          split; [exact PM|]. split; [exact K1|]. split; [exact K2|].
          split. { intros x Hx. destruct (Z.eq_dec x (fp_unHi p)) as [->|NX]; [unfold key; lia|]. apply K3. lia. }
          exact K4. }
        { right. exact HK. }
        cbn [fp_unHi] in P5. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia|exact P4].
  Qed.

  Lemma pk_loop : forall f sz p,
    PK p -> (Z.to_nat (fp_unHi p - fp_unLo p + 1) <= sz)%nat -> (Z.to_nat (fp_unHi p - fp_unLo p + 1) < 2 * f)%nat ->
    let p' := fpart_loop f sz ec med p in
    PK p' /\ fp_unLo p' = fp_unHi p' + 1.
  Proof.
    induction f as [|f IH]; intros sz p HP Hsz Hf; [lia|]. cbn zeta.
    rewrite fpart_loop_S. cbn zeta.
    pose proof (pk_lo (S sz) p HP ltac:(lia)) as LL. cbn zeta in LL. cps_destruct LL as (L1 & L2 & L3 & L5 & L4).
    set (p1 := fpart_lo (S sz) ec med p) in *.
    assert (S1 : (Z.to_nat (fp_unHi p1 - fp_unLo p1 + 1) < S sz)%nat) by (rewrite L2; lia).
    pose proof (pk_hi (S sz) p1 L1 S1 L4) as MM. cbn zeta in MM. cps_destruct MM as (M1 & M2 & M3 & M5 & M4).
    set (p2 := fpart_hi (S sz) ec med p1) in *.
    destruct (Z.ltb_spec (fp_unHi p2) (fp_unLo p2)) as [LT|GE].
    { split; [exact M1|]. cps_destruct M1 as (_ & _ & C2 & _). lia. }
    destruct M4 as [M4|[KH KL]]; [lia|].
    assert (NE : fp_unLo p2 < fp_unHi p2).
    { destruct (Z.eq_dec (fp_unLo p2) (fp_unHi p2)) as [X|X]; [|lia]. rewrite X in KL. lia. }
    cps_destruct M1 as (A & B & C & D & E & PM & K1 & K2 & K3 & K4).
    match goal with |- PK (fpart_loop f sz ec med ?q) /\ _ => specialize (IH sz q) end.
    cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in IH.
    destruct IH as (P1 & P2); [| lia | lia | split; [exact P1|exact P2]].
    unfold PK; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [apply fm_perm_fswap; try assumption; lia|].
    split. { intros x Hx. rewrite key_fswap_o by lia. apply K1. lia. }
    split. { intros x Hx. destruct (Z.eq_dec x (fp_unLo p2)) as [->|NX].
             - rewrite key_fswap_a by (try assumption; lia). exact KH.
             - rewrite key_fswap_o by lia. apply K2. lia. }
    split. { intros x Hx. destruct (Z.eq_dec x (fp_unHi p2)) as [->|NX].
             - rewrite key_fswap_b by (try assumption; lia). exact KL.
             - rewrite key_fswap_o by lia. apply K3. lia. }
    intros x Hx. rewrite key_fswap_o by lia. apply K4. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma qk_part : forall fm,
    fm_perm fm nb -> lo <= hi + 1 ->
    let sz := Z.to_nat (hi - lo + 1) in
    let p := fpart_loop (S sz) sz ec med (FP fm lo hi lo hi) in
    PK p /\ fp_unLo p = fp_unHi p + 1.
  Proof.
    intros fm PM LH. cbn zeta. apply pk_loop; cbn [fp_unLo fp_unHi]; [|lia|lia].
    unfold PK; cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]. repeat (split; [first [lia | exact PM | intros; lia]|]). intros; lia.
  Qed.
End QK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ARR.
  Variables (ec : zarr) (nb : Z).
  Hypothesis NB : nb <= 4294967296.

  (* [comment removed for export] *)
  Definition arranged (g : zarr) (med lo hi a c : Z) : Prop :=
    (forall x, lo <= x < lo + a -> key ec g x < med) /\
    (forall x, lo + a <= x <= hi - c -> key ec g x = med) /\
    (forall x, hi - c < x <= hi -> med < key ec g x).

  Lemma qk_arrange : forall med lo hi (p : fpart),
    0 <= lo -> hi < nb -> PK ec nb med lo hi p -> fp_unLo p = fp_unHi p + 1 ->
    let n := fmin (fp_ltLo p - lo) (fp_unLo p - fp_ltLo p) in
    let fm1 := fvswap (S (Z.to_nat n)) (fp_fm p) lo (fp_unLo p - n) n in
    let m := fmin (hi - fp_gtHi p) (fp_gtHi p - fp_unHi p) in
    let fm2 := fvswap (S (Z.to_nat m)) fm1 (fp_unLo p) (hi - m + 1) m in
    fm_perm fm2 nb /\ frame_out (fp_fm p) fm2 lo hi /\
    arranged fm2 med lo hi (fp_unLo p - fp_ltLo p) (fp_gtHi p - fp_unHi p).
  Proof.
    (intros med lo hi p Hlo Hhi; cps_intros (A & B & C & D & E & PM & K1 & K2 & K3 & K4); intros UU). cbn zeta.
    set (a := fp_unLo p - fp_ltLo p). set (c := fp_gtHi p - fp_unHi p).
    set (e1 := fp_ltLo p - lo). set (e2 := hi - fp_gtHi p).
    set (n := fmin e1 a).
    assert (Hn : 0 <= n /\ n <= e1 /\ n <= a /\ (n = e1 \/ n = a)) by (subst n; unfold fmin; destruct (Z.ltb_spec e1 a); lia).
    destruct (fvswap_perm_frame (S (Z.to_nat n)) (fp_fm p) nb lo (fp_unLo p - n) n lo hi PM NB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [PM1 FR1].
    destruct (fvswap_blocks (S (Z.to_nat n)) (fp_fm p) nb lo (fp_unLo p - n) n PM NB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [X1 Y1].
    set (fm1 := fvswap (S (Z.to_nat n)) (fp_fm p) lo (fp_unLo p - n) n) in *.
    (* [comment removed for export] *)
    assert (A1 : forall x, lo <= x < lo + a -> key ec fm1 x < med).
    { intros x Hx. unfold key. destruct (Z.lt_ge_cases x (lo + n)) as [L|G].
      - destruct (X1 (x - lo) ltac:(lia)) as [X _]. replace (lo + (x - lo)) with x in X by lia. rewrite X.
        apply K2. lia.
      - (* [comment removed for export] *)
        rewrite Y1 by lia. apply K2. lia. }
    assert (B1 : forall x, lo + a <= x < fp_unLo p -> key ec fm1 x = med).
    { intros x Hx. unfold key. destruct (Z.lt_ge_cases x (fp_unLo p - n)) as [L|G].
      - rewrite Y1 by lia. apply K1. lia.
      - destruct (X1 (x - (fp_unLo p - n)) ltac:(lia)) as [_ X]. replace (fp_unLo p - n + (x - (fp_unLo p - n))) with x in X by lia.
        rewrite X. apply K1. lia. }
    assert (C1 : forall x, fp_unLo p <= x -> rd32 fm1 x = rd32 (fp_fm p) x) by (intros x Hx; apply Y1; lia).
    set (m := fmin e2 c).
    assert (Hm : 0 <= m /\ m <= e2 /\ m <= c /\ (m = e2 \/ m = c)) by (subst m; unfold fmin; destruct (Z.ltb_spec e2 c); lia).
    destruct (fvswap_perm_frame (S (Z.to_nat m)) fm1 nb (fp_unLo p) (hi - m + 1) m lo hi PM1 NB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [PM2 FR2].
    destruct (fvswap_blocks (S (Z.to_nat m)) fm1 nb (fp_unLo p) (hi - m + 1) m PM1 NB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [X2 Y2].
    set (fm2 := fvswap (S (Z.to_nat m)) fm1 (fp_unLo p) (hi - m + 1) m) in *.
    split; [exact PM2|]. split; [eapply frame_out_trans; eassumption|].
    split; [|split].
    - intros x Hx. unfold key. rewrite Y2 by lia. apply A1. lia.
    - intros x Hx. destruct (Z.lt_ge_cases x (fp_unLo p)) as [L|G].
      + unfold key. rewrite Y2 by lia. apply B1. lia.
      + (* [comment removed for export] *)
        destruct (Z.lt_ge_cases x (fp_unLo p + m)) as [L2|G2].
        * destruct (X2 (x - fp_unLo p) ltac:(lia)) as [X _]. replace (fp_unLo p + (x - fp_unLo p)) with x in X by lia.
          unfold key. rewrite X. rewrite C1 by lia. apply K4. lia.
        * unfold key. rewrite Y2 by lia. rewrite C1 by lia. cps_destruct Hm as (_ & _ & _ & [Hm'|Hm']).
          -- apply K4. lia.   (* [comment removed for export] *)
          -- apply K4. lia.
    - intros x Hx. destruct (Z.lt_ge_cases x (hi - m + 1)) as [L|G].
      + unfold key. rewrite Y2 by lia. rewrite C1 by lia. apply K3. lia.
      + destruct (X2 (x - (hi - m + 1)) ltac:(lia)) as [_ X]. replace (hi - m + 1 + (x - (hi - m + 1))) with x in X by lia.
        unfold key. rewrite X. rewrite C1 by lia. apply K3. lia.
  Qed.
End ARR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ST.
  Variables (ec : zarr) (nb W L R : Z).
  Hypothesis NB : nb <= 4294967296.
  Hypothesis HL : 0 <= L.
  Hypothesis HR : R < nb.

  Definition inframe (q : fqs) (t x : Z) : Prop := elo q t <= x <= ehi q t.

  Definition QINV (q : fqs) : Prop :=
    (forall t, 0 <= t < fq_sp q -> L <= elo q t /\ ehi q t <= R) /\
    (forall t u x, 0 <= t < fq_sp q -> 0 <= u < fq_sp q -> t <> u -> inframe q t x -> inframe q u x -> False) /\
    (forall i j, L <= i -> i < j -> j <= R ->
       (forall t, 0 <= t < fq_sp q -> ~ (inframe q t i /\ inframe q t j)) ->
       key ec (fq_fm q) i <= key ec (fq_fm q) j).

  (* [comment removed for export] *)
  Lemma qinv_step : forall q q',
    SINV nb W q -> QINV q -> 0 < fq_sp q -> fm_perm (fq_fm q) nb ->
    let sp := fq_sp q in let lo := elo q (sp - 1) in let hi := ehi q (sp - 1) in let g := fq_fm q' in
    fm_perm g nb -> frame_out (fq_fm q) g lo hi ->
    sp - 1 <= fq_sp q' ->
    (forall t, 0 <= t < sp - 1 -> elo q' t = elo q t /\ ehi q' t = ehi q t) ->
    (forall t, sp - 1 <= t < fq_sp q' -> lo <= elo q' t /\ ehi q' t <= hi) ->
    (forall t u x, sp - 1 <= t < fq_sp q' -> sp - 1 <= u < fq_sp q' -> t <> u -> inframe q' t x -> inframe q' u x -> False) ->
    (forall i j, lo <= i -> i < j -> j <= hi ->
       (forall t, sp - 1 <= t < fq_sp q' -> ~ (inframe q' t i /\ inframe q' t j)) -> key ec g i <= key ec g j) ->
    QINV q'.
  Proof.
    (intros q q' SI; cps_intros (Q1 & Q2 & Q3); intros Hsp PM). cbn zeta.
    set (sp := fq_sp q). set (lo := elo q (sp - 1)). set (hi := ehi q (sp - 1)).
    intros PMg FR Hsp' HO HN HD HLS.
    cps_destruct SI as (S0 & S1 & _). cps_destruct (S1 (sp - 1) ltac:(lia)) as (E1 & E2 & E3). fold lo hi in E1, E2, E3.
    destruct (Q1 (sp - 1) ltac:(lia)) as [R1 R2]. fold lo hi in R1, R2.
    (* [comment removed for export] *)
    assert (DIS : forall t x, 0 <= t < sp - 1 -> lo <= x <= hi -> ~ inframe q t x).
    { intros t x Ht Hx IN. apply (Q2 t (sp - 1) x); try lia; [exact IN|]. unfold inframe; fold lo hi; lia. }
    assert (INO : forall t x, 0 <= t < sp - 1 -> inframe q' t x <-> inframe q t x).
    { intros t x Ht. unfold inframe. destruct (HO t Ht) as [-> ->]. tauto. }
    split; [|split].
    - intros t Ht. destruct (Z.lt_ge_cases t (sp - 1)) as [LT|GE].
      + destruct (HO t ltac:(lia)) as [-> ->]. apply Q1. lia.
      + destruct (HN t ltac:(lia)). lia.
    - intros t u x Ht Hu NE IT IU.
      destruct (Z.lt_ge_cases t (sp - 1)) as [LT|GT]; destruct (Z.lt_ge_cases u (sp - 1)) as [LU|GU].
      + apply (Q2 t u x); try lia; [apply (INO t x)|apply (INO u x)]; try lia; assumption.
      + apply (DIS t x); [lia| |apply (INO t x); [lia|exact IT]]. destruct (HN u ltac:(lia)). unfold inframe in IU. lia.
      + apply (DIS u x); [lia| |apply (INO u x); [lia|exact IU]]. destruct (HN t ltac:(lia)). unfold inframe in IT. lia.
      + apply (HD t u x); try lia; assumption.
    - intros i j Hi Hij Hj NF.
      assert (SRC : forall x, lo <= x <= hi -> exists x', lo <= x' <= hi /\ rd32 (fq_fm q') x = rd32 (fq_fm q) x').
      { intros x Hx. apply (perm_frame_src (fq_fm q) (fq_fm q') nb lo hi); try assumption; lia. }
      assert (OLD : forall i0 j0, L <= i0 -> i0 < j0 -> j0 <= R -> ~ (lo <= i0 <= hi /\ lo <= j0 <= hi) ->
                (forall t, 0 <= t < sp - 1 -> ~ (inframe q t i0 /\ inframe q t j0)) ->
                key ec (fq_fm q) i0 <= key ec (fq_fm q) j0).
      { intros i0 j0 A0 B0 C0 NB0 NF0. apply Q3; try lia. intros t Ht.
        destruct (Z.eq_dec t (sp - 1)) as [->|NT]; [unfold inframe; fold lo hi; lia|]. apply NF0. lia. }
      destruct (Z.le_gt_cases lo i) as [LI|LI]; destruct (Z.le_gt_cases j hi) as [HJ|HJ].
      + (* [comment removed for export] *)
        apply HLS; try lia. intros t Ht. apply NF. lia.
      + (* [comment removed for export] *)
        destruct (Z.le_gt_cases i hi) as [IH2|IH2].
        * cps_destruct (SRC i ltac:(lia)) as (i' & Hi' & Ei). unfold key. rewrite Ei. rewrite (FR j) by lia.
          apply (OLD i' j); try lia. intros t Ht [X Y]. apply (DIS t i'); try lia. exact X.
        * unfold key. rewrite (FR i), (FR j) by lia. apply (OLD i j); try lia.
          intros t Ht [X Y]. apply (NF t ltac:(lia)). split; apply INO; try lia; assumption.
      + (* [comment removed for export] *)
        destruct (Z.le_gt_cases lo j) as [JL|JL].
        * cps_destruct (SRC j ltac:(lia)) as (j' & Hj' & Ej). unfold key. rewrite Ej. rewrite (FR i) by lia.
          apply (OLD i j'); try lia. intros t Ht [X Y]. apply (DIS t j'); try lia. exact Y.
        * unfold key. rewrite (FR i), (FR j) by lia. apply (OLD i j); try lia.
          intros t Ht [X Y]. apply (NF t ltac:(lia)). split; apply INO; try lia; assumption.
      + (* [comment removed for export] *)
        unfold key. rewrite (FR i), (FR j) by lia. apply (OLD i j); try lia.
        intros t Ht [X Y]. apply (NF t ltac:(lia)). split; apply INO; try lia; assumption.
  Qed.
End ST.

Section IT2.
  Variables (ec : zarr) (nb W L R : Z).
  Hypothesis NB : nb <= 4294967296.
  Hypothesis HL : 0 <= L.
  Hypothesis HR : R < nb.

  Lemma qs_iter_sorted : forall q,
    SINV nb W q -> QINV ec L R q -> 0 < fq_sp q -> fm_perm (fq_fm q) nb ->
    QINV ec L R (fqs_iter ec q) /\ fm_perm (fq_fm (fqs_iter ec q)) nb.
  Proof.
    intros q SI QI Hsp PM.
    cps_pose SI as (S0 & S1 & S2 & S3 & S4).
    cps_destruct (S1 (fq_sp q - 1) ltac:(lia)) as (E1 & E2 & E3). cps_pose QI as (Q1 & _ & _).
    destruct (Q1 (fq_sp q - 1) ltac:(lia)) as [R1 R2].
    unfold elo, ehi in E1, E2, E3, R1, R2.
    pose proof (qinv_step ec nb W L R q) as STEP. cbn zeta in STEP.
    unfold fqs_iter.
    set (lo := zget (fq_slo q) (fq_sp q - 1)) in *. set (hi := zget (fq_shi q) (fq_sp q - 1)) in *.
    destruct (Z.ltb_spec (hi - lo) 10) as [SM|BIG].
    { (* [comment removed for export] *)
      destruct (fss_perm_frame ec nb NB (fq_fm q) lo hi ltac:(lia) ltac:(lia) PM) as [P F].
      split; [|cbn [fq_fm]; exact P].
      apply (STEP _ SI QI Hsp PM); cbn [fq_fm fq_sp fq_slo fq_shi]; try first [exact P | exact F | lia].
      - intros t Ht. split; reflexivity.
      - unfold elo, ehi; fold lo; fold hi. intros i j Hi Hij Hj _. apply (fss_sorted ec nb NB (fq_fm q) lo hi); lia || assumption. }
    set (r3 := ((fq_r q * 7621 + 1) mod 32768) mod 3).
    set (med := if r3 =? 0 then _ else _).
    pose proof (qk_part ec nb med lo hi NB ltac:(lia) ltac:(lia) (fq_fm q) PM ltac:(lia)) as KP. cbn zeta in KP.
    pose proof (pf_loop ec nb NB (S (Z.to_nat (hi - lo + 1))) (Z.to_nat (hi - lo + 1)) (fq_fm q) lo hi med (FP (fq_fm q) lo hi lo hi) ltac:(lia) ltac:(lia)) as PFL.
    set (p := fpart_loop _ _ ec med _) in *.
    cps_destruct PFL as (_ & PMp & FRp). { split; [unfold PB; cbn; lia|]. cbn [fp_fm]. split; [exact PM | apply frame_out_refl]. }
    destruct KP as [KPK KU]. cps_pose KPK as (A & B & C & D & E & _ & K1 & K2 & K3 & K4).
    destruct (Z.ltb_spec (fp_gtHi p) (fp_ltLo p)) as [NOP|PUSH].
    { (* [comment removed for export] *)
      split; [|cbn [fq_fm]; exact PMp].
      apply (STEP _ SI QI Hsp PM); cbn [fq_fm fq_sp fq_slo fq_shi]; try first [exact PMp | exact FRp | lia].
      - intros t Ht. split; reflexivity.
      - unfold elo, ehi; fold lo; fold hi. intros i j Hi Hij Hj _.
        assert (ALL : forall x, lo <= x <= hi -> key ec (fp_fm p) x = med).
        { intros x Hx. destruct (Z.lt_ge_cases x (fp_ltLo p)); [apply K1; lia | apply K4; lia]. }
        rewrite !ALL by lia. lia. }
    pose proof (qk_arrange ec nb NB med lo hi p ltac:(lia) ltac:(lia) KPK KU) as AR. cbn zeta in AR.
    cps_destruct AR as (PM2 & FR2 & AR1 & AR2 & AR3).
    set (fm2 := fvswap _ (fvswap _ _ _ _ _) _ _ _) in *.
    set (a := fp_unLo p - fp_ltLo p) in *. set (c := fp_gtHi p - fp_unHi p) in *.
    assert (AC : 0 <= a /\ 0 <= c /\ a + c <= hi - lo + 1) by (subst a c; lia).
    replace (lo + fp_unLo p - fp_ltLo p - 1) with (lo + a - 1) by lia.
    replace (hi - (fp_gtHi p - fp_unHi p) + 1) with (hi - c + 1) by lia.
    assert (FRall : frame_out (fq_fm q) fm2 lo hi) by (eapply frame_out_trans; [exact FRp | exact FR2]).
    set (q2 := {| fq_fm := fm2; fq_sp := fq_sp q - 1; fq_slo := fq_slo q; fq_shi := fq_shi q; fq_r := _ |}).
    assert (GEN : forall l1 h1 l2 h2,
              ((l1 = lo /\ h1 = lo + a - 1 /\ l2 = hi - c + 1 /\ h2 = hi) \/ (l2 = lo /\ h2 = lo + a - 1 /\ l1 = hi - c + 1 /\ h1 = hi)) ->
              QINV ec L R (fpush (fpush q2 l1 h1) l2 h2) /\ fm_perm (fq_fm (fpush (fpush q2 l1 h1) l2 h2)) nb).
    2:{ destruct (Z.ltb_spec (hi - (hi - c + 1)) (lo + a - 1 - lo)); apply GEN; lia. }
    intros l1 h1 l2 h2 ORD. split; [|cbn [fq_fm fpush]; exact PM2].
    apply (STEP _ SI QI Hsp PM); cbn [fq_fm fq_sp fq_slo fq_shi fpush q2]; try first [exact PM2 | exact FRall | lia].
    - intros t Ht. unfold elo, ehi; cbn [fq_slo fq_shi fq_sp fpush q2]. rewrite !zz0 by lia. split; reflexivity.
    - intros t Ht. unfold elo, ehi; cbn [fq_slo fq_shi fq_sp fpush q2].
      destruct (Z.eq_dec t (fq_sp q - 1)) as [->|NT].
      + rewrite !zz1. lia.
      + replace t with (fq_sp q - 1 + 1) by lia. rewrite !zz2. lia.
    - intros t u x Ht Hu NE IT IU. unfold inframe, elo, ehi in IT, IU; cbn [fq_slo fq_shi fq_sp fpush q2] in IT, IU.
      destruct (Z.eq_dec t (fq_sp q - 1)) as [->|NT]; destruct (Z.eq_dec u (fq_sp q - 1)) as [->|NU]; try lia.
      + replace u with (fq_sp q - 1 + 1) in IU by lia. rewrite !zz1 in IT. rewrite !zz2 in IU. lia.
      + replace t with (fq_sp q - 1 + 1) in IT by lia. rewrite !zz2 in IT. rewrite !zz1 in IU. lia.
    - unfold elo at 1; unfold ehi at 1; fold lo; fold hi. intros i j Hi Hij Hj NF.
      (* [comment removed for export] *)
      assert (NLT : ~ (i < lo + a /\ j < lo + a)).
      { intros [X Y]. destruct ORD as [(-> & -> & -> & ->)|(-> & -> & -> & ->)].
        - apply (NF (fq_sp q - 1) ltac:(lia)). unfold inframe, elo, ehi; cbn [fq_slo fq_shi fq_sp fpush q2]. rewrite !zz1. lia.
        - apply (NF (fq_sp q - 1 + 1) ltac:(lia)). unfold inframe, elo, ehi; cbn [fq_slo fq_shi fq_sp fpush q2]. rewrite !zz2. lia. }
      assert (NGT : ~ (hi - c < i /\ hi - c < j)).
      { intros [X Y]. destruct ORD as [(-> & -> & -> & ->)|(-> & -> & -> & ->)].
        - apply (NF (fq_sp q - 1 + 1) ltac:(lia)). unfold inframe, elo, ehi; cbn [fq_slo fq_shi fq_sp fpush q2]. rewrite !zz2. lia.
        - apply (NF (fq_sp q - 1) ltac:(lia)). unfold inframe, elo, ehi; cbn [fq_slo fq_shi fq_sp fpush q2]. rewrite !zz1. lia. }
      destruct (Z.lt_ge_cases i (lo + a)) as [IA|IA].
      + (* [comment removed for export] *)
        pose proof (AR1 i ltac:(lia)).
        destruct (Z.le_gt_cases j (hi - c)) as [JB|JB]; [rewrite (AR2 j) by lia; lia | pose proof (AR3 j ltac:(lia)); lia].
      + destruct (Z.le_gt_cases i (hi - c)) as [IB|IB].
        * rewrite (AR2 i) by lia. destruct (Z.le_gt_cases j (hi - c)) as [JB|JB]; [rewrite (AR2 j) by lia; lia | pose proof (AR3 j ltac:(lia)); lia].
        * exfalso. apply NGT. lia.
  Qed.
End IT2.

Section LOOP.
  Variables (ec : zarr) (nb W L R : Z).
  Hypothesis NB : nb <= 4294967296.

  Lemma qs_loop_sorted : forall v q,
    SINV nb W q -> QINV ec L R q -> fm_perm (fq_fm q) nb ->
    QINV ec L R (fqs_loop v ec q) /\ fm_perm (fq_fm (fqs_loop v ec q)) nb.
  Proof.
    induction v as [|v IH]; intros q SI QI PM.
    - cbn [fqs_loop]. split; assumption.
    - rewrite fqs_loop_S. destruct (Z.ltb_spec 0 (fq_sp q)) as [P|NP]; [|split; assumption].
      destruct (qs_iter_sorted ec nb W L R NB q SI QI P PM) as [Q1 P1].
      apply IH; [apply (qs_iter_ok ec nb W q SI P) | exact Q1 | exact P1].
  Qed.
End LOOP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem fqs_sorted : forall ec nb fm slo shi l r v,
  fm_perm fm nb -> 0 <= l -> l <= r + 1 -> r < nb -> nb <= 4294967296 ->
  let q := fqs_loop v ec {| fq_fm := fm; fq_sp := 1; fq_slo := zset slo 0 l; fq_shi := zset shi 0 r; fq_r := 0 |} in
  fq_sp q <= 0 ->
  sorted_by ec (fq_fm q) l r /\ fm_perm (fq_fm q) nb /\ frame_out fm (fq_fm q) l r.
Proof.
  intros ec nb fm slo shi l r v PM Hl Hlr Hr NB. cbn zeta. intros SP.
  set (q0 := {| fq_fm := fm; fq_sp := 1; fq_slo := zset slo 0 l; fq_shi := zset shi 0 r; fq_r := 0 |}) in *.
  assert (SI : SINV nb (r - l + 2) q0).
  { unfold SINV, ew, elo, ehi; cbn [fq_sp fq_slo fq_shi q0]. split; [lia|]. split.
    { intros i Hi. replace i with 0 by lia. rewrite !zget_zset_same. lia. }
    split; [intros; lia|]. split; [intros; lia|]. intros _. rewrite !zget_zset_same. lia. }
  assert (QI : QINV ec l r q0).
  { split; [|split].
    - intros t Ht. unfold elo, ehi; cbn [fq_sp fq_slo fq_shi q0] in *. replace t with 0 by lia. rewrite !zget_zset_same. lia.
    - intros t u x Ht Hu NE. cbn [fq_sp q0] in Ht, Hu. lia.
    - intros i j Hi Hij Hj NF. exfalso. apply (NF 0); [cbn [fq_sp q0]; lia|].
      unfold inframe, elo, ehi; cbn [fq_slo fq_shi q0]. rewrite !zget_zset_same. lia. }
  destruct (qs_loop_sorted ec nb (r - l + 2) l r NB v q0 SI QI PM) as [(Q1 & Q2 & Q3) P].
  split; [|split; [exact P | apply (proj2 (fqs_perm_frame ec nb fm slo shi l r v PM Hl Hlr Hr NB))]].
  intros i j Hi Hij Hj. destruct (Z.eq_dec i j) as [->|NE]; [lia|]. apply Q3; lia.
Qed.

(* [comment removed for export] *)
Theorem fallbackQSort3_sorted : forall ec nb fm slo shi l r,
  fm_perm fm nb -> 0 <= l -> l <= r + 1 -> r < nb -> nb <= 4294967296 ->
  let q := fallbackQSort3 fm ec slo shi l r in
  sorted_by ec (fq_fm q) l r /\ fm_perm (fq_fm q) nb /\ frame_out fm (fq_fm q) l r.
Proof.
  intros ec nb fm slo shi l r PM Hl Hlr Hr NB. unfold fallbackQSort3, fpush. cbn [fq_fm fq_sp fq_slo fq_shi fq_r].
  replace (0 + 1) with 1 by lia.
  apply fqs_sorted; try assumption.
  set (q0 := {| fq_fm := fm; fq_sp := 1; fq_slo := zset slo 0 l; fq_shi := zset shi 0 r; fq_r := 0 |}).
  assert (SI : SINV nb (r - l + 2) q0).
  { unfold SINV, ew, elo, ehi; cbn [fq_sp fq_slo fq_shi q0]. split; [lia|]. split.
    { intros i Hi. replace i with 0 by lia. rewrite !zget_zset_same. lia. }
    split; [intros; lia|]. split; [intros; lia|]. intros _. rewrite !zget_zset_same. lia. }
  apply (qs_loop_term ec nb (r - l + 2)); [exact SI|].
  unfold phi, fqs_fuel. cbn [fq_sp q0]. change (Z.to_nat 1) with 1%nat. cbn [phi_n].
  unfold ew, elo, ehi; cbn [fq_slo fq_shi q0]. rewrite !zget_zset_same. lia.
Qed.
