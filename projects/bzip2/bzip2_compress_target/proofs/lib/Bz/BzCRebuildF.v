(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortF BzCLemmasFs BzCFactsFs BzCPermF.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Fixpoint sumF (g : Z -> Z) (j : Z) (n : nat) : Z :=
  match n with O => 0 | S n' => g j + sumF g (j + 1) n' end.

Lemma sumF_ext : forall n g h j, (forall b, j <= b < j + Z.of_nat n -> g b = h b) -> sumF g j n = sumF h j n.
Proof. induction n as [|n IH]; intros g h j H; cbn; [reflexivity|]. rewrite H by lia. rewrite (IH g h) by (intros; apply H; lia). reflexivity. Qed.

Lemma sumF_nonneg : forall n g j, (forall b, j <= b < j + Z.of_nat n -> 0 <= g b) -> 0 <= sumF g j n.
Proof. induction n as [|n IH]; intros g j H; cbn; [lia|]. assert (0 <= g j) by (apply H; lia). assert (0 <= sumF g (j+1) n) by (apply IH; intros; apply H; lia). lia. Qed.

Lemma sumF_term_le : forall n g j b, (forall b, j <= b < j + Z.of_nat n -> 0 <= g b) -> j <= b < j + Z.of_nat n -> g b <= sumF g j n.
Proof.
  induction n as [|n IH]; intros g j b H Hb; cbn; [lia|].
  destruct (Z.eq_dec b j) as [->|NE].
  - assert (0 <= sumF g (j+1) n) by (apply sumF_nonneg; intros; apply H; lia). lia.
  - assert (g b <= sumF g (j+1) n) by (apply IH; [intros; apply H|]; lia). assert (0 <= g j) by (apply H; lia). lia.
Qed.

Lemma sumF_upd : forall n g h j b d, j <= b < j + Z.of_nat n -> (forall x, h x = if x =? b then g x + d else g x) -> sumF h j n = sumF g j n + d.
Proof.
  induction n as [|n IH]; intros g h j b d Hb H; cbn; [lia|].
  destruct (Z.eq_dec b j) as [->|NE].
  - rewrite H, Z.eqb_refl. rewrite (sumF_ext n h g) by (intros x Hx; rewrite H; destruct (Z.eqb_spec x j); [lia|reflexivity]). lia.
  - rewrite H. destruct (Z.eqb_spec j b); [lia|]. rewrite (IH g h (j+1) b d) by (lia || exact H). lia.
Qed.

(* [comment removed for export] *)
Lemma sumF_pos_ex : forall n g j, (forall b, j <= b < j + Z.of_nat n -> 0 <= g b) -> 1 <= sumF g j n ->
  exists b, j <= b < j + Z.of_nat n /\ 1 <= g b.
Proof.
  induction n as [|n IH]; intros g j H S; cbn in S; [lia|].
  destruct (Z.lt_ge_cases 0 (g j)) as [P|NP].
  - exists j. split; [lia|lia].
  - cps_destruct (IH g (j+1)) as (b & Hb & Gb); [intros; apply H; lia | lia |]. exists b. split; [lia|exact Gb].
Qed.

(* [comment removed for export] *)
Lemma sumF_ind : forall n j v, j <= v < j + Z.of_nat n -> sumF (fun b => if v =? b then 1 else 0) j n = 1.
Proof.
  induction n as [|n IH]; intros j v Hv; cbn; [lia|].
  destruct (Z.eqb_spec v j) as [->|NE].
  - rewrite (sumF_ext n _ (fun _ => 0)). 2:{ intros b Hb. destruct (Z.eqb_spec j b); [lia|reflexivity]. }
    assert (Z0 : forall m k, sumF (fun _ => 0) k m = 0) by (induction m; intros; cbn; [|rewrite IHm]; lia). rewrite Z0. lia.
  - rewrite IH by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma skip0_spec : forall fuel fc j b, j <= b -> b - j < Z.of_nat fuel -> zget fc b <> 0 ->
  let j' := fs_skip0 fuel fc j in j <= j' <= b /\ zget fc j' <> 0 /\ (forall x, j <= x < j' -> zget fc x = 0).
Proof.
  induction fuel as [|fuel IH]; intros fc j b Hj Hf Hb; cbn zeta; [lia|].
  cbn [fs_skip0]. destruct (Z.eqb_spec (zget fc j) 0) as [E|NE].
  - assert (j <> b) by (intros ->; congruence).
    cps_destruct (IH fc (j+1) b ltac:(lia) ltac:(lia) Hb) as (A & B & C).
    split; [lia|]. split; [exact B|]. intros x Hx. destruct (Z.eq_dec x j) as [->|NX]; [exact E| apply C; lia].
  - split; [lia|]. split; [exact NE|]. intros; lia.
Qed.

Section S5.
  Variables (ec : zarr) (nb : Z) (fm bh : zarr).
  Hypothesis ECB : zbok ec.
  Hypothesis NB : 0 <= nb.

  (* [comment removed for export] *)
  Lemma sum_Eq : forall k, (k <= Z.to_nat nb)%nat -> sumF (fun b => Eq ec b k) 0 256 = Z.of_nat k.
  Proof.
    induction k as [|k IH]; intros Hk.
    - unfold Eq. cbn [cntP]. assert (Z0 : forall m j, sumF (fun _ => 0) j m = 0) by (induction m; intros; cbn; [|rewrite IHm]; lia). apply Z0.
    - transitivity (sumF (fun b => Eq ec b k) 0 256 + 1); [|rewrite IH by lia; lia].
      assert (R : 0 <= rd8 ec (Z.of_nat k) < 256) by (unfold rd8; apply ECB).
      rewrite <- (sumF_ind 256 0 (rd8 ec (Z.of_nat k))) by lia.
      assert (G : forall n j, sumF (fun b => Eq ec b (S k)) j n = sumF (fun b => Eq ec b k) j n + sumF (fun b => if rd8 ec (Z.of_nat k) =? b then 1 else 0) j n).
      { induction n as [|n IHn]; intros j; cbn [sumF]; [lia|]. rewrite IHn. rewrite Eq_S. lia. }
      apply G.
  Qed.

  Lemma fc0_get : forall b, zget (fp_fc0 ec nb) b = if ((0 <=? b) && (b <? 256))%bool then Eq ec b (Z.to_nat nb) else 0.
  Proof.
    intros b. unfold fp_fc0. rewrite fs_copy_get. replace (0 + Z.of_nat 256) with 256 by reflexivity.
    destruct ((0 <=? b) && (b <? 256))%bool; [apply ft2_get; assumption | apply zget_znew].
  Qed.

  Definition RB (i : nat) (s : zarr * zarr * Z) : Prop :=
    let fc := snd (fst s) in let j := snd s in
    0 <= j <= 255 /\ (forall b, 0 <= zget fc b) /\ (forall b, b < j -> zget fc b = 0) /\
    sumF (zget fc) 0 256 = nb - Z.of_nat i.

  Lemma RB0 : RB 0 (fp_rb fm ec bh nb 0).
  Proof.
    unfold RB, fp_rb. cbn [fs_rebuild fst snd]. split; [lia|]. split; [|split].
    - intros b. rewrite fc0_get. destruct (_ && _)%bool; [|lia]. pose proof (Eq_range ec nb b (Z.to_nat nb) ltac:(lia)). lia.
    - intros b Hb. rewrite fc0_get. destruct (Z.leb_spec 0 b); [lia|reflexivity].
    - rewrite (sumF_ext 256 _ (fun b => Eq ec b (Z.to_nat nb))). 2:{ intros b Hb. rewrite fc0_get. destruct (Z.leb_spec 0 b), (Z.ltb_spec b 256); cbn; try reflexivity; lia. }
      rewrite sum_Eq by lia. lia.
  Qed.

  Lemma fs_rebuild_snoc : forall n e fc j i0 fmx,
    fs_rebuild (S n) e fc fmx i0 j =
      (let s := fs_rebuild n e fc fmx i0 j in let e' := fst (fst s) in let fc' := snd (fst s) in let j0 := snd s in
       let j' := fs_skip0 258%nat fc' j0 in
       (wr8 e' (rd32 fmx (i0 + Z.of_nat n)) j', zset fc' j' (zget fc' j' - 1), j')).
  Proof.
    induction n as [|n IH]; intros e fc j i0 fmx.
    - rewrite fs_rebuild_S. cbn zeta. change (fs_rebuild 0 e fc fmx i0 j) with (e, fc, j). cbn [fst snd].
      rewrite Z.add_0_r. reflexivity.
    - rewrite fs_rebuild_S. cbn zeta. rewrite IH. cbn zeta.
      rewrite (fs_rebuild_S n e fc fmx i0 j). cbn zeta.
      replace (i0 + 1 + Z.of_nat n) with (i0 + Z.of_nat (S n)) by lia. reflexivity.
  Qed.

  Lemma fp_rb_S : forall i, fp_rb fm ec bh nb (S i) =
    (let s := fp_rb fm ec bh nb i in let e := fst (fst s) in let fc := snd (fst s) in let j := snd s in
     let j' := fs_skip0 258%nat fc j in
     (wr8 e (rd32 (fh_fm (fp_hsF fm ec bh nb)) (Z.of_nat i)) j', zset fc j' (zget fc j' - 1), j')).
  Proof.
    intros i. unfold fp_rb. rewrite fs_rebuild_snoc. cbn zeta. rewrite Z.add_0_l. reflexivity.
  Qed.

  Lemma RB_step : forall i, Z.of_nat i < nb -> RB i (fp_rb fm ec bh nb i) ->
    let s := fp_rb fm ec bh nb i in let fc := snd (fst s) in let j := snd s in let j' := fs_skip0 258%nat fc j in
    0 <= j /\ j' <= 255 /\ (zget fc j' =? 0) = false /\ 1 <= zget fc j' <= nb /\ RB (S i) (fp_rb fm ec bh nb (S i)).
  Proof.
    intros i Hi R. cbn zeta. cps_destruct R as (Rj & Rnn & Rz & Rs).
    set (s := fp_rb fm ec bh nb i) in *. set (fc := snd (fst s)) in *. set (j := snd s) in *.
    cps_destruct (sumF_pos_ex 256 (zget fc) 0 ltac:(intros; apply Rnn) ltac:(lia)) as (b & Hb & Gb).
    assert (JB : j <= b). { destruct (Z.lt_ge_cases b j) as [L|G]; [|exact G]. rewrite Rz in Gb by exact L. lia. }
    cps_destruct (skip0_spec 258%nat fc j b JB ltac:(cbn; lia) ltac:(lia)) as (A & B & C). cbn zeta in A, B, C.
    set (j' := fs_skip0 258 fc j) in *.
    pose proof (Rnn j') as NNj'. pose proof (sumF_term_le 256 (zget fc) 0 j' ltac:(intros; apply Rnn) ltac:(lia)) as TL.
    split; [lia|]. split; [lia|]. split; [apply Z.eqb_neq; exact B|]. split; [lia|].
    unfold RB. rewrite fp_rb_S. cbn zeta. fold s. fold fc. fold j. fold j'. cbn [fst snd].
    split; [lia|]. split; [|split].
    - intros b0. rewrite zget_zset. destruct (Z.eqb_spec b0 j'); [lia| apply Rnn].
    - intros b0 Hb0. rewrite zget_zset. destruct (Z.eqb_spec b0 j'); [lia|].
      destruct (Z.lt_ge_cases b0 j); [apply Rz; assumption | apply C; lia].
    - rewrite (sumF_upd 256 (zget fc) _ 0 j' (-1)); [rewrite Rs; lia | lia |].
      intros x. rewrite zget_zset. destruct (Z.eqb_spec x j'); [subst; lia|reflexivity].
  Qed.

  Theorem fsf_rebuild_ok : fsf_rebuild fm ec bh nb.
  Proof.
    assert (ALL : forall i, Z.of_nat i <= nb -> RB i (fp_rb fm ec bh nb i)).
    { induction i as [|i IH]; intros Hi; [apply RB0|].
      cps_destruct (RB_step i ltac:(lia) (IH ltac:(lia))) as (_ & _ & _ & _ & R). exact R. }
    intros i Hi. cbn zeta.
    cps_destruct (RB_step (Z.to_nat i) ltac:(lia) (ALL (Z.to_nat i) ltac:(lia))) as (A & B & C & D & _). cbn zeta in *.
    repeat split; try assumption; lia.
  Qed.
End S5.
