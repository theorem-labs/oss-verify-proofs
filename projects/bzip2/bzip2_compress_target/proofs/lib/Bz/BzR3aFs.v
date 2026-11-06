(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCSortF BzCLemmasFs BzCFactsFs BzCFactsFs2 BzCPermF BzCPermF2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCPermF2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCScanF BzR2Theory BzR3aPre BzR3aQs.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCSortF BzCLemmasFs BzCFactsFs BzCFactsFs2 BzCPermF BzCPermF2. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCPermF2. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCScanF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzR3aEc.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2.BzCQsortF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCScanF.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma word_ones_bits : forall bh q b, 0 <= q -> q mod 32 = 0 -> bh_word bh q = 4294967295 ->
  q <= b <= q + 31 -> isset_bh bh b = true.
Proof.
  intros bh q b Hq Ha Hw Hb. rewrite isset_tb by lia. unfold bh_word in Hw. rewrite shiftr5_div in Hw.
  replace (b / 32) with (q / 32) by (Z.div_mod_to_equations; lia). rewrite Hw.
  change 4294967295 with (Z.ones 32). apply Z.ones_spec_low. pose proof (Z.mod_pos_bound b 32 ltac:(lia)). lia.
Qed.
Lemma word_zero_bits : forall bh q b, 0 <= q -> q mod 32 = 0 -> bh_word bh q = 0 ->
  q <= b <= q + 31 -> isset_bh bh b = false.
Proof.
  intros bh q b Hq Ha Hw Hb. rewrite isset_tb by lia. unfold bh_word in Hw. rewrite shiftr5_div in Hw.
  replace (b / 32) with (q / 32) by (Z.div_mod_to_equations; lia). rewrite Hw. apply Z.bits_0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma scanB_bits : forall f bh k x, 0 <= k -> k mod 32 = 0 -> k <= x < fs_scan_word_ff f bh k -> isset_bh bh x = true.
Proof.
  induction f as [|f IH]; intros bh k x Hk Ha Hx; cbn [fs_scan_word_ff] in Hx; [lia|].
  destruct (Z.eqb_spec (bh_word bh k) 4294967295) as [E|NE]; [|lia].
  destruct (Z.lt_ge_cases x (k + 32)) as [L|G].
  - apply (word_ones_bits bh k x); lia || assumption.
  - apply (IH bh (k + 32) x); [lia | Z.div_mod_to_equations; lia | lia].
Qed.
Lemma scanE_bits : forall f bh k x, 0 <= k -> k mod 32 = 0 -> k <= x < fs_scan_word_00 f bh k -> isset_bh bh x = false.
Proof.
  induction f as [|f IH]; intros bh k x Hk Ha Hx; cbn [fs_scan_word_00] in Hx; [lia|].
  destruct (Z.eqb_spec (bh_word bh k) 0) as [E|NE]; [|lia].
  destruct (Z.lt_ge_cases x (k + 32)) as [L|G].
  - apply (word_zero_bits bh k x); lia || assumption.
  - apply (IH bh (k + 32) x); [lia | Z.div_mod_to_equations; lia | lia].
Qed.

(* [comment removed for export] *)
Section Bracket.
  Variables (bh : zarr) (nb : Z).
  Hypothesis NB : 1 <= nb.
  Hypothesis SENT : sent bh nb.

  Lemma bit_nb : isset_bh bh nb = true.
  Proof. pose proof (proj1 (SENT 0 ltac:(lia))) as T. rewrite Z.mul_0_r, Z.add_0_r in T. exact T. Qed.

  Theorem bracket : forall k0, 0 <= k0 <= nb -> isset_bh bh k0 = true ->
    let l := bk1 nb bh k0 - 1 in let r := bk2 nb bh (bk1 nb bh k0) - 1 in
    k0 <= l /\ (forall x, k0 <= x <= l -> isset_bh bh x = true) /\
    (l < nb -> isset_bh bh (l + 1) = false /\ l < r < nb /\
               (forall x, l < x <= r -> isset_bh bh x = false) /\ isset_bh bh (r + 1) = true).
  Proof.
    intros k0 Hk0 B0. cbv zeta.
    cps_pose (scanA_ok bh nb NB k0 ltac:(lia) ltac:(lia)) as (A1 & A2 & A3). set (kA := fs_scan_set_unal (FSC nb) bh k0) in *.
    (* [comment removed for export] *)
    assert (K1 : k0 <= bk1 nb bh k0 /\ isset_bh bh (bk1 nb bh k0) = false /\ (forall x, k0 <= x < bk1 nb bh k0 -> isset_bh bh x = true)).
    { unfold bk1. cbv zeta. fold kA. destruct (isset_bh bh kA) eqn:IA.
      - assert (AL : kA mod 32 = 0).
        { cbn [andb] in A2. rewrite unaligned_bh_mod in A2. apply Bool.negb_false_iff in A2. apply Z.eqb_eq in A2. exact A2. }
        cps_pose (scanB_ok bh nb NB SENT kA ltac:(lia) AL) as (B1 & B2 & B3). set (kB := fs_scan_word_ff (FSC nb) bh kA) in *.
        cps_pose (scanC_ok bh nb NB SENT kB ltac:(lia)) as (C1 & C2 & C3).
        split; [lia|]. split; [exact C2|]. intros x Hx.
        destruct (Z.lt_ge_cases x kA) as [L|G]; [apply A3; lia|].
        destruct (Z.lt_ge_cases x kB) as [L2|G2]; [apply (scanB_bits (FSC nb) bh kA x); lia || assumption | apply C3; lia].
      - split; [lia|]. split; [exact IA|]. intros x Hx. apply A3. lia. }
    cps_destruct K1 as (K1a & K1b & K1c). set (k1 := bk1 nb bh k0) in *.
    assert (K1gt : k0 < k1). { destruct (Z.eq_dec k0 k1) as [E|N]; [|lia]. rewrite <- E in K1b. rewrite K1b in B0. discriminate. }
    split; [lia|]. split; [intros x Hx; apply K1c; lia|].
    intros Hl. replace (k1 - 1 + 1) with k1 by lia. split; [exact K1b|].
    (* [comment removed for export] *)
    cps_pose (scanD_ok bh nb NB k1 ltac:(lia) ltac:(lia)) as (D1 & D2 & D3). set (kD := fs_scan_clr_unal (FSC nb) bh k1) in *.
    assert (K2 : k1 <= bk2 nb bh k1 /\ isset_bh bh (bk2 nb bh k1) = true /\ (forall x, k1 <= x < bk2 nb bh k1 -> isset_bh bh x = false)).
    { unfold bk2. cbv zeta. fold kD. destruct (isset_bh bh kD) eqn:ID; cbn [negb].
      - split; [lia|]. split; [exact ID|]. intros x Hx. apply D3. lia.
      - assert (AL : kD mod 32 = 0).
        { cbn [andb negb] in D2. rewrite unaligned_bh_mod in D2. apply Bool.negb_false_iff in D2. apply Z.eqb_eq in D2. exact D2. }
        cps_pose (scanE_ok bh nb NB SENT kD ltac:(lia) AL) as (E1 & E2 & E3). set (kE := fs_scan_word_00 (FSC nb) bh kD) in *.
        cps_pose (scanF_ok bh nb NB SENT kE ltac:(lia)) as (F1 & F2 & F3).
        split; [lia|]. split; [exact F2|]. intros x Hx.
        destruct (Z.lt_ge_cases x kD) as [L|G]; [apply D3; lia|].
        destruct (Z.lt_ge_cases x kE) as [L2|G2]; [apply (scanE_bits (FSC nb) bh kD x); lia || assumption | apply F3; lia]. }
    cps_destruct K2 as (K2a & K2b & K2c). set (k2 := bk2 nb bh k1) in *.
    assert (K2gt : k1 < k2). { destruct (Z.eq_dec k1 k2) as [E|N]; [|lia]. rewrite <- E in K2b. rewrite K2b in K1b. discriminate. }
    assert (K2le : k2 <= nb). { destruct (Z.le_gt_cases k2 nb) as [|G]; [assumption|]. exfalso.
                                pose proof (K2c nb ltac:(lia)) as X. rewrite bit_nb in X. discriminate. }
    replace (k2 - 1 + 1) with k2 by lia.
    split; [lia|]. split; [intros x Hx; apply K2c; lia | exact K2b].
  Qed.
End Bracket.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma isset_fs_headers_in : forall n bh ec fm i cc k, 0 <= i -> i <= k < i + Z.of_nat n ->
  isset_bh (fs_headers n bh ec fm i cc) k =
  (isset_bh bh k || negb ((if k =? i then cc else key ec fm (k - 1)) =? key ec fm k))%bool.
Proof.
  induction n as [|n IH]; intros bh ec fm i cc k Hi Hk; [lia|].
  rewrite fs_headers_S. cbv zeta. fold (key ec fm i).
  destruct (Z.eq_dec k i) as [->|NE].
  - rewrite Z.eqb_refl. destruct (Z.eqb_spec cc (key ec fm i)) as [E|N]; cbn [negb].
    + rewrite isset_fs_headers_out by lia. rewrite Bool.orb_false_r. reflexivity.
    + rewrite isset_fs_headers_out by lia. rewrite isset_set_bh by lia. rewrite Z.eqb_refl. cbn. rewrite Bool.orb_true_r. reflexivity.
  - replace (k =? i) with false by (symmetry; apply Z.eqb_neq; exact NE).
    destruct (Z.eqb_spec cc (key ec fm i)) as [E|N]; cbn [negb].
    + rewrite IH by lia. destruct (Z.eqb_spec k (i + 1)) as [->|N2]; [|reflexivity].
      replace (i + 1 - 1) with i by lia. rewrite E. reflexivity.
    + rewrite IH by lia. rewrite isset_set_bh by lia. replace (k =? i) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [orb].
      destruct (Z.eqb_spec k (i + 1)) as [->|N2]; [|reflexivity]. replace (i + 1 - 1) with i by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section EclassVal.
  Variables (nb : Z) (fm bh : zarr) (H : Z).
  Hypothesis NB : 1 <= nb <= 4294967296. Hypothesis HH : 1 <= H <= nb. Hypothesis PM : fm_perm fm nb.

  (* [comment removed for export] *)
  Fixpoint hdrn (x : nat) : Z :=
    match x with
    | O => 0
    | S x' => if isset_bh bh (Z.of_nat x) then Z.of_nat x else hdrn x'
    end.
  Definition hdr (x : Z) : Z := hdrn (Z.to_nat x).

  Lemma hdr_0 : hdr 0 = 0. Proof. reflexivity. Qed.
  Lemma hdr_S : forall x, 0 <= x -> hdr (x + 1) = if isset_bh bh (x + 1) then x + 1 else hdr x.
  Proof.
    intros x Hx. unfold hdr. replace (Z.to_nat (x + 1)) with (S (Z.to_nat x)) by lia. cbn [hdrn].
    replace (Z.of_nat (S (Z.to_nat x))) with (x + 1) by lia. reflexivity.
  Qed.
  Lemma hdr_step : forall i, 0 < i -> hdr i = if isset_bh bh i then i else hdr (i - 1).
  Proof. intros i Hi. pose proof (hdr_S (i - 1) ltac:(lia)) as E. replace (i - 1 + 1) with i in E by lia. exact E. Qed.
  Lemma hdrn_range : forall m, 0 <= hdrn m <= Z.of_nat m.
  Proof. induction m as [|m IH]; cbn [hdrn]; [lia|]. destruct (isset_bh bh (Z.of_nat (S m))); lia. Qed.
  Lemma hdr_range : forall x, 0 <= x -> 0 <= hdr x <= x.
  Proof. intros x Hx. unfold hdr. pose proof (hdrn_range (Z.to_nat x)). lia. Qed.

  (* [comment removed for export] *)
  Lemma eclass_val_step : forall n ec i j,
    0 <= i -> i + Z.of_nat n <= nb -> j = (if i =? 0 then 0 else hdr (i - 1)) ->
    (forall i', 0 <= i' < i -> rd32 ec (kk nb fm H i') = hdr i') ->
    forall i', 0 <= i' < i + Z.of_nat n -> rd32 (fs_eclass n ec fm bh H nb i j) (kk nb fm H i') = hdr i'.
  Proof.
    induction n as [|n IH]; intros ec i j Hi Hn Hj P i' Hi'.
    - cbn [fs_eclass]. apply P. lia.
    - rewrite fs_eclass_S. cbv zeta. change (if rd32 fm i - H <? 0 then rd32 fm i - H + nb else rd32 fm i - H) with (kk nb fm H i).
      set (j' := if isset_bh bh i then i else j).
      assert (Hj' : j' = hdr i).
      { subst j' j. destruct (Z.eqb_spec i 0) as [->|N]; [rewrite hdr_0; destruct (isset_bh bh 0); reflexivity|].
        rewrite (hdr_step i) by lia. reflexivity. }
      pose proof (hdr_range i Hi) as HR.
      replace (i + Z.of_nat (S n)) with (i + 1 + Z.of_nat n) in Hi' |- * by lia.
      apply (IH _ (i + 1) j'); [lia | lia | | | lia].
      + rewrite Hj'. replace (i + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). f_equal. lia.
      + intros x Hx. destruct (Z.eq_dec x i) as [->|N].
        * rewrite rd32_wr32_same; [exact Hj'|]. rewrite Hj'. lia.
        * rewrite rd32_wr32_other; [apply P; lia|]. intros E. apply N. apply (kk_inj nb fm H HH PM); lia || exact E.
  Qed.

  Theorem eclass_val : forall ec i, 0 <= i < nb ->
    rd32 (fs_eclass (Z.to_nat nb) ec fm bh H nb 0 0) (kk nb fm H i) = hdr i.
  Proof.
    intros ec i Hi. apply (eclass_val_step (Z.to_nat nb) ec 0 0); [lia | lia | reflexivity | intros; lia | lia].
  Qed.
End EclassVal.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma isset_fs_bh_init_iff : forall n bh ft i k, 0 <= k -> (forall b, i <= b < i + Z.of_nat n -> 0 <= zget ft b) ->
  isset_bh (fs_bh_init n bh ft i) k = true <-> isset_bh bh k = true \/ exists b, i <= b < i + Z.of_nat n /\ zget ft b = k.
Proof.
  induction n as [|n IH]; intros bh ft i k Hk Hft.
  - cbn [fs_bh_init]. split; [tauto|]. intros [A|(b & Hb & _)]; [exact A|lia].
  - rewrite fs_bh_init_S. rewrite IH; [|lia|intros b Hb; apply Hft; lia]. rewrite isset_set_bh by (try apply Hft; lia).
    rewrite Bool.orb_true_iff, Z.eqb_eq. split.
    + intros [[A|A]|(b & Hb & E)]; [right; exists i; split; [lia|auto] | tauto | right; exists b; split; [lia|exact E]].
    + intros [A|(b & Hb & E)]; [tauto|]. destruct (Z.eq_dec b i) as [->|N]; [left; left; auto | right; exists b; split; [lia|exact E]].
Qed.

Lemma isset_fs_bh_zero : forall n bh k, 0 <= k < 32 * Z.of_nat n -> isset_bh (fs_bh_zero n bh 0) k = false.
Proof.
  intros n bh k Hk. rewrite isset_tb by lia. rewrite fs_bh_zero_get.
  replace ((0 <=? k / 32) && (k / 32 <? 0 + Z.of_nat n))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; Z.div_mod_to_equations; lia).
  apply Z.bits_0.
Qed.
End BzR3aEc.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2.BzCQsortF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCScanF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2Theory OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR3aPre OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR3aQs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR3aFs.BzR3aEc.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section FS.
  Variable t : list Z.                        (* [comment removed for export] *)
  Let n : nat := length t.
  Let nb : Z := Z.of_nat n.
  Hypothesis NB : 1 <= nb <= 900000.

  Local Notation PRE := (BzR3aPre.pre t).
  Let Hn0 : (0 < n)%nat. Proof. unfold nb in NB. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition INV (H : nat) (fm bh : zarr) : Prop :=
    fm_perm fm nb /\ sent bh nb /\ isset_bh bh 0 = true /\
    (forall i j, 0 <= i -> i <= j -> j < nb -> lexle (PRE H (rd32 fm i)) (PRE H (rd32 fm j))) /\
    (forall i, 0 < i < nb -> (isset_bh bh i = true <-> lexlt (PRE H (rd32 fm (i - 1))) (PRE H (rd32 fm i)))).

  Section Classes.
    Variables (H : nat) (fm bh : zarr).
    Hypothesis IV : INV H fm bh.
    Let PM := proj1 IV.
    Let I2 := proj1 (proj2 (proj2 (proj2 IV))).
    Let I3 := proj2 (proj2 (proj2 (proj2 IV))).

    (* [comment removed for export] *)
    Lemma noset_eq : forall i j, 0 <= i -> i <= j -> j < nb ->
      (forall m, i < m <= j -> isset_bh bh m = false) -> PRE H (rd32 fm i) = PRE H (rd32 fm j).
    Proof.
      intros i j Hi Hij Hj. remember (Z.to_nat (j - i)) as d eqn:Hd. revert j Hij Hj Hd.
      induction d as [|d IH]; intros j Hij Hj Hd NS.
      - replace j with i by lia. reflexivity.
      - rewrite (IH (j - 1)); [|lia|lia|lia|intros m Hm; apply NS; lia].
        destruct (I2 (j - 1) j ltac:(lia) ltac:(lia) Hj) as [LT|EQ]; [|exact EQ].
        exfalso. pose proof (proj2 (I3 j ltac:(lia)) LT) as B. rewrite (NS j) in B by lia. discriminate.
    Qed.

    (* [comment removed for export] *)
    Lemma set_lt : forall i j m, 0 <= i -> i < m -> m <= j -> j < nb -> isset_bh bh m = true ->
      lexlt (PRE H (rd32 fm i)) (PRE H (rd32 fm j)).
    Proof.
      intros i j m Hi Him Hmj Hj B.
      pose proof (proj1 (I3 m ltac:(lia)) B) as LT.
      pose proof (I2 i (m - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as A.
      pose proof (I2 m j ltac:(lia) ltac:(lia) ltac:(lia)) as C.
      destruct A as [A| A]; [|rewrite A]; destruct C as [C|C]; try rewrite <- C; eauto using lexlt_trans.
    Qed.

    (* [comment removed for export] *)
    Lemma hdr_spec : forall i, 0 <= i -> 0 <= hdr bh i <= i /\ isset_bh bh (hdr bh i) = true /\
      (forall m, hdr bh i < m <= i -> isset_bh bh m = false).
    Proof.
      intros i Hi. remember (Z.to_nat i) as d eqn:Hd. revert i Hi Hd.
      induction d as [|d IH]; intros i Hi Hd.
      - replace i with 0 by lia. rewrite hdr_0. split; [lia|]. split; [exact (proj1 (proj2 (proj2 IV)))|intros; lia].
      - cps_destruct (IH (i - 1) ltac:(lia) ltac:(lia)) as (A & B & C).
        rewrite (hdr_step bh i) by lia. destruct (isset_bh bh i) eqn:Bi.
        + split; [lia|]. split; [exact Bi|intros; lia].
        + split; [lia|]. split; [exact B|]. intros m Hm. destruct (Z.eq_dec m i) as [->|N]; [exact Bi|apply C; lia].
    Qed.

    Lemma hdr_eq_pre : forall i, 0 <= i < nb -> PRE H (rd32 fm (hdr bh i)) = PRE H (rd32 fm i).
    Proof.
      intros i Hi. cps_destruct (hdr_spec i ltac:(lia)) as (A & B & C). apply noset_eq; try lia. exact C.
    Qed.

    Lemma hdr_lt_pre : forall i j, 0 <= i < nb -> 0 <= j < nb -> hdr bh i < hdr bh j ->
      lexlt (PRE H (rd32 fm i)) (PRE H (rd32 fm j)).
    Proof.
      intros i j Hi Hj L. cps_destruct (hdr_spec i ltac:(lia)) as (A & B & C). cps_destruct (hdr_spec j ltac:(lia)) as (A' & B' & C').
      destruct (Z.lt_ge_cases i (hdr bh j)) as [X|X].
      - apply (set_lt i j (hdr bh j)); try lia. exact B'.
      - exfalso. rewrite (C (hdr bh j)) in B' by lia. discriminate.
    Qed.

    Lemma hdr_cmp : forall i j, 0 <= i < nb -> 0 <= j < nb ->
      (hdr bh i < hdr bh j <-> lexlt (PRE H (rd32 fm i)) (PRE H (rd32 fm j))) /\
      (hdr bh i = hdr bh j <-> PRE H (rd32 fm i) = PRE H (rd32 fm j)).
    Proof.
      intros i j Hi Hj.
      assert (E : hdr bh i = hdr bh j -> PRE H (rd32 fm i) = PRE H (rd32 fm j)).
      { intros E. rewrite <- (hdr_eq_pre i), <- (hdr_eq_pre j) by lia. rewrite E. reflexivity. }
      split; split.
      - apply hdr_lt_pre; lia.
      - intros L. destruct (Z.lt_trichotomy (hdr bh i) (hdr bh j)) as [X|[X|X]]; [exact X| |].
        + exfalso. rewrite (E X) in L. exact (lexlt_irrefl _ L).
        + exfalso. pose proof (hdr_lt_pre j i Hj Hi X) as L'. exact (lexlt_irrefl _ (lexlt_trans _ _ _ L L')).
      - exact E.
      - intros P. destruct (Z.lt_trichotomy (hdr bh i) (hdr bh j)) as [X|[X|X]]; [|exact X|]; exfalso.
        + pose proof (hdr_lt_pre i j Hi Hj X) as L. rewrite P in L. exact (lexlt_irrefl _ L).
        + pose proof (hdr_lt_pre j i Hj Hi X) as L. rewrite P in L. exact (lexlt_irrefl _ L).
    Qed.
  End Classes.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Key.
    Variables (HZ : Z) (H : nat) (fm0 bh0 ec0 : zarr).
    Hypothesis HHZ : HZ = Z.of_nat H.
    Hypothesis HH : 1 <= HZ <= nb.
    Hypothesis IV : INV H fm0 bh0.
    Let ec1 := fs_eclass (Z.to_nat nb) ec0 fm0 bh0 HZ nb 0 0.

    (* [comment removed for export] *)
    Lemma key_pos : forall p, 0 <= p < nb -> exists i, 0 <= i < nb /\ rd32 fm0 i = (p + HZ) mod nb /\ rd32 ec1 p = hdr bh0 i.
    Proof.
      intros p Hp. pose proof (proj1 IV) as PM.
      cps_destruct (fm_perm_onto fm0 nb PM ((p + HZ) mod nb) ltac:(apply Z.mod_pos_bound; lia)) as (i & Hi & Ei).
      exists i. split; [exact Hi|]. split; [exact Ei|].
      replace p with (kk nb fm0 HZ i).
      - apply eclass_val; try lia. exact PM.
      - unfold kk. rewrite Ei. destruct (Z.lt_ge_cases (p + HZ) nb) as [L|G].
        + rewrite Z.mod_small by lia. destruct (Z.ltb_spec (p + HZ - HZ) 0); lia.
        + rewrite <- (Z.mod_unique (p + HZ) nb 1 (p + HZ - nb)) by lia. destruct (Z.ltb_spec (p + HZ - nb - HZ) 0); lia.
    Qed.

    Lemma key_cmp : forall p q, 0 <= p < nb -> 0 <= q < nb ->
      (rd32 ec1 p < rd32 ec1 q <-> lexlt (PRE H (p + HZ)) (PRE H (q + HZ))) /\
      (rd32 ec1 p = rd32 ec1 q <-> PRE H (p + HZ) = PRE H (q + HZ)).
    Proof.
      intros p q Hp Hq.
      cps_destruct (key_pos p Hp) as (i & Hi & Ei & ->). cps_destruct (key_pos q Hq) as (j & Hj & Ej & ->).
      replace (PRE H (p + HZ)) with (PRE H ((p + HZ) mod nb)) by (apply pre_mod; exact Hn0).
      replace (PRE H (q + HZ)) with (PRE H ((q + HZ) mod nb)) by (apply pre_mod; exact Hn0).
      rewrite <- Ei, <- Ej. apply (hdr_cmp H fm0 bh0 IV); assumption.
    Qed.

    Lemma key_le : forall p q, 0 <= p < nb -> 0 <= q < nb ->
      rd32 ec1 p <= rd32 ec1 q -> lexle (PRE H (p + HZ)) (PRE H (q + HZ)).
    Proof.
      intros p q Hp Hq L. destruct (key_cmp p q Hp Hq) as [A B].
      destruct (Z.lt_ge_cases (rd32 ec1 p) (rd32 ec1 q)) as [X|X]; [left; apply A; exact X | right; apply B; lia].
    Qed.
  End Key.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Round.
    Variables (HZ : Z) (H : nat) (fm0 bh0 ec0 : zarr).
    Hypothesis HHZ : HZ = Z.of_nat H.
    Hypothesis HH : 1 <= HZ <= nb.
    Hypothesis IV : INV H fm0 bh0.
    Let ec1 := fs_eclass (Z.to_nat nb) ec0 fm0 bh0 HZ nb 0 0.
    Let H2 := (H + H)%nat.

    Definition BV (s : fbs) : Prop :=
      fb_ec s = ec1 /\ fm_perm (fb_fm s) nb /\ sent (fb_bh s) nb /\ isset_bh (fb_bh s) 0 = true /\
      -1 <= fb_r s < nb /\ 0 <= fb_nnd s /\ (fb_nnd s = 0 -> fb_r s = -1) /\
      (fb_done s = false -> isset_bh (fb_bh s) (fb_r s + 1) = true) /\
      (fb_done s = true -> forall i, fb_r s < i < nb -> isset_bh (fb_bh s) i = true) /\
      (forall i, 0 <= i < nb -> PRE H (rd32 (fb_fm s) i) = PRE H (rd32 fm0 i)) /\
      (forall i, fb_r s < i < nb -> rd32 (fb_fm s) i = rd32 fm0 i) /\
      (forall i, fb_r s < i -> 0 <= i -> isset_bh (fb_bh s) i = isset_bh bh0 i) /\
      (forall i j, 0 <= i -> i <= j -> j <= fb_r s -> lexle (PRE H2 (rd32 (fb_fm s) i)) (PRE H2 (rd32 (fb_fm s) j))) /\
      (forall i, 0 < i <= fb_r s -> (isset_bh (fb_bh s) i = true <-> lexlt (PRE H2 (rd32 (fb_fm s) (i - 1))) (PRE H2 (rd32 (fb_fm s) i)))).

    Lemma BV_init : forall slo shi, BV (FBS fm0 ec1 bh0 slo shi (-1) 0 false).
    Proof.
      intros slo shi. cps_pose IV as (PM & SE & B0 & I2 & I3).
      unfold BV; cbn [fb_ec fb_fm fb_bh fb_r fb_nnd fb_done].
      split; [reflexivity|]. split; [exact PM|]. split; [exact SE|]. split; [exact B0|].
      split; [lia|]. split; [lia|]. split; [intros; reflexivity|]. split; [intros _; exact B0|]. split; [intros; discriminate|].
      split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
      split; [intros; lia|]. intros; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma strict_across : forall (fm : zarr) i j m, (forall x, 0 <= x < nb -> PRE H (rd32 fm x) = PRE H (rd32 fm0 x)) ->
      0 <= i -> i < m -> m <= j -> j < nb -> isset_bh bh0 m = true ->
      lexlt (PRE H2 (rd32 fm i)) (PRE H2 (rd32 fm j)).
    Proof.
      intros fm i j m B Hi Him Hmj Hj Bm. unfold H2. apply (pre_lt_ext t Hn0 H); [lia|].
      rewrite (B i), (B j) by lia. apply (set_lt H fm0 bh0 IV i j m); assumption.
    Qed.

    Lemma BV_step : forall s, fb_done s = false -> BV s -> BV (fs_bucket_iter nb s).
    Proof.
      intros [fm ec bh slo shi r nnd dn] Hd V. cbn [fb_done] in Hd. subst dn.
      cps_destruct V as (Eec & PM & SE & B0 & Hr & Hnnd & Hnnd0 & Br & _ & B & E & EB & D & C).
      cbn [fb_ec fb_fm fb_bh fb_r fb_nnd fb_done] in *. subst ec. specialize (Br eq_refl).
      cps_pose IV as (PM0 & SE0 & B00 & I2 & I3).
      rewrite fs_bucket_iter_unfold. cbv zeta.
      pose proof (bracket bh nb ltac:(lia) SE (r + 1) ltac:(lia) Br) as BK. cbv zeta in BK.
      cps_destruct BK as (L0 & SETS & BK).
      set (l := bk1 nb bh (r + 1) - 1) in *.
      set (r2 := bk2 nb bh (bk1 nb bh (r + 1)) - 1) in *.
      replace (bk1 nb bh (r + 1)) with (l + 1) in r2 |- * by lia. fold r2.
      destruct (Z.leb_spec nb l) as [C1|C1].
      { (* [comment removed for export] *)
        unfold BV; cbn [fb_ec fb_fm fb_bh fb_r fb_nnd fb_done].
        split; [reflexivity|]. split; [exact PM|]. split; [exact SE|]. split; [exact B0|].
        split; [lia|]. split; [lia|]. split; [exact Hnnd0|]. split; [intros; discriminate|].
        split; [intros _ i Hi; apply SETS; lia|].
        split; [exact B|]. split; [exact E|]. split; [exact EB|]. split; [exact D|exact C]. }
      cps_destruct (BK C1) as (CLl & LR & CLR & SETr). clear BK.
      destruct (Z.leb_spec nb r2) as [C2|C2]; [lia|].
      destruct (Z.ltb_spec l r2) as [C3|C3]; [|lia].
      (* [comment removed for export] *)
      assert (F1 : forall i, l <= i <= r2 -> rd32 fm i = rd32 fm0 i) by (intros i Hi; apply E; lia).
      assert (F2l : isset_bh bh0 l = true) by (rewrite <- EB by lia; apply SETS; lia).
      assert (F2m : forall m, l < m <= r2 -> isset_bh bh0 m = false) by (intros m Hm; rewrite <- EB by lia; apply CLR; lia).
      assert (F2r : isset_bh bh0 (r2 + 1) = true) by (rewrite <- EB by lia; exact SETr).
      assert (Fk0 : isset_bh bh0 (r + 1) = true) by (rewrite <- EB by lia; exact Br).
      assert (F3 : forall x, l <= x <= r2 -> PRE H (rd32 fm0 x) = PRE H (rd32 fm0 l)).
      { intros x Hx. symmetry. apply (noset_eq H fm0 bh0 IV l x); try lia. intros m Hm. apply F2m. lia. }
      pose proof (fallbackQSort3_sorted ec1 nb fm slo shi l r2 PM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as QS.
      cbv zeta in QS. cps_destruct QS as (SRT & PM' & FR).
      set (fm' := fq_fm (fallbackQSort3 fm ec1 slo shi l r2)) in *.
      assert (F4 : forall i, l <= i <= r2 -> exists i', l <= i' <= r2 /\ rd32 fm' i = rd32 fm0 i').
      { intros i Hi. cps_destruct (perm_frame_src fm fm' nb l r2 PM PM' FR ltac:(lia) ltac:(lia) i Hi) as (i' & Hi' & Ei').
        exists i'. split; [exact Hi'|]. rewrite Ei'. apply F1. exact Hi'. }
      assert (NB' : forall i, 0 <= i < nb -> PRE H (rd32 fm' i) = PRE H (rd32 fm0 i)).
      { intros i Hi. destruct (Z.lt_ge_cases i l) as [X|X]; [rewrite FR by lia; apply B; lia|].
        destruct (Z.lt_ge_cases r2 i) as [Y|Y]; [rewrite FR by lia; apply B; lia|].
        cps_destruct (F4 i ltac:(lia)) as (i' & Hi' & ->). rewrite (F3 i'), (F3 i) by lia. reflexivity. }
      assert (RG : forall i, 0 <= i < nb -> 0 <= rd32 fm' i < nb) by (intros i Hi; apply (proj1 PM'); exact Hi).
      (* [comment removed for export] *)
      assert (F8le : forall i j, l <= i -> i <= j -> j <= r2 -> lexle (PRE H2 (rd32 fm' i)) (PRE H2 (rd32 fm' j))).
      { intros i j Hi Hij Hj. unfold H2. apply (proj2 (pre2_le t Hn0 H (rd32 fm' i) (rd32 fm' j))). right.
        split; [rewrite (NB' i), (NB' j) by lia; rewrite (F3 i), (F3 j) by lia; reflexivity|].
        rewrite <- HHZ. apply (key_le HZ H fm0 bh0 ec0 HH IV); [apply RG; lia|apply RG; lia|]. apply SRT; lia. }
      assert (F8lt : forall i, l < i <= r2 ->
                (key ec1 fm' (i - 1) <> key ec1 fm' i <-> lexlt (PRE H2 (rd32 fm' (i - 1))) (PRE H2 (rd32 fm' i)))).
      { intros i Hi. unfold H2. rewrite (pre2_lt t Hn0 H).
        pose proof (key_cmp HZ H fm0 bh0 ec0 HH IV (rd32 fm' (i - 1)) (rd32 fm' i) ltac:(apply RG; lia) ltac:(apply RG; lia)) as [K1 K2].
        fold ec1 in K1, K2. unfold key. rewrite <- HHZ.
        pose proof (SRT (i - 1) i ltac:(lia) ltac:(lia) ltac:(lia)) as LE. unfold key in LE.
        assert (EQH : PRE H (rd32 fm' (i - 1)) = PRE H (rd32 fm' i)) by (rewrite (NB' (i - 1)), (NB' i) by lia; rewrite (F3 (i - 1)), (F3 i) by lia; reflexivity).
        split.
        - intros NE. right. split; [exact EQH|]. apply K1. lia.
        - intros [LT|[_ LT]]; [exfalso; rewrite EQH in LT; exact (lexlt_irrefl _ LT)|].
          intros EK. apply K2 in EK. rewrite EK in LT. exact (lexlt_irrefl _ LT). }
      set (bh' := fs_headers (Z.to_nat (r2 - l + 1)) bh ec1 fm' l (-1)).
      assert (HO : forall k, 0 <= k -> k < l \/ r2 < k -> isset_bh bh' k = isset_bh bh k).
      { intros k Hk Hk2. subst bh'. apply isset_fs_headers_out; lia. }
      assert (HIN : forall k, l <= k <= r2 -> isset_bh bh' k =
                (isset_bh bh k || negb ((if k =? l then -1 else key ec1 fm' (k - 1)) =? key ec1 fm' k))%bool).
      { intros k Hk. subst bh'. apply isset_fs_headers_in; lia. }
      unfold BV; cbn [fb_ec fb_fm fb_bh fb_r fb_nnd fb_done]. fold fm'. fold bh'.
      split; [reflexivity|]. split; [exact PM'|].
      split; [subst bh'; apply sent_fs_headers; try lia; exact SE|].
      split; [subst bh'; apply isset_fs_headers_mono; try lia; exact B0|].
      split; [lia|]. split; [lia|]. split; [intros; lia|].
      split; [intros _; subst bh'; apply isset_fs_headers_mono; try lia; exact SETr|].
      split; [intros; discriminate|].
      split; [exact NB'|].
      split; [intros i Hi; rewrite FR by lia; apply E; lia|].
      split; [intros i Hi Hi0; rewrite HO by lia; apply EB; lia|].
      split.
      - (* [comment removed for export] *)
        intros i j Hi Hij Hj. destruct (Z.eq_dec i j) as [->|NE]; [apply lexle_refl|].
        destruct (Z.le_gt_cases j r) as [JR|JR].
        + rewrite !FR by lia. apply D; lia.
        + destruct (Z.le_gt_cases i r) as [IR|IR].
          * left. apply (strict_across fm' i j (r + 1)); try lia; assumption.
          * destruct (Z.lt_ge_cases i l) as [IL|IL].
            -- left. apply (strict_across fm' i j (i + 1)); try lia; [exact NB'|].
               rewrite <- EB by lia. apply SETS. lia.
            -- apply F8le; lia.
      - (* [comment removed for export] *)
        intros i Hi. destruct (Z.le_gt_cases i r) as [IR|IR].
        + rewrite HO by lia. rewrite !FR by lia. apply C. lia.
        + destruct (Z.le_gt_cases i l) as [IL|IL].
          * assert (T : isset_bh bh' i = true).
            { destruct (Z.eq_dec i l) as [->|NE].
              - rewrite HIN by lia. rewrite (SETS l) by lia. reflexivity.
              - rewrite HO by lia. apply SETS. lia. }
            rewrite T. split; [intros _|reflexivity].
            apply (strict_across fm' (i - 1) i i); try lia; [exact NB'|]. rewrite <- EB by lia. apply SETS. lia.
          * rewrite HIN by lia. rewrite (CLR i) by lia. replace (i =? l) with false by (symmetry; apply Z.eqb_neq; lia).
            cbn [orb]. rewrite <- (F8lt i) by lia. rewrite Bool.negb_true_iff, Z.eqb_neq. tauto.
    Qed.

    Lemma BV_loop : forall u s, BV s -> BV (fs_bucket_loop u nb s).
    Proof.
      induction u as [|u IH]; intros s V; [exact V|]. rewrite fs_bucket_loop_S.
      destruct (fb_done s) eqn:Hd; [exact V|]. apply IH. apply BV_step; [exact Hd|exact V].
    Qed.

    (* [comment removed for export] *)
    Lemma BV_final : forall s, BV s -> fb_done s = true ->
      INV H2 (fb_fm s) (fb_bh s) /\ (fb_nnd s = 0 -> forall i, 0 <= i < nb -> isset_bh (fb_bh s) i = true).
    Proof.
      intros [fm ec bh slo shi r nnd dn] V Hd. cbn [fb_done] in Hd. subst dn.
      cps_destruct V as (Eec & PM & SE & B0 & Hr & Hnnd & Hnnd0 & _ & G & B & E & EB & D & C).
      cbn [fb_ec fb_fm fb_bh fb_r fb_nnd fb_done] in *. specialize (G eq_refl).
      assert (G0 : forall m, r < m < nb -> isset_bh bh0 m = true) by (intros m Hm; rewrite <- EB by lia; apply G; lia).
      split.
      - split; [exact PM|]. split; [exact SE|]. split; [exact B0|]. split.
        + intros i j Hi Hij Hj. destruct (Z.eq_dec i j) as [->|NE]; [apply lexle_refl|].
          destruct (Z.le_gt_cases j r) as [JR|JR]; [apply D; lia|]. left.
          destruct (Z.le_gt_cases i r) as [IR|IR].
          * apply (strict_across fm i j (r + 1)); try lia; [exact B|]. apply G0. lia.
          * apply (strict_across fm i j (i + 1)); try lia; [exact B|]. apply G0. lia.
        + intros i Hi. destruct (Z.le_gt_cases i r) as [IR|IR]; [apply C; lia|].
          rewrite (G i) by lia. split; [intros _|reflexivity].
          apply (strict_across fm (i - 1) i i); try lia; [exact B|]. apply G0. lia.
      - intros Hn i Hi. apply G. specialize (Hnnd0 Hn). lia.
    Qed.

    (* [comment removed for export] *)
    Theorem round_ok : forall slo shi,
      let b := fs_bucket_loop (Z.to_nat (nb + 2)) nb (FBS fm0 ec1 bh0 slo shi (-1) 0 false) in
      INV H2 (fb_fm b) (fb_bh b) /\ (fb_nnd b = 0 -> forall i, 0 <= i < nb -> isset_bh (fb_bh b) i = true).
    Proof.
      intros slo shi. cbv zeta. set (s0 := FBS fm0 ec1 bh0 slo shi (-1) 0 false).
      apply BV_final; [apply BV_loop; apply BV_init|].
      cps_pose IV as (PM0 & SE0 & B00 & _ & _).
      assert (BI0 : BI nb s0). { split; [split; [exact PM0|split; [exact SE0|exact B00]]|]. cbn. intros _. split; [lia|exact B00]. }
      apply fs_bucket_loop_term; [lia|reflexivity|reflexivity|].
      intros v Hv. apply (BI_bucket_ok nb NB); [apply (BI_loop nb NB); exact BI0|exact Hv].
    Qed.
  End Round.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition allset (bh : zarr) : Prop := forall i, 0 <= i < nb -> isset_bh bh i = true.

  Definition HV (h : fhs) : Prop :=
    exists Hn : nat, fh_H h = Z.of_nat Hn /\ (1 <= Hn)%nat /\ INV Hn (fh_fm h) (fh_bh h) /\
      (fh_done h = false -> fh_H h <= nb) /\
      (fh_done h = true -> nb < fh_H h \/ allset (fh_bh h)).

  Lemma HV_step : forall h, fh_done h = false -> HV h -> HV (fs_H_iter nb h) /\ fh_H (fs_H_iter nb h) = 2 * fh_H h.
  Proof.
    (intros [fm ec bh slo shi HZ dn] Hd; cps_intros (Hn & EH & H1 & IV & LE & _)). cbn [fh_H fh_fm fh_bh fh_done] in *. subst dn.
    specialize (LE eq_refl). unfold fs_H_iter. cbn [fh_ec fh_fm fh_bh fh_H fh_slo fh_shi].
    pose proof (round_ok HZ Hn fm bh ec EH ltac:(lia) IV slo shi) as RO. cbv zeta in RO.
    set (b := fs_bucket_loop _ nb _) in *. destruct RO as [IV2 NND].
    split; [|cbn [fh_H]; lia].
    exists (Hn + Hn)%nat. cbn [fh_H fh_fm fh_bh fh_done]. split; [lia|]. split; [lia|]. split; [exact IV2|]. split.
    - intros X. apply Bool.orb_false_iff in X. destruct X as [X _]. apply Z.ltb_ge in X. lia.
    - intros X. apply Bool.orb_true_iff in X. destruct X as [X|X].
      + left. apply Z.ltb_lt in X. lia.
      + right. intros i Hi. apply Z.eqb_eq in X. exact (NND X i Hi).
  Qed.

  Lemma HV_loop : forall f h, HV h -> HV (fs_H_loop f nb h) /\ (fh_done (fs_H_loop f nb h) = true \/ fh_H (fs_H_loop f nb h) = fh_H h * 2 ^ Z.of_nat f).
  Proof.
    induction f as [|f IH]; intros h V.
    - cbn [fs_H_loop]. split; [exact V|]. right. rewrite Z.pow_0_r. lia.
    - rewrite fs_H_loop_S. destruct (fh_done h) eqn:Hd; [split; [exact V|left; exact Hd]|].
      destruct (HV_step h Hd V) as [V1 E1]. destruct (IH _ V1) as [V2 E2]. split; [exact V2|].
      destruct E2 as [E2|E2]; [left; exact E2|right]. rewrite E2, E1. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition rows_sorted (fm : zarr) : Prop :=
    forall i j, 0 <= i -> i <= j -> j < nb -> lexle (rot t (Z.to_nat (rd32 fm i))) (rot t (Z.to_nat (rd32 fm j))).

  Lemma INV_exit_sorted : forall Hn fm bh, INV Hn fm bh -> (nb < Z.of_nat Hn \/ allset bh) -> rows_sorted fm.
  Proof.
    intros Hn fm bh IV X i j Hi Hij Hj. cps_pose IV as (PM & _ & _ & I2 & I3).
    pose proof (proj1 PM i ltac:(lia)) as Ri. pose proof (proj1 PM j ltac:(lia)) as Rj.
    destruct X as [X|X].
    - apply (pre_le_rot t Hn0 Hn); [unfold nb, n in *; lia|exact Ri|exact Rj|]. apply I2; lia.
    - destruct (Z.eq_dec i j) as [->|NE]; [apply lexle_refl|].
      apply (pre_lt_rot t Hn0 Hn); [exact Ri|exact Rj|]. apply (set_lt Hn fm bh IV i j j); try lia. apply X. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Phase1.
    Variables (fm ec bh : zarr).
    Hypothesis ECB : zbok ec.
    Hypothesis BW : bh_w32 bh.
    Hypothesis TEC : forall p, 0 <= p < nb -> nth (Z.to_nat p) t 0 = rd8 ec p.
    Let fm1 := fp_fm1 fm ec nb.
    Let bh3 := fp_bh3 fm ec bh nb.

    Lemma Kp_row : forall i, 0 <= i < nb -> Kp ec nb (rd32 fm1 i) = i.
    Proof.
      intros i Hi. pose proof (fp_fm1_perm ec nb ECB ltac:(lia) fm ltac:(lia)) as PM. fold fm1 in PM.
      pose proof (proj1 PM i Hi) as R. pose proof (Kp_range ec nb ltac:(lia) (rd32 fm1 i) R) as KR.
      apply (proj2 PM); [exact KR|exact Hi|]. apply fp_fm1_Kp; [exact ECB|lia|exact R].
    Qed.

    Lemma ch0_e8 : forall i, 0 <= i < nb -> ch t (rd32 fm1 i) 0 = rd8 ec (rd32 fm1 i).
    Proof.
      intros i Hi. pose proof (proj1 (fp_fm1_perm ec nb ECB ltac:(lia) fm ltac:(lia)) i Hi) as R. fold fm1 in R.
      rewrite ch_0 by (exact Hn0 || (unfold nb, n in *; lia)). apply TEC. exact R.
    Qed.

    Theorem INV_1 : INV 1 fm1 bh3.
    Proof.
      pose proof (fp_fm1_perm ec nb ECB ltac:(lia) fm ltac:(lia)) as PM. fold fm1 in PM.
      assert (BW2 : bh_w32 (fs_bh_init 256 (fs_bh_zero (Z.to_nat (fp_nB nb)) bh 0) (fp_ft4 fm ec nb) 0)) by (apply fs_bh_init_w32, fs_bh_zero_w32; exact BW).
      pose proof (fsf_ft4_ok ec nb ECB ltac:(lia) fm ltac:(lia)) as FT4. unfold fsf_ft4 in FT4.
      assert (BITS : forall i, 0 <= i < nb -> isset_bh bh3 i = true <-> exists b, 0 <= b < 256 /\ Cl ec nb b = i).
      { intros i Hi. unfold bh3, fp_bh3. rewrite fs_sentinel_low by (try lia; exact BW2).
        rewrite isset_fs_bh_init_iff; [|lia|intros b Hb; pose proof (FT4 b ltac:(lia)); lia].
        rewrite isset_fs_bh_zero by (unfold fp_nB; Z.div_mod_to_equations; lia).
        split.
        - intros [X|(b & Hb & E)]; [discriminate|]. exists b. split; [lia|]. rewrite <- (fp_ft4_count ec nb ECB fm ltac:(lia) b ltac:(lia)). exact E.
        - cps_intros (b & Hb & E). right. exists b. split; [lia|]. rewrite fp_ft4_count by (exact ECB || lia). exact E. }
      assert (KB : forall i, 0 <= i < nb -> Cl ec nb (rd8 ec (rd32 fm1 i)) <= i < Cl ec nb (rd8 ec (rd32 fm1 i) + 1)).
      { intros i Hi. pose proof (Kp_bucket ec nb (rd32 fm1 i) (proj1 PM i Hi)) as KBi. rewrite Kp_row in KBi by exact Hi. exact KBi. }
      split; [exact PM|]. split; [unfold bh3, fp_bh3; apply sent_init; [lia|exact BW2]|]. split.
      { apply BITS; [lia|]. exists 0. split; [lia|]. apply Cl_0. exact ECB. }
      split.
      - intros i j Hi Hij Hj. apply (proj2 (pre1_le t Hn0 _ _)). rewrite !ch0_e8 by lia.
        destruct (Z.le_gt_cases (rd8 ec (rd32 fm1 i)) (rd8 ec (rd32 fm1 j))) as [LE|GT]; [exact LE|exfalso].
        pose proof (KB i ltac:(lia)) as [A _]. pose proof (KB j ltac:(lia)) as [_ D].
        pose proof (Cl_mono ec nb (rd8 ec (rd32 fm1 j) + 1) (rd8 ec (rd32 fm1 i)) ltac:(lia)). lia.
      - intros i Hi. rewrite BITS by lia. rewrite pre1_lt. rewrite !ch0_e8 by lia.
        set (c := rd8 ec (rd32 fm1 i)). set (c' := rd8 ec (rd32 fm1 (i - 1))).
        pose proof (KB i ltac:(lia)) as [A D]. pose proof (KB (i - 1) ltac:(lia)) as [A' D']. fold c in A, D. fold c' in A', D'.
        split.
        + cps_intros (b & Hb & E). destruct (Z.lt_ge_cases c' c) as [X|X]; [exact X|exfalso].
          destruct (Z.le_gt_cases b c) as [Y|Y].
          * pose proof (Cl_mono ec nb b c Y). pose proof (Cl_mono ec nb c c' X). lia.
          * pose proof (Cl_mono ec nb (c + 1) b ltac:(lia)). lia.
        + intros X. exists c. pose proof (Cl_mono ec nb (c' + 1) c ltac:(lia)).
          split; [|lia]. pose proof (ECB (rd32 fm1 i)). unfold rd8 in c. subst c. lia.
    Qed.
  End Phase1.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem fs_rows_sorted : forall fm ec bh, zbok ec -> bh_w32 bh ->
    (forall p, 0 <= p < nb -> nth (Z.to_nat p) t 0 = rd8 ec p) ->
    let h := fp_hsF fm ec bh nb in fm_perm (fh_fm h) nb /\ rows_sorted (fh_fm h).
  Proof.
    intros fm ec bh ECB BW TEC. cbv zeta. unfold fp_hsF.
    assert (V0 : HV (fp_hs0 fm ec bh nb)).
    { exists 1%nat. unfold fp_hs0. cbn [fh_H fh_fm fh_bh fh_done]. split; [reflexivity|]. split; [lia|].
      split; [apply INV_1; assumption|]. split; [intros; lia|intros; discriminate]. }
    destruct (HV_loop (Z.to_nat 64) _ V0) as [(Hn & EH & H1 & IV & LE & EX) TERM].
    split; [exact (proj1 IV)|].
    apply (INV_exit_sorted Hn _ _ IV).
    destruct TERM as [D|E]; [rewrite <- EH; apply EX; exact D|]. left. rewrite <- EH, E. unfold fp_hs0. cbn [fh_H].
    replace (Z.of_nat (Z.to_nat 64)) with 64 by lia. change (1 * 2 ^ 64) with 18446744073709551616. lia.
  Qed.
End FS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition block_of (ec : zarr) (nb : Z) : list Z := map (fun i => rd8 ec (Z.of_nat i)) (seq 0 (Z.to_nat nb)).

Lemma block_of_length : forall ec nb, length (block_of ec nb) = Z.to_nat nb.
Proof. intros. unfold block_of. rewrite length_map, length_seq. reflexivity. Qed.
Lemma block_of_nth : forall ec nb p, 0 <= p < nb -> nth (Z.to_nat p) (block_of ec nb) 0 = rd8 ec p.
Proof.
  intros ec nb p Hp. unfold block_of. rewrite (nth_map_seq _ _ 0) by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma fallbackSort_fm : forall fm ec bh nb,
  fr_fm (fallbackSort fm ec bh znew znew znew znew nb) = fh_fm (fp_hsF fm ec bh nb).
Proof.
  intros. unfold fallbackSort, fp_hsF, fp_hs0, fp_bh3, fp_fm1, fp_ft4, fp_dist, fp_ft3, fp_ft2, fp_ft1, fp_nB.
  destruct (fs_distrib (Z.to_nat nb) (fs_accum 256 (fs_count (Z.to_nat nb) (fs_ftab_zero 257 znew 0) ec 0) 1) fm ec 0) as [ft fm'] eqn:E.
  cbn [fst snd]. destruct (fs_rebuild _ _ _ _ _ _) as [[ec' fc'] j]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section PiRho.
  Variables (fm : zarr) (nb : Z).
  Hypothesis PM : fm_perm fm nb.
  Let n := Z.to_nat nb.

  Definition perm_pi (i : nat) : nat := Z.to_nat (rd32 fm (Z.of_nat i)).
  Definition perm_rho (p : nat) : nat :=
    match find (fun i => rd32 fm (Z.of_nat i) =? Z.of_nat p) (seq 0 n) with Some i => i | None => O end.

  Lemma perm_pi_lt : forall i, (i < n)%nat -> (perm_pi i < n)%nat.
  Proof. intros i Hi. unfold perm_pi. pose proof (proj1 PM (Z.of_nat i) ltac:(lia)). lia. Qed.

  Lemma perm_rho_spec : forall p, (p < n)%nat -> (perm_rho p < n)%nat /\ rd32 fm (Z.of_nat (perm_rho p)) = Z.of_nat p.
  Proof.
    intros p Hp. unfold perm_rho.
    destruct (find (fun i => rd32 fm (Z.of_nat i) =? Z.of_nat p) (seq 0 n)) as [i|] eqn:F.
    - apply find_some in F. destruct F as [IN E]. apply in_seq in IN. apply Z.eqb_eq in E. split; [lia|exact E].
    - exfalso. cps_destruct (fm_perm_onto fm nb PM (Z.of_nat p) ltac:(lia)) as (x & Hx & Ex).
      pose proof (find_none _ _ F (Z.to_nat x) ltac:(apply in_seq; lia)) as C. cbn beta in C.
      rewrite Z2Nat.id in C by lia. rewrite Ex, Z.eqb_refl in C. discriminate.
  Qed.

  Lemma perm_rho_lt : forall p, (p < n)%nat -> (perm_rho p < n)%nat.
  Proof. intros p Hp. apply perm_rho_spec. exact Hp. Qed.
  Lemma perm_pi_rho : forall p, (p < n)%nat -> perm_pi (perm_rho p) = p.
  Proof. intros p Hp. unfold perm_pi. rewrite (proj2 (perm_rho_spec p Hp)). lia. Qed.
  Lemma perm_rho_pi : forall i, (i < n)%nat -> perm_rho (perm_pi i) = i.
  Proof.
    intros i Hi. pose proof (perm_pi_lt i Hi) as L. destruct (perm_rho_spec (perm_pi i) L) as [A B].
    unfold perm_pi in B. rewrite Z2Nat.id in B by (pose proof (proj1 PM (Z.of_nat i) ltac:(lia)); lia).
    apply Nat2Z.inj. apply (proj2 PM); [lia|lia|exact B].
  Qed.
End PiRho.

(* [comment removed for export] *)
(* [comment removed for export] *)
