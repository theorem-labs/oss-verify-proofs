(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCSortF BzCLemmasFs BzCFactsFs BzCFactsFs2 BzCPermF BzCPermF2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCPermF2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCRebuildF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2.BzCQsortF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_pow2_bit' : forall w k, 0 <= k -> Z.land w (Z.shiftl 1 k) = if Z.testbit w k then Z.shiftl 1 k else 0.
Proof.
  intros w k Hk. rewrite Z.shiftl_1_l. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.testbit w k) eqn:E.
  - rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec k n); [subst; rewrite E; reflexivity| apply Bool.andb_false_r].
  - rewrite Z.bits_0. destruct (Z.eqb_spec k n); [subst; rewrite E; reflexivity| apply Bool.andb_false_r].
Qed.

Lemma isset_tb : forall bh i, 0 <= i -> isset_bh bh i = Z.testbit (zget bh (i / 32)) (i mod 32).
Proof.
  intros bh i Hi. unfold isset_bh, bh_word. rewrite shiftr5_div, land31_mod.
  pose proof (Z.mod_pos_bound i 32 ltac:(lia)) as Hm.
  rewrite land_pow2_bit' by lia.
  destruct (Z.testbit (zget bh (i / 32)) (i mod 32)).
  - destruct (Z.eqb_spec (Z.shiftl 1 (i mod 32)) 0) as [E|]; [|reflexivity].
    exfalso. rewrite Z.shiftl_1_l in E. pose proof (Z.pow_pos_nonneg 2 (i mod 32) ltac:(lia) ltac:(lia)). lia.
  - rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma divmod32_eq : forall i k, 0 <= i -> 0 <= k -> (k = i <-> k / 32 = i / 32 /\ k mod 32 = i mod 32).
Proof. intros i k Hi Hk. split; [intros ->; split; reflexivity|]. intros [A B]. rewrite (Z.div_mod k 32), (Z.div_mod i 32) by lia. lia. Qed.

Lemma isset_set_bh : forall bh i k, 0 <= i -> 0 <= k -> isset_bh (set_bh bh i) k = ((k =? i) || isset_bh bh k)%bool.
Proof.
  intros bh i k Hi Hk. rewrite !isset_tb by lia. unfold set_bh, bh_word. rewrite shiftr5_div, land31_mod, zget_zset.
  pose proof (Z.mod_pos_bound i 32 ltac:(lia)). pose proof (Z.mod_pos_bound k 32 ltac:(lia)).
  destruct (Z.eqb_spec (k / 32) (i / 32)) as [E|E].
  - rewrite Z.lor_spec, Z.shiftl_1_l, Z.pow2_bits_eqb by lia. rewrite E.
    destruct (Z.eqb_spec k i) as [->|N].
    + rewrite Z.eqb_refl. rewrite Bool.orb_true_r. reflexivity.
    + destruct (Z.eqb_spec (i mod 32) (k mod 32)) as [E2|E2]; [exfalso; apply N; apply (proj2 (divmod32_eq i k Hi Hk)); split; [exact E| symmetry; exact E2]|].
      rewrite Bool.orb_false_r. reflexivity.
  - destruct (Z.eqb_spec k i) as [->|N]; [exfalso; apply E; reflexivity|]. reflexivity.
Qed.

Lemma isset_clear_bh : forall bh i k, 0 <= i -> 0 <= k -> 0 <= zget bh (i / 32) < 4294967296 ->
  isset_bh (clear_bh bh i) k = (negb (k =? i) && isset_bh bh k)%bool.
Proof.
  intros bh i k Hi Hk Hw. rewrite !isset_tb by lia. unfold clear_bh, bh_word. rewrite shiftr5_div, land31_mod, zget_zset.
  pose proof (Z.mod_pos_bound i 32 ltac:(lia)). pose proof (Z.mod_pos_bound k 32 ltac:(lia)).
  destruct (Z.eqb_spec (k / 32) (i / 32)) as [E|E].
  - rewrite Z.land_spec, Z.lxor_spec, Z.shiftl_1_l, Z.pow2_bits_eqb by lia. rewrite E.
    replace (Z.testbit 4294967295 (k mod 32)) with true by (symmetry; change 4294967295 with (Z.ones 32); apply Z.ones_spec_low; lia).
    destruct (Z.eqb_spec k i) as [->|N].
    + rewrite Z.eqb_refl. cbn. rewrite Bool.andb_false_r. reflexivity.
    + destruct (Z.eqb_spec (i mod 32) (k mod 32)) as [E2|E2]; [exfalso; apply N; apply (proj2 (divmod32_eq i k Hi Hk)); split; [exact E| symmetry; exact E2]|].
      destruct (Z.eqb_spec (i mod 32) (k mod 32)); [lia|]. cbn. rewrite Bool.andb_true_r. reflexivity.
  - destruct (Z.eqb_spec k i) as [->|N]; [exfalso; apply E; reflexivity|]. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma isset_fs_headers_mono : forall n bh ec fm i cc k, 0 <= i -> 0 <= k ->
  isset_bh bh k = true -> isset_bh (fs_headers n bh ec fm i cc) k = true.
Proof.
  induction n as [|n IH]; intros bh ec fm i cc k Hi Hk H; [exact H|].
  rewrite fs_headers_S. cbv zeta. destruct (negb _).
  - apply IH; [lia| lia|]. rewrite isset_set_bh by lia. rewrite H. apply Bool.orb_true_r.
  - apply IH; [lia| lia| exact H].
Qed.
Lemma isset_fs_headers_out : forall n bh ec fm i cc k, 0 <= i -> 0 <= k -> (k < i \/ i + Z.of_nat n <= k) ->
  isset_bh (fs_headers n bh ec fm i cc) k = isset_bh bh k.
Proof.
  induction n as [|n IH]; intros bh ec fm i cc k Hi Hk H; [reflexivity|].
  rewrite fs_headers_S. cbv zeta. destruct (negb _).
  - rewrite IH by lia. rewrite isset_set_bh by lia. destruct (Z.eqb_spec k i); [lia| reflexivity].
  - rewrite IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sent (bh : zarr) (nb : Z) : Prop :=
  forall i, 0 <= i < 32 -> isset_bh bh (nb + 2 * i) = true /\ isset_bh bh (nb + 2 * i + 1) = false.

(* [comment removed for export] *)
Lemma sent_fs_headers : forall n bh ec fm i cc nb, 0 <= nb -> 0 <= i -> i + Z.of_nat n <= nb -> sent bh nb -> sent (fs_headers n bh ec fm i cc) nb.
Proof.
  intros n bh ec fm i cc nb Hnb Hi Hn S j Hj. rewrite !isset_fs_headers_out by lia. apply S. exact Hj.
Qed.

(* [comment removed for export] *)
Lemma fs_sentinel_bits : forall n bh nb i k, 0 <= nb -> 0 <= i -> 0 <= k -> bh_w32 bh ->
  isset_bh (fs_sentinel n bh nb i) k =
    if (nb + 2 * i <=? k) && (k <? nb + 2 * (i + Z.of_nat n)) then Z.even (k - nb) else isset_bh bh k.
Proof.
  induction n as [|n IH]; intros bh nb i k Hnb Hi Hk BW.
  - cbn [fs_sentinel]. replace (_ && _)%bool with false; [reflexivity|]. symmetry. apply Bool.andb_false_iff.
    destruct (Z.leb_spec (nb + 2 * i) k); [right; apply Z.ltb_ge; lia| left; reflexivity].
  - rewrite fs_sentinel_S. rewrite IH by (try lia; apply clear_bh_w32, set_bh_w32; exact BW).
    rewrite isset_clear_bh by (try lia; apply set_bh_w32; exact BW). rewrite isset_set_bh by lia.
    destruct (Z.leb_spec (nb + 2 * (i + 1)) k); destruct (Z.ltb_spec k (nb + 2 * (i + 1 + Z.of_nat n)));
      destruct (Z.leb_spec (nb + 2 * i) k); destruct (Z.ltb_spec k (nb + 2 * (i + Z.of_nat (S n)))); cbn [andb]; try lia; try reflexivity.
    + destruct (Z.eqb_spec k (nb + 2 * i + 1)); [lia|]. destruct (Z.eqb_spec k (nb + 2 * i)); [lia|]. reflexivity.
    + destruct (Z.eqb_spec k (nb + 2 * i + 1)) as [->|N1].
      { cbn [negb andb]. destruct (Z.even _) eqn:Ev; [exfalso; apply Z.even_spec in Ev; destruct Ev as [m Hm]; lia| reflexivity]. }
      destruct (Z.eqb_spec k (nb + 2 * i)) as [->|N2].
      { cbn [negb andb orb]. symmetry. apply Z.even_spec. exists i. lia. }
      exfalso. lia.
    + destruct (Z.eqb_spec k (nb + 2 * i + 1)); [lia|]. destruct (Z.eqb_spec k (nb + 2 * i)); [lia|]. reflexivity.
Qed.

Lemma sent_init : forall bh nb, 0 <= nb -> bh_w32 bh -> sent (fs_sentinel 32 bh nb 0) nb.
Proof.
  intros bh nb Hnb BW i Hi. rewrite !fs_sentinel_bits by (try lia; exact BW).
  replace ((nb + 2 * 0 <=? nb + 2 * i) && (nb + 2 * i <? nb + 2 * (0 + Z.of_nat 32)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  replace ((nb + 2 * 0 <=? nb + 2 * i + 1) && (nb + 2 * i + 1 <? nb + 2 * (0 + Z.of_nat 32)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  split.
  - apply Z.even_spec. exists i. lia.
  - destruct (Z.even _) eqn:Ev; [exfalso; apply Z.even_spec in Ev; destruct Ev as [m Hm]; lia| reflexivity].
Qed.
(* [comment removed for export] *)
Lemma fs_sentinel_low : forall bh nb k, 0 <= nb -> 0 <= k < nb -> bh_w32 bh -> isset_bh (fs_sentinel 32 bh nb 0) k = isset_bh bh k.
Proof.
  intros bh nb k Hnb Hk BW. rewrite fs_sentinel_bits by (try lia; exact BW).
  replace (_ && _)%bool with false; [reflexivity|]. symmetry. apply Bool.andb_false_iff. left. apply Z.leb_gt. lia.
Qed.
Lemma isset_fs_bh_init_mono : forall n bh ft i k, 0 <= k -> (forall b, i <= b < i + Z.of_nat n -> 0 <= zget ft b) -> isset_bh bh k = true -> isset_bh (fs_bh_init n bh ft i) k = true.
Proof.
  induction n as [|n IH]; intros bh ft i k Hk Hft H; [exact H|].
  rewrite fs_bh_init_S. apply IH; [lia| intros b Hb; apply Hft; lia|]. rewrite isset_set_bh by (try lia; apply Hft; lia). rewrite H. apply Bool.orb_true_r.
Qed.
Lemma isset_fs_bh_init_at : forall n bh ft i b, (forall b, i <= b < i + Z.of_nat n -> 0 <= zget ft b) -> i <= b < i + Z.of_nat n -> isset_bh (fs_bh_init n bh ft i) (zget ft b) = true.
Proof.
  induction n as [|n IH]; intros bh ft i b Hft Hb; [lia|].
  rewrite fs_bh_init_S. destruct (Z.eq_dec b i) as [->|N].
  - apply isset_fs_bh_init_mono; [apply Hft; lia| intros b Hb'; apply Hft; lia|]. rewrite isset_set_bh by (apply Hft; lia). rewrite Z.eqb_refl. reflexivity.
  - apply IH; [intros b' Hb'; apply Hft; lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Scan.
  Variable c : Z -> bool. Variable s : Z. Variable scan : nat -> Z -> Z.
  Hypothesis scan_0 : forall k, scan O k = k.
  Hypothesis scan_S : forall f k, scan (S f) k = if c k then scan f (k + s) else k.

  Lemma scan_first : forall f j k, (j <= f)%nat -> c (k + s * Z.of_nat j) = false ->
    (forall j', (j' < j)%nat -> c (k + s * Z.of_nat j') = true) -> scan f k = k + s * Z.of_nat j.
  Proof.
    induction f as [|f IH]; intros j k Hj Hc Hall.
    - assert (j = 0)%nat by lia. subst j. rewrite scan_0. lia.
    - rewrite scan_S. destruct j as [|j].
      + replace (k + s * Z.of_nat 0) with k in Hc by lia. rewrite Hc. lia.
      + pose proof (Hall 0%nat ltac:(lia)) as H0. replace (k + s * Z.of_nat 0) with k in H0 by lia. rewrite H0.
        rewrite (IH j (k + s)); [lia| lia| replace (k + s + s * Z.of_nat j) with (k + s * Z.of_nat (S j)) by lia; exact Hc|].
        intros j' Hj'. replace (k + s + s * Z.of_nat j') with (k + s * Z.of_nat (S j')) by lia. apply Hall. lia.
  Qed.

  Lemma first_failure : forall (n : nat) k, c (k + s * Z.of_nat n) = false ->
    exists j, (j <= n)%nat /\ c (k + s * Z.of_nat j) = false /\ forall j', (j' < j)%nat -> c (k + s * Z.of_nat j') = true.
  Proof.
    induction n as [|n IH]; intros k Hc.
    - exists 0%nat. split; [lia|]. split; [exact Hc| intros; lia].
    - destruct (c k) eqn:Ck.
      + cps_destruct (IH (k + s)) as (j & Hj & Hcj & Hall); [replace (k + s + s * Z.of_nat n) with (k + s * Z.of_nat (S n)) by lia; exact Hc|].
        exists (S j). split; [lia|]. split; [replace (k + s * Z.of_nat (S j)) with (k + s + s * Z.of_nat j) by lia; exact Hcj|].
        intros j' Hj'. destruct j' as [|j']; [replace (k + s * Z.of_nat 0) with k by lia; exact Ck|].
        replace (k + s * Z.of_nat (S j')) with (k + s + s * Z.of_nat j') by lia. apply Hall. lia.
      + exists 0%nat. split; [lia|]. split; [replace (k + s * Z.of_nat 0) with k by lia; exact Ck| intros; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma scan_spec : forall f (n : nat) k, (n <= f)%nat -> c (k + s * Z.of_nat n) = false ->
    exists j, (j <= n)%nat /\ scan f k = k + s * Z.of_nat j /\ c (k + s * Z.of_nat j) = false /\ forall j', (j' < j)%nat -> c (k + s * Z.of_nat j') = true.
  Proof.
    intros f n k Hn Hc. cps_destruct (first_failure n k Hc) as (j & Hj & Hcj & Hall).
    exists j. split; [exact Hj|]. split; [apply scan_first; [lia| exact Hcj| exact Hall]|]. split; [exact Hcj| exact Hall].
  Qed.
End Scan.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma word_not_ones : forall bh q b, 0 <= q -> q mod 32 = 0 -> q <= b <= q + 31 -> isset_bh bh b = false ->
  (bh_word bh q =? 4294967295) = false.
Proof.
  intros bh q b Hq Ha Hb Hc. rewrite isset_tb in Hc by lia. unfold bh_word. rewrite shiftr5_div.
  replace (b / 32) with (q / 32) in Hc by (Z.div_mod_to_equations; lia).
  apply Z.eqb_neq. intros E. rewrite E in Hc. change 4294967295 with (Z.ones 32) in Hc.
  rewrite Z.ones_spec_low in Hc by (pose proof (Z.mod_pos_bound b 32 ltac:(lia)); lia). discriminate.
Qed.
Lemma word_not_zero : forall bh q b, 0 <= q -> q mod 32 = 0 -> q <= b <= q + 31 -> isset_bh bh b = true ->
  (bh_word bh q =? 0) = false.
Proof.
  intros bh q b Hq Ha Hb Hc. rewrite isset_tb in Hc by lia. unfold bh_word. rewrite shiftr5_div.
  replace (b / 32) with (q / 32) in Hc by (Z.div_mod_to_equations; lia).
  apply Z.eqb_neq. intros E. rewrite E in Hc. rewrite Z.bits_0 in Hc. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Six.
  Variables (bh : zarr) (nb : Z).
  Hypothesis NB : 1 <= nb.
  Hypothesis SENT : sent bh nb.
  Let F := FSC nb.
  Let LF : (Z.to_nat (nb + 70) = F)%nat. Proof. reflexivity. Qed.

  Lemma sent_odd : forall i, 0 <= i < 32 -> isset_bh bh (nb + 2 * i + 1) = false.
  Proof. intros i Hi. exact (proj2 (SENT i Hi)). Qed.
  Lemma sent_even : forall i, 0 <= i < 32 -> isset_bh bh (nb + 2 * i) = true.
  Proof. intros i Hi. exact (proj1 (SENT i Hi)). Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma scanA_ok : forall k, 0 <= k -> k <= nb ->
    let kA := fs_scan_set_unal F bh k in
    k <= kA <= k + 31 /\ isset_bh bh kA && unaligned_bh kA = false /\ (forall x, k <= x < kA -> isset_bh bh x = true).
  Proof.
    intros k Hk Hkn. cbv zeta.
    set (d := (32 - k mod 32) mod 32). pose proof (Z.mod_pos_bound k 32 ltac:(lia)) as Hm.
    assert (Hd : 0 <= d <= 31) by (subst d; Z.div_mod_to_equations; lia).
    assert (Ha : (k + d) mod 32 = 0) by (subst d; Z.div_mod_to_equations; lia).
    cps_destruct (scan_spec (fun x => isset_bh bh x && unaligned_bh x) 1 (fun f x => fs_scan_set_unal f bh x)
                ltac:(reflexivity) ltac:(intros; apply fs_scan_set_unal_S) F (Z.to_nat d) k ltac:(unfold F, FSC; lia)) as (j & Hj & E & Hc & Hall).
    { replace (k + 1 * Z.of_nat (Z.to_nat d)) with (k + d) by lia. rewrite unaligned_bh_mod, Ha. cbn. apply Bool.andb_false_r. }
    rewrite E. split; [lia|]. split; [exact Hc|].
    intros x Hx. specialize (Hall (Z.to_nat (x - k)) ltac:(lia)). replace (k + 1 * Z.of_nat (Z.to_nat (x - k))) with x in Hall by lia.
    apply Bool.andb_true_iff in Hall. exact (proj1 Hall).
  Qed.

  (* [comment removed for export] *)
  Lemma scanB_ok : forall k, 0 <= k <= nb + 31 -> k mod 32 = 0 ->
    let kB := fs_scan_word_ff F bh k in
    k <= kB <= nb + 31 /\ (bh_word bh kB =? 4294967295) = false /\ kB mod 32 = 0.
  Proof.
    intros k Hk Ha. cbv zeta.
    set (q0 := 32 * ((nb + 1) / 32)). assert (Hq0 : nb - 30 <= q0 <= nb + 1 /\ q0 mod 32 = 0) by (subst q0; Z.div_mod_to_equations; lia).
    destruct (Z_le_gt_dec k q0) as [LE|GT].
    - assert (Hn : exists n, q0 = k + 32 * Z.of_nat n) by (exists (Z.to_nat ((q0 - k) / 32)); Z.div_mod_to_equations; lia).
      destruct Hn as [n Hn].
      cps_destruct (scan_spec (fun x => bh_word bh x =? 4294967295) 32 (fun f x => fs_scan_word_ff f bh x)
                  ltac:(reflexivity) ltac:(intros; apply fs_scan_word_ff_S) F n k ltac:(unfold F, FSC; lia)) as (j & Hj & E & Hc & Hall).
      { rewrite <- Hn. apply (word_not_ones bh q0 (nb + 1)); [lia| lia| lia|]. replace (nb + 1) with (nb + 2 * 0 + 1) by lia. apply sent_odd. lia. }
      rewrite E. split; [lia|]. split; [exact Hc|]. Z.div_mod_to_equations. lia.
    - assert (Hk2 : nb + 2 <= k) by (Z.div_mod_to_equations; lia).
      cps_destruct (scan_spec (fun x => bh_word bh x =? 4294967295) 32 (fun f x => fs_scan_word_ff f bh x)
                  ltac:(reflexivity) ltac:(intros; apply fs_scan_word_ff_S) F 0%nat k ltac:(lia)) as (j & Hj & E & Hc & Hall).
      { replace (k + 32 * Z.of_nat 0) with k by lia.
        apply (word_not_ones bh k (nb + 2 * ((k - nb) / 2) + 1)); [lia| lia| Z.div_mod_to_equations; lia|]. apply sent_odd. Z.div_mod_to_equations; lia. }
      assert (j = 0)%nat by lia. subst j. rewrite E. replace (k + 32 * Z.of_nat 0) with k in Hc |- * by lia. split; [lia|]. split; [exact Hc| exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma scanC_ok : forall k, 0 <= k <= nb + 31 ->
    let kC := fs_scan_set F bh k in
    k <= kC <= nb + 32 /\ isset_bh bh kC = false /\ (forall x, k <= x < kC -> isset_bh bh x = true).
  Proof.
    intros k Hk. cbv zeta.
    assert (Hb : exists b, k <= b <= nb + 32 /\ b <= k + nb + 1 /\ isset_bh bh b = false).
    { destruct (Z_le_gt_dec k (nb + 1)) as [LE|GT].
      - exists (nb + 1). split; [lia|]. split; [lia|]. replace (nb + 1) with (nb + 2 * 0 + 1) by lia. apply sent_odd. lia.
      - exists (nb + 2 * ((k - nb) / 2) + 1). split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|]. apply sent_odd. Z.div_mod_to_equations; lia. }
    cps_destruct Hb as (b & Hb1 & Hb2 & Hb3).
    cps_destruct (scan_spec (fun x => isset_bh bh x) 1 (fun f x => fs_scan_set f bh x)
                ltac:(reflexivity) ltac:(intros; apply fs_scan_set_S) F (Z.to_nat (b - k)) k ltac:(unfold F, FSC; lia)) as (j & Hj & E & Hc & Hall).
    { replace (k + 1 * Z.of_nat (Z.to_nat (b - k))) with b by lia. exact Hb3. }
    rewrite E. split; [lia|]. split; [exact Hc|].
    intros x Hx. specialize (Hall (Z.to_nat (x - k)) ltac:(lia)). replace (k + 1 * Z.of_nat (Z.to_nat (x - k))) with x in Hall by lia. exact Hall.
  Qed.

  (* [comment removed for export] *)
  Lemma scanD_ok : forall k, 0 <= k -> k <= nb ->
    let kD := fs_scan_clr_unal F bh k in
    k <= kD <= k + 31 /\ negb (isset_bh bh kD) && unaligned_bh kD = false /\ (forall x, k <= x < kD -> isset_bh bh x = false).
  Proof.
    intros k Hk Hkn. cbv zeta.
    set (d := (32 - k mod 32) mod 32). pose proof (Z.mod_pos_bound k 32 ltac:(lia)) as Hm.
    assert (Hd : 0 <= d <= 31) by (subst d; Z.div_mod_to_equations; lia).
    assert (Ha : (k + d) mod 32 = 0) by (subst d; Z.div_mod_to_equations; lia).
    cps_destruct (scan_spec (fun x => negb (isset_bh bh x) && unaligned_bh x) 1 (fun f x => fs_scan_clr_unal f bh x)
                ltac:(reflexivity) ltac:(intros; apply fs_scan_clr_unal_S) F (Z.to_nat d) k ltac:(unfold F, FSC; lia)) as (j & Hj & E & Hc & Hall).
    { replace (k + 1 * Z.of_nat (Z.to_nat d)) with (k + d) by lia. rewrite unaligned_bh_mod, Ha. cbn. apply Bool.andb_false_r. }
    rewrite E. split; [lia|]. split; [exact Hc|].
    intros x Hx. specialize (Hall (Z.to_nat (x - k)) ltac:(lia)). replace (k + 1 * Z.of_nat (Z.to_nat (x - k))) with x in Hall by lia.
    apply Bool.andb_true_iff in Hall. destruct Hall as [H1 _]. apply Bool.negb_true_iff in H1. exact H1.
  Qed.

  (* [comment removed for export] *)
  Lemma scanE_ok : forall k, 0 <= k <= nb + 31 -> k mod 32 = 0 ->
    let kE := fs_scan_word_00 F bh k in
    k <= kE <= nb + 31 /\ (bh_word bh kE =? 0) = false /\ kE mod 32 = 0.
  Proof.
    intros k Hk Ha. cbv zeta.
    set (q0 := 32 * (nb / 32)). assert (Hq0 : nb - 31 <= q0 <= nb /\ q0 mod 32 = 0) by (subst q0; Z.div_mod_to_equations; lia).
    destruct (Z_le_gt_dec k q0) as [LE|GT].
    - assert (Hn : exists n, q0 = k + 32 * Z.of_nat n) by (exists (Z.to_nat ((q0 - k) / 32)); Z.div_mod_to_equations; lia).
      destruct Hn as [n Hn].
      cps_destruct (scan_spec (fun x => bh_word bh x =? 0) 32 (fun f x => fs_scan_word_00 f bh x)
                  ltac:(reflexivity) ltac:(intros; apply fs_scan_word_00_S) F n k ltac:(unfold F, FSC; lia)) as (j & Hj & E & Hc & Hall).
      { rewrite <- Hn. apply (word_not_zero bh q0 nb); [lia| lia| lia|]. pose proof (sent_even 0 ltac:(lia)) as T. rewrite Z.mul_0_r, Z.add_0_r in T. exact T. }
      rewrite E. split; [lia|]. split; [exact Hc|]. Z.div_mod_to_equations. lia.
    - assert (Hk2 : nb + 1 <= k) by (Z.div_mod_to_equations; lia).
      cps_destruct (scan_spec (fun x => bh_word bh x =? 0) 32 (fun f x => fs_scan_word_00 f bh x)
                  ltac:(reflexivity) ltac:(intros; apply fs_scan_word_00_S) F 0%nat k ltac:(lia)) as (j & Hj & E & Hc & Hall).
      { replace (k + 32 * Z.of_nat 0) with k by lia.
        apply (word_not_zero bh k (nb + 2 * ((k - nb + 1) / 2))); [lia| lia| Z.div_mod_to_equations; lia|]. apply sent_even. Z.div_mod_to_equations; lia. }
      assert (j = 0)%nat by lia. subst j. rewrite E. replace (k + 32 * Z.of_nat 0) with k in Hc |- * by lia. split; [lia|]. split; [exact Hc| exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma scanF_ok : forall k, 0 <= k <= nb + 31 ->
    let kF := fs_scan_clr F bh k in
    k <= kF <= nb + 32 /\ isset_bh bh kF = true /\ (forall x, k <= x < kF -> isset_bh bh x = false).
  Proof.
    intros k Hk. cbv zeta.
    assert (Hb : exists b, k <= b <= nb + 32 /\ b <= k + nb /\ isset_bh bh b = true).
    { destruct (Z_le_gt_dec k nb) as [LE|GT].
      - exists nb. split; [lia|]. split; [lia|]. pose proof (sent_even 0 ltac:(lia)) as T. rewrite Z.mul_0_r, Z.add_0_r in T. exact T.
      - exists (nb + 2 * ((k - nb + 1) / 2)). split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|]. apply sent_even. Z.div_mod_to_equations; lia. }
    cps_destruct Hb as (b & Hb1 & Hb2 & Hb3).
    cps_destruct (scan_spec (fun x => negb (isset_bh bh x)) 1 (fun f x => fs_scan_clr f bh x)
                ltac:(reflexivity) ltac:(intros; apply fs_scan_clr_S) F (Z.to_nat (b - k)) k ltac:(unfold F, FSC; lia)) as (j & Hj & E & Hc & Hall).
    { replace (k + 1 * Z.of_nat (Z.to_nat (b - k))) with b by lia. rewrite Hb3. reflexivity. }
    rewrite E. split; [lia|]. split; [apply Bool.negb_false_iff in Hc; exact Hc|].
    intros x Hx. specialize (Hall (Z.to_nat (x - k)) ltac:(lia)). replace (k + 1 * Z.of_nat (Z.to_nat (x - k))) with x in Hall by lia.
    apply Bool.negb_true_iff in Hall. exact Hall.
  Qed.

  (* [comment removed for export] *)
  Lemma scan_ok_of : forall k0, 0 <= k0 <= nb -> isset_bh bh k0 = true -> scan_ok nb bh k0.
  Proof.
    intros k0 Hk0 B0. unfold scan_ok. fold F. cbv zeta.
    cps_pose (scanA_ok k0 ltac:(lia) ltac:(lia)) as (A1 & A2 & A3). set (kA := fs_scan_set_unal F bh k0) in *.
    assert (K1 : k0 + 1 <= bk1 nb bh k0 /\ bk1 nb bh k0 <= nb + 32).
    { unfold bk1. cbv zeta. fold F. fold kA. destruct (isset_bh bh kA) eqn:IA.
      - assert (AL : kA mod 32 = 0).
        { cbn [andb] in A2. rewrite unaligned_bh_mod in A2. apply Bool.negb_false_iff in A2. apply Z.eqb_eq in A2. exact A2. }
        cps_pose (scanB_ok kA ltac:(lia) AL) as (B1 & B2 & B3). set (kB := fs_scan_word_ff F bh kA) in *.
        cps_pose (scanC_ok kB ltac:(lia)) as (C1 & C2 & C3).
        split; [| lia].
        destruct (Z_lt_le_dec k0 (fs_scan_set F bh kB)); [lia|]. exfalso.
        assert (fs_scan_set F bh kB = k0) by lia. rewrite H in C2. rewrite C2 in B0. discriminate.
      - split; [| lia]. destruct (Z.eq_dec kA k0) as [EA|]; [| lia]. exfalso. rewrite EA in IA. rewrite IA in B0. discriminate. }
    split; [lia|]. split; [lia|]. split; [exact A2|]. split; [lia|]. split.
    - intros IA. assert (AL : kA mod 32 = 0).
      { rewrite IA in A2. cbn [andb] in A2. rewrite unaligned_bh_mod in A2. apply Bool.negb_false_iff in A2. apply Z.eqb_eq in A2. exact A2. }
      cps_pose (scanB_ok kA ltac:(lia) AL) as (B1 & B2 & B3). set (kB := fs_scan_word_ff F bh kA) in *.
      cps_pose (scanC_ok kB ltac:(lia)) as (C1 & C2 & C3).
      split; [exact B2|]. split; [lia|]. split; [exact C2| lia].
    - intros Hl. set (k1 := bk1 nb bh k0) in *.
      cps_pose (scanD_ok k1 ltac:(lia) ltac:(lia)) as (D1 & D2 & D3). set (kD := fs_scan_clr_unal F bh k1) in *.
      split; [exact D2|]. split; [lia|]. intros ID.
      assert (AL : kD mod 32 = 0).
      { rewrite ID in D2. cbn [andb negb] in D2. rewrite unaligned_bh_mod in D2. apply Bool.negb_false_iff in D2. apply Z.eqb_eq in D2. exact D2. }
      cps_pose (scanE_ok kD ltac:(lia) AL) as (E1 & E2 & E3). set (kE := fs_scan_word_00 F bh kD) in *.
      cps_pose (scanF_ok kE ltac:(lia)) as (F1 & F2 & F3).
      split; [exact E2|]. split; [lia|]. split; [exact F2| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma bk2_set : forall k0, 0 <= k0 <= nb -> isset_bh bh k0 = true -> bk1 nb bh k0 - 1 < nb ->
    isset_bh bh (bk2 nb bh (bk1 nb bh k0)) = true /\ bk1 nb bh k0 <= bk2 nb bh (bk1 nb bh k0) <= nb + 32.
  Proof.
    intros k0 Hk0 B0 Hl. pose proof (scan_ok_of k0 Hk0 B0) as SOK. unfold scan_ok in SOK. cbv zeta in SOK. fold F in SOK.
    cps_destruct SOK as (_ & K01 & _).
    unfold bk2. cbv zeta. fold F. set (k1 := bk1 nb bh k0) in *.
    cps_pose (scanD_ok k1 ltac:(lia) ltac:(lia)) as (D1 & D2 & D3). set (kD := fs_scan_clr_unal F bh k1) in *.
    destruct (isset_bh bh kD) eqn:ID; cbn [negb].
    - split; [exact ID| lia].
    - assert (AL : kD mod 32 = 0).
      { cbn [andb negb] in D2. rewrite unaligned_bh_mod in D2. apply Bool.negb_false_iff in D2. apply Z.eqb_eq in D2. exact D2. }
      cps_pose (scanE_ok kD ltac:(lia) AL) as (E1 & E2 & E3). set (kE := fs_scan_word_00 F bh kD) in *.
      cps_pose (scanF_ok kE ltac:(lia)) as (F1 & F2 & F3).
      split; [exact F2| lia].
  Qed.
End Six.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Eclass.
  Variables (nb : Z) (fm bh : zarr) (H : Z).
  Hypothesis NB : 1 <= nb <= 4294967296. Hypothesis HH : 1 <= H <= nb. Hypothesis PM : fm_perm fm nb.
  Definition kk (i : Z) : Z := let k := rd32 fm i - H in if k <? 0 then k + nb else k.
  Lemma kk_range : forall i, 0 <= i < nb -> 0 <= kk i < nb.
  Proof. intros i Hi. unfold kk. pose proof (proj1 PM i Hi). destruct (Z.ltb_spec (rd32 fm i - H) 0); lia. Qed.
  Lemma kk_inj : forall i j, 0 <= i < nb -> 0 <= j < nb -> kk i = kk j -> i = j.
  Proof.
    intros i j Hi Hj E. apply (proj2 PM i j Hi Hj). unfold kk in E. pose proof (proj1 PM i Hi). pose proof (proj1 PM j Hj).
    destruct (Z.ltb_spec (rd32 fm i - H) 0); destruct (Z.ltb_spec (rd32 fm j - H) 0); lia.
  Qed.
  Definition EP (ec : zarr) (i : Z) : Prop := forall k, 0 <= k < nb -> (exists i', 0 <= i' < i /\ kk i' = k) -> 0 <= rd32 ec k < nb.
  Lemma eclass_step : forall n ec i j, 0 <= i -> i + Z.of_nat n <= nb -> 0 <= j < nb -> (j <= i) -> EP ec i ->
    EP (fs_eclass n ec fm bh H nb i j) (i + Z.of_nat n).
  Proof.
    induction n as [|n IH]; intros ec i j Hi Hn Hj Hji P.
    - cbn [fs_eclass]. replace (i + Z.of_nat 0) with i by lia. exact P.
    - rewrite fs_eclass_S. cbv zeta. set (j' := if isset_bh bh i then i else j).
      assert (Hj' : 0 <= j' < nb /\ j' <= i + 1) by (subst j'; destruct (isset_bh bh i); lia).
      replace (i + Z.of_nat (S n)) with (i + 1 + Z.of_nat n) by lia.
      apply IH; [lia| lia| lia| lia|].
      (intros k Hk; cps_intros (i' & Hi' & Ek)). change (if rd32 fm i - H <? 0 then rd32 fm i - H + nb else rd32 fm i - H) with (kk i).
      destruct (Z.eq_dec (kk i) k) as [E|N].
      + rewrite <- E, rd32_wr32_same by lia. lia.
      + rewrite rd32_wr32_other by (intros E; apply N; symmetry; exact E).
        apply P; [exact Hk|]. exists i'. split; [| exact Ek].
        destruct (Z.eq_dec i' i) as [->|]; [exfalso; apply N; exact Ek| lia].
  Qed.
  Lemma eclass_ok : forall ec, ec_ok nb (fs_eclass (Z.to_nat nb) ec fm bh H nb 0 0).
  Proof.
    intros ec k Hk. pose proof (eclass_step (Z.to_nat nb) ec 0 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as P.
    replace (0 + Z.of_nat (Z.to_nat nb)) with nb in P by lia.
    apply P; [(intros k' Hk'; cps_intros (i' & Hi' & _)); lia| exact Hk|].
    cps_destruct (inj_onto kk nb kk_range kk_inj k Hk) as (i & Hi & Ei). exists i. split; [lia| exact Ei].
  Qed.
End Eclass.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Inv.
  Variables (fm0 ec0 bh0 : zarr) (nb : Z).
  Hypothesis ECB : zbok ec0. Hypothesis BW0 : bh_w32 bh0. Hypothesis NB : 1 <= nb <= 900000.

  Definition BIw (fm bh : zarr) : Prop := fm_perm fm nb /\ sent bh nb /\ isset_bh bh 0 = true.
  Definition BI (s : fbs) : Prop :=
    BIw (fb_fm s) (fb_bh s) /\ (fb_done s = false -> -1 <= fb_r s < nb /\ isset_bh (fb_bh s) (fb_r s + 1) = true).

  Lemma BI_step : forall s, fb_done s = false -> BI s -> BI (fs_bucket_iter nb s).
  Proof.
    intros [fm ec bh slo shi r nnd dn] Hd ((PM & SE & B0) & R). cbn [fb_fm fb_bh fb_done fb_r] in *. subst dn.
    specialize (R eq_refl). destruct R as [Hr Br].
    rewrite fs_bucket_iter_unfold. cbv zeta.
    pose proof (scan_ok_of bh nb ltac:(lia) SE (r + 1) ltac:(lia) Br) as SOK. unfold scan_ok in SOK. cbv zeta in SOK. cps_destruct SOK as (_ & K01 & _).
    set (k1 := bk1 nb bh (r + 1)) in *.
    destruct (Z.leb_spec nb (k1 - 1)) as [C1|C1].
    { split; [split; [exact PM| split; [exact SE| exact B0]]| cbn; intros; discriminate]. }
    pose proof (bk2_set bh nb ltac:(lia) SE (r + 1) ltac:(lia) Br ltac:(lia)) as [B2 K12]. fold k1 in B2, K12. set (k2 := bk2 nb bh k1) in *.
    destruct (Z.leb_spec nb (k2 - 1)) as [C2|C2].
    { split; [split; [exact PM| split; [exact SE| exact B0]]| cbn; intros; discriminate]. }
    destruct (Z.ltb_spec (k1 - 1) (k2 - 1)) as [C3|C3].
    - unfold BI, BIw. cbn [fb_fm fb_bh fb_done fb_r].
      pose proof (fqs_perm_frame ec nb fm slo shi (k1 - 1) (k2 - 1) (fqs_fuel (k1 - 1) (k2 - 1)) PM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [PM' _].
      unfold fallbackQSort3, fpush. cbn [fq_fm fq_sp fq_slo fq_shi fq_r]. replace (0 + 1) with 1 by reflexivity.
      split; [split; [exact PM'| split]|].
      + apply sent_fs_headers; [lia| lia| lia| exact SE].
      + apply isset_fs_headers_mono; [lia| lia| exact B0].
      + intros _. split; [lia|]. replace (k2 - 1 + 1) with k2 by lia. apply isset_fs_headers_mono; [lia| lia| exact B2].
    - unfold BI, BIw. cbn [fb_fm fb_bh fb_done fb_r]. split; [split; [exact PM| split; [exact SE| exact B0]]|].
      intros _. split; [lia|]. replace (k2 - 1 + 1) with k2 by lia. exact B2.
  Qed.
  Lemma BI_loop : forall u s, BI s -> BI (fs_bucket_loop u nb s).
  Proof.
    induction u as [|u IH]; intros s B; [exact B|]. rewrite fs_bucket_loop_S. destruct (fb_done s) eqn:Hd; [exact B|]. apply IH. apply BI_step; [exact Hd| exact B].
  Qed.
  Lemma BI_bucket_ok : forall s, BI s -> fb_done s = false -> bucket_ok nb s.
  Proof.
    intros [fm ec bh slo shi r nnd dn] ((PM & SE & B0) & R) Hd. cbn [fb_fm fb_bh fb_done fb_r fb_ec fb_slo fb_shi] in *. subst dn.
    specialize (R eq_refl). destruct R as [Hr Br].
    unfold bucket_ok. cbn [fb_fm fb_bh fb_r fb_ec fb_slo fb_shi]. cbv zeta.
    pose proof (scan_ok_of bh nb ltac:(lia) SE (r + 1) ltac:(lia) Br) as SOK. split; [exact SOK|].
    unfold scan_ok in SOK. cbv zeta in SOK. cps_destruct SOK as (_ & K01 & _).
    intros H1 H2 H3. apply qsort_ok_intro; lia.
  Qed.

  Definition HI (h : fhs) : Prop := BIw (fh_fm h) (fh_bh h).
  Lemma HI_0 : HI (fp_hs fm0 ec0 bh0 nb 0).
  Proof.
    unfold HI, BIw. cbn [fp_hs fs_H_loop fh_fm fh_bh fp_hs0]. split; [apply fp_fm1_perm; [exact ECB| lia| lia]|].
    unfold fp_bh3.
    assert (BW2 : bh_w32 (fs_bh_init 256 (fs_bh_zero (Z.to_nat (fp_nB nb)) bh0 0) (fp_ft4 fm0 ec0 nb) 0)) by (apply fs_bh_init_w32, fs_bh_zero_w32; exact BW0).
    split; [apply sent_init; [lia| exact BW2]|].
    rewrite fs_sentinel_low by (try lia; exact BW2).
    pose proof (fsf_ft4_ok ec0 nb ECB ltac:(lia) fm0 ltac:(lia)) as FT4. unfold fsf_ft4 in FT4.
    pose proof (fp_ft4_count ec0 nb ECB fm0 ltac:(lia) 0 ltac:(lia)) as C0. rewrite (Cl_0 ec0 nb ECB) in C0.
    lazymatch goal with |- isset_bh ?X 0 = true => replace (isset_bh X 0) with (isset_bh X (zget (fp_ft4 fm0 ec0 nb) 0)) by (rewrite C0; reflexivity) end.
    apply isset_fs_bh_init_at; [| lia]. intros b Hb. pose proof (FT4 b ltac:(lia)). lia.
  Qed.
  Lemma HI_step : forall t, fh_done (fp_hs fm0 ec0 bh0 nb t) = false -> HI (fp_hs fm0 ec0 bh0 nb t) -> HI (fp_hs fm0 ec0 bh0 nb (S t)).
  Proof.
    (intros t Hd; cps_intros (PM & SE & B0)). rewrite fp_hs_S by exact Hd. unfold fs_H_iter, HI. cbn [fh_fm fh_bh].
    set (h := fp_hs fm0 ec0 bh0 nb t) in *.
    set (s0 := FBS (fh_fm h) (fs_eclass (Z.to_nat nb) (fh_ec h) (fh_fm h) (fh_bh h) (fh_H h) nb 0 0) (fh_bh h) (fh_slo h) (fh_shi h) (-1) 0 false).
    assert (B : BI s0). { split; [split; [exact PM| split; [exact SE| exact B0]]|]. cbn. intros _. split; [lia|]. exact B0. }
    exact (proj1 (BI_loop (Z.to_nat (nb + 2)) s0 B)).
  Qed.
  Lemma HI_all : forall t, fh_done (fp_hs fm0 ec0 bh0 nb t) = false -> HI (fp_hs fm0 ec0 bh0 nb t).
  Proof.
    induction t as [|t IH]; intros Hd; [apply HI_0|].
    destruct (fh_done (fp_hs fm0 ec0 bh0 nb t)) eqn:Hdt.
    - pose proof (fp_hs_stay fm0 ec0 bh0 nb t 1 Hdt) as E. change (1 + t)%nat with (S t) in E. rewrite E, Hdt in Hd. discriminate.
    - apply HI_step; [exact Hdt| exact (IH eq_refl)].
  Qed.

  Theorem fsf_ec_ok : fsf_ec fm0 ec0 bh0 nb.
  Proof.
    intros t Hd. cps_destruct (HI_all t Hd) as (PM & SE & B0). unfold fp_ecT. cbv zeta.
    pose proof (fp_hs_H fm0 ec0 bh0 nb t ltac:(lia) Hd) as [EH HB].
    apply eclass_ok; [lia| rewrite EH; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat t) ltac:(lia) ltac:(lia)); lia| exact PM].
  Qed.

  Theorem fsf_bucket_ok : fsf_bucket fm0 ec0 bh0 nb.
  Proof.
    intros t u Hd Hdu. cps_destruct (HI_all t Hd) as (PM & SE & B0). unfold fp_bs in *. cbv zeta in Hdu |- *.
    apply BI_bucket_ok; [| exact Hdu]. apply BI_loop.
    split; [split; [exact PM| split; [exact SE| exact B0]]|]. cbn. intros _. split; [lia|]. exact B0.
  Qed.
End Inv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fs_facts_intro : forall fm ec bh nb, zbok ec -> bh_w32 bh -> 1 <= nb <= 900000 -> fs_facts fm ec bh nb.
Proof.
  intros fm ec bh nb ECB BW NB. unfold fs_facts.
  split; [apply fsf_distrib_ok; [exact ECB| lia| lia]|].
  split; [apply fsf_ft4_ok; [exact ECB| lia| lia]|].
  split; [apply fsf_fm1_ok; [exact ECB| lia| lia]|].
  split; [apply fsf_ec_ok; [exact ECB| exact BW| exact NB]|].
  split; [apply fsf_bucket_ok; [exact ECB| exact BW| exact NB]|].
  apply fsf_rebuild_ok; [exact ECB| lia].
Qed.
