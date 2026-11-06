(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortF CmpMem BzCLemmasFs CmpFsKit0 AsanKit.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition SCb (X : fsenv) (Y : afenv) (nnd Hh : Z) (v112 v128 v136 v152 v160 v208 : word) : list cell :=
  [C8 (Z_to_bv 64 7621); C8 (Z_to_bv 64 (fe_nb X)); C8 (Z_to_bv 64 nnd); C8 (Z_to_bv 64 Hh); C8 (Z_to_bv 64 (ae_SHF Y)); C8 v112; C8 (Z_to_bv 64 0);
   C8 v128; C8 v136; C8 (Z_to_bv 64 2147483647); C8 v152; C8 v160;
   C8 (Z_to_bv 64 (18446744073709551615 - ae_SHI Y)); C8 (Z_to_bv 64 (18446744073709551615 - ae_SLO Y)); C8 (Z_to_bv 64 (ae_SHI Y)); C8 (Z_to_bv 64 (ae_SLO Y));
   C8 (Z_to_bv 64 (ae_FCP Y)); C8 v208; C8 (Z_to_bv 64 1)].

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. unfold le8, le4, word_to_le_bytes. reflexivity. Qed.
Lemma skipn_le8 : forall (n : nat) (w : word) (l : list byte), (8 <= n)%nat -> skipn n (le8 w ++ l) = skipn (n - 8) l.
Proof. intros n w l Hn. rewrite skipn_app, length_le8. rewrite skipn_all2 by (rewrite length_le8; lia). reflexivity. Qed.

(* [comment removed for export] *)
Lemma SCb_rd128 : forall segs (m : amem) X Y nnd Hh v112 v128 v136 v152 v160 v208,
  rw_cells segs m (ae_P Y + 72) (SCb X Y nnd Hh v112 v128 v136 v152 v160 v208) -> ov_read_bytes segs m (wa (ae_P Y + 128)) 4 = Some (le4 v128).
Proof.
  intros segs m X Y nnd Hh v112 v128 v136 v152 v160 v208 H. destruct H as [[Hwf Hb] Hw].
  replace (wa (ae_P Y + 128)) with (wa (ae_P Y + 72 + Z.of_nat 56)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_ov_read segs m _ _ 56 4 Hb).
  2:{ unfold SCb. cbn [cells_bytes cbytes]. rewrite !length_app, !length_le8. cbn. lia. }
  f_equal; unfold SCb; cbn [cells_bytes cbytes]; rewrite !skipn_le8 by lia; cbn [Nat.sub]; rewrite skipn_O;
    rewrite firstn_app, length_le8; cbn [Nat.sub]; rewrite firstn_O, app_nil_r; apply firstn4_le8.
Qed.
Lemma SCb_rd136 : forall segs (m : amem) X Y nnd Hh v112 v128 v136 v152 v160 v208,
  rw_cells segs m (ae_P Y + 72) (SCb X Y nnd Hh v112 v128 v136 v152 v160 v208) -> ov_read_bytes segs m (wa (ae_P Y + 136)) 4 = Some (le4 v136).
Proof.
  intros segs m X Y nnd Hh v112 v128 v136 v152 v160 v208 H. destruct H as [[Hwf Hb] Hw].
  replace (wa (ae_P Y + 136)) with (wa (ae_P Y + 72 + Z.of_nat 64)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_ov_read segs m _ _ 64 4 Hb).
  2:{ unfold SCb. cbn [cells_bytes cbytes]. rewrite !length_app, !length_le8. cbn. lia. }
  f_equal; unfold SCb; cbn [cells_bytes cbytes]; rewrite !skipn_le8 by lia; cbn [Nat.sub]; rewrite skipn_O;
    rewrite firstn_app, length_le8; cbn [Nat.sub]; rewrite firstn_O, app_nil_r; apply firstn4_le8.
Qed.

(* [comment removed for export] *)
Lemma bveqb0_true : forall x, (- 9223372036854775808 <= x < 9223372036854775808)%Z ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = true -> x = 0%Z.
Proof.
  intros x Hx H. unfold bv_eqb in H. apply Z.eqb_eq in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with 18446744073709551616%Z in H. Z.div_mod_to_equations. lia.
Qed.
Lemma bveqb0_false : forall x, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false -> x <> 0%Z.
Proof. intros x H E. subst x. unfold bv_eqb in H. rewrite Z.eqb_refl in H. discriminate. Qed.
Lemma bvlts0_true : forall x, (- 9223372036854775808 <= x < 9223372036854775808)%Z ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 0) = true -> (x < 0)%Z.
Proof.
  intros x Hx H. rewrite bv_lts_zero_r in H. apply Z.leb_le in H. rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with 18446744073709551616%Z in H. change (2^63)%Z with 9223372036854775808%Z in H. Z.div_mod_to_equations. lia.
Qed.
Lemma bvlts0_false : forall x, (- 9223372036854775808 <= x < 9223372036854775808)%Z ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 0) = false -> (0 <= x)%Z.
Proof.
  intros x Hx H. rewrite bv_lts_zero_r in H. apply Z.leb_gt in H. rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with 18446744073709551616%Z in H. change (2^63)%Z with 9223372036854775808%Z in H. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma zbv_sub_mod_r : forall a b, Z_to_bv 64 (a - b mod 18446744073709551616) = Z_to_bv 64 (a - b).
Proof. intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
Lemma zbv_sub_mod_l : forall a b, Z_to_bv 64 (a mod 18446744073709551616 - b) = Z_to_bv 64 (a - b).
Proof. intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
Lemma zbv_add_mod_r : forall a b, Z_to_bv 64 (a + b mod 18446744073709551616) = Z_to_bv 64 (a + b).
Proof. intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
Lemma zbv_add_mod_l : forall a b, Z_to_bv 64 (a mod 18446744073709551616 + b) = Z_to_bv 64 (a + b).
Proof. intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma app_fp_WtB : forall X Y, fsenv_ok X -> afenv_ok X Y -> afenv_offsh X Y ->
  app_fp [(fe_A1 X, fe_A1 X + ARR1_SIZE); (ae_P Y + 88, ae_P Y + 216); (ae_SLO Y, ae_SLO Y + 400); (ae_SHI Y, ae_SHI Y + 400)].
Proof.
  intros X Y XOK YOK YOFF. pose proof alloc_ceiling_range as ACR.
  unfold fsenv_ok, CEILv in XOK. cbv zeta in XOK. unfold afenv_ok, CEILv, SH_LO, SH_HI in YOK. cbv zeta in YOK.
  unfold afenv_offsh, SH_LO, SH_HI in YOFF.
  destruct XOK as (? & ? & ? & ? & ? & ? & ? & ? & ? & _). destruct YOK as (? & ? & ? & ? & ? & ? & ? & ? & ?).
  destruct YOFF as (O1 & O2 & O3 & O4).
  cbn [app_fp]. unfold SH_LO, SH_HI. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma frdW_intro_ro : forall segs W (m0 : amem) A cs,
  ro_cells segs m0 A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> frdW segs W m0 A cs.
Proof. intros segs W m0 A cs H D m MU. exact (ro_cells_transport segs W m0 m A cs H MU D). Qed.

End ACeilS1.

Ltac demod := rewrite ?zbv_sub_mod_r, ?zbv_sub_mod_l, ?zbv_add_mod_r, ?zbv_add_mod_l.
