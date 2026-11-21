(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayTF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayLP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayBlock.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayRows.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayFacts.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayTrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayRowsOk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayExcess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Large.
Variable b : oblock.
Variable lbs : Z.
Hypothesis OK : oblock_ok b lbs.
Hypothesis LBS : 1456 <= lbs <= 32768.

Notation lenL := (ob_lenL b).
Notation lenD := (ob_lenD b).
Notation BC := (ob_BC b).
Notation BD := (ob_BD b).
Notation syms := (ob_syms b).

Lemma Hc1_crude : 0 <= ob_Hc1 b <= 4495.
Proof.
  pose proof (ok_Hc1 b lbs OK) as E. pose proof (ok_blc b lbs OK) as [BL _]. pose proof (ok_WB b lbs OK) as WB.
  assert (S1 : 0 <= zsum (fun x => BC x * (BD x + xb_of_bl x)) 0 19 <= 14 * zsum BC 0 19).
  { rewrite <- zsum_scale. split.
    - apply zsum_nonneg. intros x Hx. pose proof (BC_nonneg b lbs OK x ltac:(lia)). pose proof (BD_range b lbs OK x ltac:(lia)).
      assert (0 <= xb_of_bl x <= 7) by (unfold xb_of_bl; destruct (x =? 16); [lia|]; destruct (x =? 17); [lia|]; destruct (x =? 18); lia). nia.
    - apply zsum_mono. intros x Hx. pose proof (BC_nonneg b lbs OK x ltac:(lia)). pose proof (BD_range b lbs OK x ltac:(lia)).
      assert (0 <= xb_of_bl x <= 7) by (unfold xb_of_bl; destruct (x =? 16); [lia|]; destruct (x =? 17); [lia|]; destruct (x =? 18); lia). nia. }
  lia.
Qed.

Lemma exS_split s0 : In s0 syms ->
  exS b s0 <= match s0 with OLit _ => 0 | OPair lc dc => hexL lc (lenL lc) + hexD dc (lenD dc) end.
Proof.
  intros I. pose proof (sym_ok_in b lbs OK s0 I) as SO. unfold exS. destruct s0 as [c|lc dc]; cbn [dcostS]; cbn in SO.
  - pose proof (in_syms_fL b _ I) as U. cbn [keyL] in U. pose proof (lenL_used b lbs OK c ltac:(lia) ltac:(lia)). lia.
  - unfold hexL, hexD.
    replace ((257 <=? lc) && (lc <=? 285)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    replace ((0 <=? dc) && (dc <=? 29)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    lia.
Qed.

Lemma EX_split : vEX b <= lsum (fun c => hexL c (lenL c) * fL b c) (zrange 0 286) + lsum (fun d => hexD d (lenD d) * gD b d) (zrange 0 30).
Proof.
  unfold vEX. rewrite (lsum_fL_w b lbs (fun c => hexL c (lenL c)) 0 286), (lsum_gD_w b lbs OK (fun d => hexD d (lenD d))).
  replace (existsb (Z.eqb 256) (zrange 0 286)) with true by (symmetry; apply existsb_exists; exists 256; split; [apply zrange_in; lia|reflexivity]).
  replace (hexL 256 (lenL 256)) with 0 by reflexivity. rewrite Z.add_0_r, <- ssum_add.
  apply ssum_le. intros s0 I. pose proof (exS_split s0 I) as X. pose proof (sym_ok_in b lbs OK s0 I) as SO.
  destruct s0 as [c|lc dc]; cbn [keyL]; cbn in SO.
  - replace (existsb (Z.eqb c) (zrange 0 286)) with true by (symmetry; apply existsb_exists; exists c; split; [apply zrange_in; lia|apply Z.eqb_refl]).
    unfold hexL. replace ((257 <=? c) && (c <=? 285)) with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). lia.
  - replace (existsb (Z.eqb lc) (zrange 0 286)) with true by (symmetry; apply existsb_exists; exists lc; split; [apply zrange_in; lia|apply Z.eqb_refl]).
    lia.
Qed.

Lemma EXL_bound : 540000 * lsum (fun c => hexL c (lenL c) * fL b c) (zrange 0 286) <= (NSYM b + 1) * (540 * 1602 + 2000 * 286).
Proof.
  destruct (ok_TL b lbs OK) as (zL & TF & _ & EL). pose proof (TL_W b lbs OK zL TF) as W. pose proof (ok_N b lbs OK).
  pose proof (tree_excess_L zL (fL b) [] TF ltac:(rewrite W; change (fib 24) with 46368; lia)) as X. rewrite W in X.
  change (Z.to_nat 286) with 286%nat in X. rewrite <- lsum_zrange in X.
  rewrite (lsum_ext (fun c => ffreq (fL b) [] c * hexL c (zt_len zL c)) (fun c => hexL c (lenL c) * fL b c)) in X; [exact X|].
  intros c Hc. apply zrange_in in Hc. rewrite ffreq_nil. rewrite <- EL by lia. lia.
Qed.

Lemma hexD_nonneg d L : 0 <= hexD d L.
Proof. unfold hexD. destruct (_ && _); lia. Qed.

Lemma EXD_bound : 540000 * lsum (fun d => hexD d (lenD d) * gD b d) (zrange 0 30) <= (NSYM b + 2) * (540 * 2114 + 2000 * 30).
Proof.
  destruct (ok_TD b lbs OK) as (zD & TF & _ & EL). pose proof (TD_W b lbs OK zD TF) as W. pose proof (WD_le b lbs OK) as WDle. pose proof (ok_N b lbs OK).
  assert (WDle2 : WD b <= NSYM b + 2).
  { unfold WD. destruct (forced_facts b lbs OK) as (_ & LF & _). unfold vP.
    pose proof (scount_le_len (fun s => match s with OLit _ => false | OPair _ _ => true end) syms). unfold NSYM. lia. }
  pose proof (tree_excess_D zD (gD b) (ob_forced b) TF ltac:(rewrite W; change (fib 24) with 46368; lia)) as X. rewrite W in X.
  change (Z.to_nat 30) with 30%nat in X. rewrite <- lsum_zrange in X.
  assert (Y : lsum (fun d => hexD d (lenD d) * gD b d) (zrange 0 30) <= lsum (fun d => ffreq (gD b) (ob_forced b) d * hexD d (zt_len zD d)) (zrange 0 30)).
  { apply lsum_le. intros d Hd. apply zrange_in in Hd. rewrite <- EL by lia. rewrite ffreqD.
    pose proof (hexD_nonneg d (lenD d)). pose proof (gD_nonneg b d).
    destruct (forcedD b d) eqn:Fd; [|lia]. apply (forcedD_spec b) in Fd. destruct (forced_facts b lbs OK) as (_ & _ & FF). destruct (FF d Fd). nia. }
  assert (0 <= WD b) by (unfold WD; unfold vP; pose proof (scount_nonneg (fun s => match s with OLit _ => false | OPair _ _ => true end) syms); lia).
  nia.
Qed.

Theorem overlay_bound_large : vH b + vEX b <= 8 * lbs - 10.
Proof.
  pose proof Hc1_crude as [H0 H1]. pose proof EX_split as E. pose proof EXL_bound as XL. pose proof EXD_bound as XD.
  pose proof (ok_N b lbs OK) as N. unfold vH.
  set (A := lsum (fun c => hexL c (lenL c) * fL b c) (zrange 0 286)) in *.
  set (B := lsum (fun d => hexD d (lenD d) * gD b d) (zrange 0 30)) in *.
  clearbody A B. nia.
Qed.

End Large.
