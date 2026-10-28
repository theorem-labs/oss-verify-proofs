(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzInv BzWalkArith.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sv32_upd_same : forall ws i v, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat ->
  sv32 (upd ws (Z.to_nat i) v) i = bv_swrap 32 (bv_unsigned v).
Proof. intros. unfold sv32. rewrite wnth_upd_same by assumption. reflexivity. Qed.
Lemma sv32_upd_other : forall ws i j v, (0 <= i)%Z -> (0 <= j)%Z -> i <> j ->
  sv32 (upd ws (Z.to_nat i) v) j = sv32 ws j.
Proof. intros. unfold sv32. rewrite wnth_upd_other by assumption. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WriteN.
  Variable segs : list Segment.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End WriteN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ReadB0.
  Variable segs : list Segment.
  Lemma u32arr_read_b0 : forall m A ws (i : Z) w a,
    u32arr segs m A ws -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 4 * i) ->
    ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (bv_unsigned w)].
  Proof.
    intros m A ws i w a [Hb _] Hn Hi ->.
    cps_destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
    replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
    rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 1 Hb).
    2:{ rewrite Eu, !app_length, length_le4, Hlu. lia. }
    rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
    rewrite firstn_app. unfold le4. cbn. reflexivity.
  Qed.
End ReadB0.
Lemma byte_lit_unsigned_mod : forall z, bv_unsigned (Z_to_bv 8 z) = (z mod 256)%Z.
Proof. intros. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Section Recell.
  Variable segs : list Segment.
  Lemma rw_cells_recell : forall m A cs cs',
    rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
    rw_cells segs m A cs'.
  Proof.
    intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb]| rewrite Es; exact Hw].
  Qed.
  Lemma rw_cells_split_c8_zero : forall m A pre post,
    rw_cells segs m A (pre ++ C8 (Z_to_bv 64 0) :: post) ->
    rw_cells segs m A (pre ++ C4 (Z_to_bv 64 0) :: C4 (Z_to_bv 64 0) :: post).
  Proof.
    intros m A pre post H. eapply rw_cells_recell; [exact H| | |].
    - pose proof (proj1 (proj1 H)) as W. rewrite cells_wf_app in W |- *. cbn [cells_wf] in *. tauto.
    - rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. reflexivity.
    - rewrite !cells_size_app. cbn. lia.
  Qed.
End Recell.

(* [comment removed for export] *)
Definition R16 (l : list byte) (f : Z -> Z) (N : Z) : Prop :=
  forall k, (0 <= k < N)%Z ->
    nth_error l (Z.to_nat (2 * k)) = Some (Z_to_bv 8 (f k mod 256)%Z) /\
    nth_error l (Z.to_nat (2 * k + 1)) = Some (Z_to_bv 8 (f k / 256)%Z).
Definition R8 (l : list byte) (g : Z -> Z) (M : Z) : Prop :=
  forall y, (0 <= y < M)%Z -> nth_error l (Z.to_nat y) = Some (Z_to_bv 8 (g y)).
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma Z_to_bv8_eqm : forall x y, (x mod 256 = y mod 256)%Z -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
  intros x y E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8)%Z with 256%Z. exact E.
Qed.
Lemma le2_lit : forall u, (0 <= u)%Z -> le2 (Z_to_bv 64 u) = [Z_to_bv 8 ((u mod 65536) mod 256)%Z; Z_to_bv 8 ((u mod 65536) / 256)%Z].
Proof.
  intros u Hu. unfold le2. cbn [Z_to_le_bytes]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  f_equal; [| f_equal]; apply Z_to_bv8_eqm.
  - Z.div_mod_to_equations. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8)%Z with 256%Z. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma R16_value : forall (x : Z), (0 <= x < 65536)%Z ->
  (bv_unsigned (Z_to_bv 8 (x mod 256)%Z) + 256 * bv_unsigned (Z_to_bv 8 (x / 256)%Z) = x)%Z.
Proof.
  intros x H. rewrite !byte_lit_unsigned_mod.
  rewrite (Z.mod_small (x / 256)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_mod by lia. pose proof (Z.div_mod x 256 ltac:(lia)). lia.
Qed.

End ACeilS1.
