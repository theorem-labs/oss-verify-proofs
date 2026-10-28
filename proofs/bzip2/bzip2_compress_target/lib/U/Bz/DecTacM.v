(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


Lemma Z_to_le_bytes_app : forall n k z, (0 <= z)%Z ->
  Z_to_le_bytes (n + k) z = Z_to_le_bytes n z ++ Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros k z Hz.
  - cbn [Nat.add Z_to_le_bytes app]. replace (8 * Z.of_nat 0)%Z with 0%Z by reflexivity. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH by (apply Z.shiftr_nonneg; lia).
    rewrite Z.shiftr_shiftr by lia. repeat f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma le8_split : forall w : word, le8 w = le4 w ++ le4 (Z_to_bv 64 (bv_unsigned w / 4294967296)).
Proof.
  intros w. unfold le8, le4, word_to_le_bytes. pose proof (bv_unsigned_in_range 64 w) as R.
  change 8%nat with (4 + 4)%nat. rewrite Z_to_le_bytes_app by lia. f_equal.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus in *.
  rewrite Z.mod_small; [reflexivity|].
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_C8_split : forall segs m A pre (w : word) post,
  rw_cells segs m A (pre ++ C8 w :: post) ->
  rw_cells segs m A (pre ++ C4 w :: C4 (Z_to_bv 64 (bv_unsigned w / 4294967296)) :: post).
Proof.
  intros segs m A pre w post H.
  pose proof H as H0. destruct H0 as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 [_ W3]].
  eapply rw_cells_same_bytes; [ | | | exact H].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le8_split. rewrite <- app_assoc. reflexivity.
  - rewrite !cells_size_app. reflexivity.
  - apply cells_wf_app. split; [exact W1|]. cbn. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End ACeilS1.


(* [comment removed for export] *)
Ltac slot_split H k :=
  lazymatch type of H with rw_cells ?sg ?m ?A ?cs =>
    rewrite <- (firstn_skipn k cs) in H; cbn [firstn skipn] in H;
    lazymatch type of H with rw_cells _ _ _ (?pre ++ C8 ?w :: ?post) =>
      apply (rw_cells_C8_split sg m A pre w post) in H; cbn [app] in H
    end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Arr.
Section ACeilS2. Context {ACEIL__ : ACeil}.


Lemma u32arr_split3 : forall segs m A ws (i k : nat), (i + k <= length ws)%nat ->
  u32arr segs m A ws ->
  u32arr segs m A (firstn i ws) /\
  u32arr segs m (A + 4 * Z.of_nat i) (firstn k (skipn i ws)) /\
  u32arr segs m (A + 4 * Z.of_nat (i + k)) (skipn (i + k) ws) /\
  length (firstn i ws) = i /\ length (firstn k (skipn i ws)) = k /\ length (skipn (i + k) ws) = (length ws - (i + k))%nat /\
  ws = firstn i ws ++ firstn k (skipn i ws) ++ skipn (i + k) ws.
Proof.
  intros segs m A ws i k Hik H.
  cps_pose (proj1 (u32arr_window segs m A ws i k Hik) H) as (H1 & H2 & H3).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [rewrite firstn_length_le; [reflexivity|lia]|].
  split; [rewrite firstn_length_le; [reflexivity|rewrite skipn_length; lia]|].
  split; [rewrite skipn_length; reflexivity|].
  rewrite <- (firstn_skipn i ws) at 1. f_equal.
  rewrite <- (firstn_skipn k (skipn i ws)) at 1. rewrite skipn_skipn, (Nat.add_comm k i). reflexivity.
Qed.

Lemma u32arr_join3 : forall segs m A pre mid suf,
  u32arr segs m A pre -> u32arr segs m (A + 4 * Z.of_nat (length pre)) mid ->
  u32arr segs m (A + 4 * Z.of_nat (length pre + length mid)) suf ->
  u32arr segs m A (pre ++ mid ++ suf).
Proof.
  intros segs m A pre mid suf H1 H2 H3.
  apply (proj2 (u32arr_app segs m A pre (mid ++ suf))). split; [exact H1|].
  apply (proj2 (u32arr_app segs m _ mid suf)). split; [exact H2|].
  replace (A + 4 * Z.of_nat (length pre) + 4 * Z.of_nat (length mid))%Z with (A + 4 * Z.of_nat (length pre + length mid))%Z by lia.
  exact H3.
Qed.

Lemma u8arr_split3 : forall segs m A bs (i k : nat), (i + k <= length bs)%nat ->
  u8arr segs m A bs ->
  u8arr segs m A (firstn i bs) /\
  u8arr segs m (A + Z.of_nat i) (firstn k (skipn i bs)) /\
  u8arr segs m (A + Z.of_nat (i + k)) (skipn (i + k) bs) /\
  length (firstn i bs) = i /\ length (firstn k (skipn i bs)) = k /\ length (skipn (i + k) bs) = (length bs - (i + k))%nat /\
  bs = firstn i bs ++ firstn k (skipn i bs) ++ skipn (i + k) bs.
Proof.
  intros segs m A bs i k Hik H.
  cps_pose (proj1 (u8arr_window segs m A bs i k Hik) H) as (H1 & H2 & H3).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [rewrite firstn_length_le; [reflexivity|lia]|].
  split; [rewrite firstn_length_le; [reflexivity|rewrite skipn_length; lia]|].
  split; [rewrite skipn_length; reflexivity|].
  rewrite <- (firstn_skipn i bs) at 1. f_equal.
  rewrite <- (firstn_skipn k (skipn i bs)) at 1. rewrite skipn_skipn, (Nat.add_comm k i). reflexivity.
Qed.

Lemma u8arr_join3 : forall segs m A pre mid suf,
  u8arr segs m A pre -> u8arr segs m (A + Z.of_nat (length pre)) mid ->
  u8arr segs m (A + Z.of_nat (length pre + length mid)) suf ->
  u8arr segs m A (pre ++ mid ++ suf).
Proof.
  intros segs m A pre mid suf H1 H2 H3.
  apply (proj2 (u8arr_app segs m A pre (mid ++ suf))). split; [exact H1|].
  apply (proj2 (u8arr_app segs m _ mid suf)). split; [exact H2|].
  replace (A + Z.of_nat (length pre) + Z.of_nat (length mid))%Z with (A + Z.of_nat (length pre + length mid))%Z by lia.
  exact H3.
Qed.
End ACeilS2.


(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Frame.
Section ACeilS3. Context {ACEIL__ : ACeil}.


Lemma sub_fp_nil : forall Wq, sub_fp [] Wq.
Proof. intros Wq x _. exact I. Qed.

Lemma outside_not_inside : forall Wq x lo n, outside Wq x -> inside Wq lo n -> ~ (lo <= x < lo + n)%Z.
Proof.
  induction Wq as [|[a b] Wq IH]; intros x lo n Ho Hi; cbn in *.
  - destruct Hi.
  - destruct Ho as [H1 H2]. destruct Hi as [Hi|Hi]; [lia|]. eapply IH; eauto.
Qed.

Lemma sub_fp_cons : forall lo hi W Wq, inside Wq lo (hi - lo) -> sub_fp W Wq -> sub_fp ((lo, hi) :: W) Wq.
Proof.
  intros lo hi W Wq Hin Hs x Ho. cbn. split.
  - pose proof (outside_not_inside Wq x lo (hi - lo) Ho Hin). lia.
  - apply Hs. exact Ho.
Qed.

Lemma sub_fp_app_l : forall W W', sub_fp W (W ++ W').
Proof.
  induction W as [|[a b] W IH]; intros W' x Ho; cbn in *; [exact I|].
  destruct Ho as [H1 H2]. split; [exact H1|]. exact (IH W' x H2).
Qed.
End ACeilS3.


(* [comment removed for export] *)
Ltac sub_fp_solve :=
  repeat (apply sub_fp_cons; [ cbn [inside]; lia | ]); apply sub_fp_nil.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs BzContracts DecCut.

Ltac dj_plain :=
  lazymatch goal with
  | |- _ /\ _ => split; [ first [lia | exact I] | dj_plain ]
  | |- True => exact I
  | |- _ => lia
  end.

Ltac revive_f H MUL WML AOK :=
  unfold hidden in H;
  lazymatch type of MUL with munch ?W ?me ?m' =>
  lazymatch type of H with
  | rw_cells ?segs me ?A ?cs =>
      let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y;
      apply (rw_cells_transport segs W me m' A cs) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; dj_plain ]; clear Y
  | u32arr ?segs me ?A ?ws =>
      let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y;
      apply (u32arr_transport segs W me m' A ws) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; dj_plain ]; clear Y
  | u8arr ?segs me ?A ?bs =>
      let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y;
      apply (u8arr_transport segs W me m' A bs) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; dj_plain ]; clear Y
  | bytes_at ?segs me ?A ?bs =>
      let Y := fresh "SEPsrc" in pose proof (act_sep_s_src _ _ AOK) as Y;
      apply (bytes_at_transport segs W me m' A bs) in H; [ | exact MUL | cbn [disjoint_from]; simpl_sizes; dj_plain ]; clear Y
  | drest_at ?segs me ?S ?r =>
      apply (drest_transport segs W me m' S r) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; dj_plain | cbn [disjoint_from]; dj_plain | cbn [disjoint_from]; dj_plain ]
  | blk_at ?segs me ?cx ?k =>
      apply (blk_at_transport segs W me m' cx k) in H;
      [ | exact MUL | exact WML
        | let E := fresh "E" in
          intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
          [ pose proof (act_tt_s _ _ AOK E) as (? & ?)
          | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?)
          | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?) ];
          cbn [disjoint_from]; dj_plain ]
  end end.

Ltac revive_all_f MUL WML AOK :=
  repeat lazymatch goal with H : hidden _ |- _ => first [ revive_f H MUL WML AOK | fail 100 "cannot revive" H ] end.
