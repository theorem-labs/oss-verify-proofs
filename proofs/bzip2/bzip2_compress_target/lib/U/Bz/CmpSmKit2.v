(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA CmpCutSmB CmpHmKit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsGm BzCSmF1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCFactsSmB BzCFactsSmB2 CmpSmKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le4_0 : le4 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 4.
Proof. rewrite le4_bytes. reflexivity. Qed.
Lemma u32s_repeat_0 : forall n, u32s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (4 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat]. rewrite u32s_cons, IH, le4_0.
  replace (4 * S n)%nat with (4 + 4 * n)%nat by lia. rewrite repeat_app. reflexivity.
Qed.

Section WithSegs.
  Variable segs : list Segment.

  Lemma u32arr_zero_init : forall m P n,
    rw_cells segs m P [CB (Z.to_nat (4 * n)) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * n)))] -> 0 <= n ->
    u32arr segs m P (repeat (Z_to_bv 64 0) (Z.to_nat n)).
  Proof.
    intros m P n H Hn. apply (proj2 (u32arr_u8arr' segs m P _)). rewrite u32s_repeat_0.
    replace (4 * Z.to_nat n)%nat with (Z.to_nat (4 * n)) by lia.
    exact (u8arr_of_rw_cells segs m P _ _ H).
  Qed.

  (* [comment removed for export] *)
  Lemma ovw_zfill0_split : forall rf J N i n, 0 <= i -> i + Z.of_nat n <= N ->
    ovw (zfill0 n rf i) J N = firstn (Z.to_nat i) (ovw rf J N) ++ repeat (Z_to_bv 64 0) n ++ skipn (Z.to_nat i + n) (ovw rf J N).
  Proof.
    intros rf J N i n Hi HN. apply nth_error_ext. intros k.
    pose proof (ovw_length_nat rf J N) as L. pose proof (ovw_length_nat (zfill0 n rf i) J N) as L'.
    destruct (Nat.lt_ge_cases k (Z.to_nat N)) as [Hk|Hk].
    2:{ rewrite (proj2 (nth_error_None _ _)) by lia. symmetry. apply (proj2 (nth_error_None _ _)).
        rewrite !length_app, length_firstn, repeat_length, length_skipn. lia. }
    replace k with (Z.to_nat (Z.of_nat k)) by lia.
    destruct (Nat.lt_ge_cases k (Z.to_nat i)) as [H1|H1].
    - rewrite nth_error_app1 by (rewrite length_firstn; lia). rewrite nth_error_firstn' by lia.
      rewrite !ovw_nth_raw by lia. rewrite zfill0_def, zfill0_get.
      replace ((i <=? Z.of_nat k) && (Z.of_nat k <? i + Z.of_nat n))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      reflexivity.
    - rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn.
      destruct (Nat.lt_ge_cases k (Z.to_nat i + n)) as [H2|H2].
      + rewrite nth_error_app1 by (rewrite repeat_length; lia).
        rewrite nth_error_repeat by lia.
        rewrite ovw_nth_raw by lia. rewrite zfill0_def, zfill0_get.
        replace ((i <=? Z.of_nat k) && (Z.of_nat k <? i + Z.of_nat n))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        reflexivity.
      + rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length, nth_error_skipn.
        replace (Z.to_nat i + n + (Z.to_nat (Z.of_nat k) - Nat.min (Z.to_nat i) (length (ovw rf J N)) - n))%nat with (Z.to_nat (Z.of_nat k)) by lia.
        rewrite !ovw_nth_raw by lia. rewrite zfill0_def, zfill0_get.
        replace ((i <=? Z.of_nat k) && (Z.of_nat k <? i + Z.of_nat n))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
        reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rfrow_before_memset : forall m P rf J N t A,
    u32arr segs m P (ovw rf J N) -> 0 <= t -> 0 <= A -> 258 * t + A <= N ->
    u32arr segs m P (firstn (Z.to_nat (258 * t)) (ovw rf J N)) /\
    rw_cells segs m (P + 1032 * t) [CB (Z.to_nat (4 * A)) (u32s (firstn (Z.to_nat A) (skipn (Z.to_nat (258 * t)) (ovw rf J N))))] /\
    u32arr segs m (P + 1032 * t + 4 * A) (skipn (Z.to_nat (258 * t + A)) (ovw rf J N)).
  Proof.
    intros m P rf J N t A H Ht HA HN. pose proof (ovw_length_nat rf J N) as L.
    rewrite <- (firstn_skipn (Z.to_nat (258 * t)) (ovw rf J N)) in H. apply (proj1 (u32arr_app segs m P _ _)) in H. destruct H as [H0 H].
    rewrite length_firstn, L in H. replace (P + 4 * Z.of_nat (Nat.min (Z.to_nat (258 * t)) (Z.to_nat N))) with (P + 1032 * t) in H by lia.
    rewrite <- (firstn_skipn (Z.to_nat A) (skipn (Z.to_nat (258 * t)) (ovw rf J N))) in H.
    apply (proj1 (u32arr_app segs m (P + 1032 * t) _ _)) in H. destruct H as [H1 H2].
    rewrite length_firstn, length_skipn, L, skipn_skipn in H2.
    replace (P + 1032 * t + 4 * Z.of_nat (Nat.min (Z.to_nat A) (Z.to_nat N - Z.to_nat (258 * t)))) with (P + 1032 * t + 4 * A) in H2 by lia.
    replace (Z.to_nat A + Z.to_nat (258 * t))%nat with (Z.to_nat (258 * t + A)) in H2 by lia.
    split; [exact H0|]. split; [|exact H2].
    apply (proj1 (u32arr_u8arr' segs m (P + 1032 * t) _)) in H1. apply (rw_cells_of_u8arr segs) in H1.
    rewrite u32s_length, length_firstn, length_skipn, L in H1.
    replace (4 * Nat.min (Z.to_nat A) (Z.to_nat N - Z.to_nat (258 * t)))%nat with (Z.to_nat (4 * A)) in H1 by lia. exact H1.
  Qed.

  (* [comment removed for export] *)
  Lemma rfrow_after_memset : forall m P rf J N t A,
    u32arr segs m P (firstn (Z.to_nat (258 * t)) (ovw rf J N)) ->
    rw_cells segs m (P + 1032 * t) [CB (Z.to_nat (4 * A)) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * A)))] ->
    u32arr segs m (P + 1032 * t + 4 * A) (skipn (Z.to_nat (258 * t + A)) (ovw rf J N)) ->
    0 <= t -> 0 <= A -> 258 * t + A <= N ->
    u32arr segs m P (ovw (zfill0 (Z.to_nat A) rf (258 * t)) J N).
  Proof.
    intros m P rf J N t A H0 H1 H2 Ht HA HN.
    rewrite (ovw_zfill0_split rf J N (258 * t) (Z.to_nat A)) by lia.
    apply (proj2 (u32arr_app segs m P _ _)). split.
    - exact H0.
    - rewrite length_firstn, ovw_length_nat. replace (P + 4 * Z.of_nat (Nat.min (Z.to_nat (258 * t)) (Z.to_nat N))) with (P + 1032 * t) by lia.
      apply (proj2 (u32arr_app segs m (P + 1032 * t) _ _)). split; [apply (u32arr_zero_init m _ A H1 HA)|].
      rewrite repeat_length. replace (P + 1032 * t + 4 * Z.of_nat (Z.to_nat A)) with (P + 1032 * t + 4 * A) by lia.
      replace (Z.to_nat (258 * t) + Z.to_nat A)%nat with (Z.to_nat (258 * t + A)) by lia. exact H2.
  Qed.

  (* [comment removed for export] *)
  Lemma fave_zero_cells : forall m A f,
    rw_cells segs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> u32arr segs m A (zw32 (zero6 f) 6).
  Proof.
    intros m A f H. pose proof (rw_cells_merge segs m A [] _ [] ltac:(rewrite app_nil_r; exact H)) as M. cbn [app cells_size csize Nat.add] in M.
    replace (zw32 (zero6 f) 6) with (repeat (Z_to_bv 64 0) (Z.to_nat 6)).
    - apply (u32arr_zero_init m A 6); [| lia]. cbn [Z.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add repeat].
      lazymatch type of M with rw_cells _ _ _ [CB 24 ?bs] => replace (repeat (Z_to_bv 8 0) 24) with bs; [exact M| vm_compute; reflexivity] end.
    - apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k 6) as [Hk|Hk].
      + rewrite nth_error_repeat by lia. replace k with (Z.to_nat (Z.of_nat k)) by lia. rewrite zw32_nth by lia.
        unfold zero6. rewrite zfill0_get. replace ((0 <=? Z.of_nat k) && (Z.of_nat k <? 0 + Z.of_nat 6))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity.
      + rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia). reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma fave_cells_of_junk : forall m A (bs : list byte), u8arr segs m A bs -> length bs = 24%nat ->
    exists w1 w2 w3, rw_cells segs m A [C8 w1; C8 w2; C8 w3].
  Proof.
    intros m A bs U L. cps_destruct (u8arr_C8s 3 segs m A bs U ltac:(rewrite L; reflexivity)) as (w1 & w2 & w3 & H). cbn [map] in H.
    exists w1, w2, w3. exact H.
  Qed.
End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w_img_apartK (hi : Z) (W : list (Z * Z)) : Prop := Forall (fun iv => snd iv <= IMG_LO3 \/ hi <= fst iv) W.
Lemma w_img_apartK_disjoint : forall hi W A n, w_img_apartK hi W -> IMG_LO3 <= A -> A + n <= hi -> disjoint_from W A n.
Proof.
  intros hi W A n H LO HI. induction H as [|[lo' hi'] W H1 H2 IH]; cbn; [exact I|]. cbn in H1. split; [lia| exact IH].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le2_of_bytes : forall bs : list byte, length bs = 2%nat -> le2 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le2, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  assert (R : (0 <= bytes_le_to_Z bs < 2^16)%Z).
  { rewrite bytes_le_to_Z_le_val. pose proof (le_val_range _ (bytes_ok_map bs)) as X.
    rewrite length_map, L in X. change (256 ^ Z.of_nat 2)%Z with (2^16)%Z in X. lia. }
  unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. rewrite Z.mod_small by lia.
  rewrite <- L. apply MuslStr.Z_to_le_bytes_to_Z.
Qed.
Lemma rw_cells_CB2_C2 : forall segs m A pre bs post,
  rw_cells segs m A (pre ++ CB 2 bs :: post) -> rw_cells segs m A (pre ++ C2 (le_bytes_to_word bs) :: post).
Proof.
  intros segs m A pre bs post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 [W2 W3]]. cbn in W2.
  split; [split|].
  - apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W3].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le2_of_bytes by exact W2. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.
(* [comment removed for export] *)
Lemma cost_cells_of_junk6 : forall segs m A (bs : list byte), u8arr segs m A bs -> length bs = 12%nat ->
  exists w1 w2 w3 w4 w5 w6, rw_cells segs m A [C2 w1; C2 w2; C2 w3; C2 w4; C2 w5; C2 w6].
Proof.
  intros segs m A bs U L. pose proof (rw_cells_of_u8arr segs m A bs U) as C. rewrite L in C.
  pose proof (rw_cells_split_CB segs m A [] 12 bs [] [2;2;2;2;2;2]%nat C eq_refl) as S. cbn [mk_CB_cells app] in S.
  apply (rw_cells_CB2_C2 segs m A []) in S; cbn [app] in S.
  lazymatch type of S with rw_cells _ _ _ (?c1 :: _) => apply (rw_cells_CB2_C2 segs m A [c1]) in S; cbn [app] in S end.
  lazymatch type of S with rw_cells _ _ _ (?c1 :: ?c2 :: _) => apply (rw_cells_CB2_C2 segs m A [c1; c2]) in S; cbn [app] in S end.
  lazymatch type of S with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: _) => apply (rw_cells_CB2_C2 segs m A [c1; c2; c3]) in S; cbn [app] in S end.
  lazymatch type of S with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: _) => apply (rw_cells_CB2_C2 segs m A [c1; c2; c3; c4]) in S; cbn [app] in S end.
  lazymatch type of S with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: _) => apply (rw_cells_CB2_C2 segs m A [c1; c2; c3; c4; c5]) in S; cbn [app] in S end.
  lazymatch type of S with rw_cells _ _ _ [C2 ?w1; C2 ?w2; C2 ?w3; C2 ?w4; C2 ?w5; C2 ?w6] => exists w1, w2, w3, w4, w5, w6; exact S end.
Qed.
Lemma cost_zero_cells6 : forall segs m A,
  rw_cells segs m A [C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0)] ->
  u8arr segs m A (zb8 znew 12).
Proof.
  intros segs m A H. pose proof (rw_cells_merge segs m A [] _ [] ltac:(rewrite app_nil_r; exact H)) as M. cbn [app cells_size csize Nat.add] in M.
  apply (zb8_init segs m A 12 _ M ltac:(lia)).
  intros k b Hk.
  assert (cells_bytes [C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0)] = repeat (Z_to_bv 8 0) 12) as E by (vm_compute; reflexivity).
  rewrite E in Hk. apply nth_error_In in Hk. apply repeat_spec in Hk. exact Hk.
Qed.
(* [comment removed for export] *)
Lemma fave_cells_of_junk6 : forall segs m A (bs : list byte), u8arr segs m A bs -> length bs = 24%nat ->
  exists w1 w2 w3 w4 w5 w6, rw_cells segs m A [C4 w1; C4 w2; C4 w3; C4 w4; C4 w5; C4 w6].
Proof.
  intros segs m A bs U L. pose proof (rw_cells_of_u8arr segs m A bs U) as C. rewrite L in C.
  pose proof (rw_cells_split_CB segs m A [] 24 bs [] [4;4;4;4;4;4]%nat C eq_refl) as S. cbn [mk_CB_cells app] in S.
  apply (rw_cells_CB4_C4 segs m A []) in S; cbn [app] in S.
  lazymatch type of S with rw_cells _ _ _ (?c1 :: _) => apply (rw_cells_CB4_C4 segs m A [c1]) in S; cbn [app] in S end.
  lazymatch type of S with rw_cells _ _ _ (?c1 :: ?c2 :: _) => apply (rw_cells_CB4_C4 segs m A [c1; c2]) in S; cbn [app] in S end.
  lazymatch type of S with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: _) => apply (rw_cells_CB4_C4 segs m A [c1; c2; c3]) in S; cbn [app] in S end.
  lazymatch type of S with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: _) => apply (rw_cells_CB4_C4 segs m A [c1; c2; c3; c4]) in S; cbn [app] in S end.
  lazymatch type of S with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: _) => apply (rw_cells_CB4_C4 segs m A [c1; c2; c3; c4; c5]) in S; cbn [app] in S end.
  lazymatch type of S with rw_cells _ _ _ [C4 ?w1; C4 ?w2; C4 ?w3; C4 ?w4; C4 ?w5; C4 ?w6] => exists w1, w2, w3, w4, w5, w6; exact S end.
Qed.
Lemma fave_zero_cells6 : forall segs m A f,
  rw_cells segs m A [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  u32arr segs m A (zw32 (zero6 f) 6).
Proof.
  intros segs m A f H. pose proof (rw_cells_merge segs m A [] _ [] ltac:(rewrite app_nil_r; exact H)) as M. cbn [app cells_size csize Nat.add] in M.
  replace (zw32 (zero6 f) 6) with (repeat (Z_to_bv 64 0) (Z.to_nat 6)).
  - apply (u32arr_zero_init segs m A 6); [| lia]. cbn [Z.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add repeat].
    lazymatch type of M with rw_cells _ _ _ [CB 24 ?bs] => replace (repeat (Z_to_bv 8 0) 24) with bs; [exact M| vm_compute; reflexivity] end.
  - apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k 6) as [Hk|Hk].
    + rewrite nth_error_repeat by lia. replace k with (Z.to_nat (Z.of_nat k)) by lia. rewrite zw32_nth by lia.
      unfold zero6. rewrite zfill0_get. replace ((0 <=? Z.of_nat k) && (Z.of_nat k <? 0 + Z.of_nat 6))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity.
    + rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le8_firstn4 : forall v, firstn 4 (le8 v) = le4 v.
Proof. intros v. reflexivity. Qed.
Lemma rw_cells_lw_C8 : forall segs m A pre v post ad,
  rw_cells segs m A (pre ++ C8 v :: post) -> ad = wa (A + Z.of_nat (cells_size pre)) ->
  ov_read_bytes segs m ad 4 = Some (le4 v).
Proof.
  intros segs m A pre v post ad [[Hwf Hb] _] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [Wp _].
  pose proof (cells_bytes_length pre Wp) as Lp.
  rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
  rewrite (bytes_at_read segs m A _ (Z.of_nat (cells_size pre)) 4 Hb); [| lia| rewrite !length_app, length_le8, Lp; lia].
  f_equal. rewrite Nat2Z.id, skipn_app, Lp, Nat.sub_diag. rewrite skipn_all2 by (rewrite Lp; lia). cbn [skipn app].
  change (skipn 0 (le8 v ++ cells_bytes post)) with (le8 v ++ cells_bytes post).
  rewrite firstn_app, length_le8. change (4 - 8)%nat with 0%nat. cbn [firstn]. rewrite app_nil_r. apply le8_firstn4.
Qed.

End ACeilS1.
