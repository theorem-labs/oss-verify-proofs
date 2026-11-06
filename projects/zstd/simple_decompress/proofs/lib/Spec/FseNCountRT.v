(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseReaderRT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wsum_app l1 l2 : wsum (l1 ++ l2) = wsum l1 + wsum l2.
Proof. induction l1; simpl; lia. Qed.

Lemma wsum_repeat0 n : wsum (repeat 0 n) = 0.
Proof. induction n; cbn [repeat wsum]; auto. Qed.

Lemma firstn_upd_nat_lt m m' v l : (m <= m')%nat -> firstn m (upd_nat m' v l) = firstn m l.
Proof.
  revert m' l; induction m; intros m' [|x l] H; simpl; auto.
  - destruct m'; reflexivity.
  - destruct m'; [lia|]. simpl. f_equal. apply IHm. lia.
Qed.

Lemma firstn_S_upd_nat m v l : (m < length l)%nat -> firstn (S m) (upd_nat m v l) = firstn m l ++ [v].
Proof.
  revert l; induction m; intros [|x l] H; simpl in *; try lia; auto.
  rewrite IHm by lia. reflexivity.
Qed.

Lemma firstn_repeat0 m n : (m <= n)%nat -> firstn m (repeat 0 n) = repeat 0 m.
Proof. revert n; induction m; intros [|n] H; simpl; auto; try lia. f_equal. apply IHm. lia. Qed.

Lemma firstn_app_repeat (pre : list Z) n m :
  (length pre <= m <= length pre + n)%nat -> firstn m (pre ++ repeat 0 n) = pre ++ repeat 0 (m - length pre).
Proof.
  intros. rewrite firstn_app. rewrite firstn_all2 by lia. f_equal.
  apply firstn_repeat0. lia.
Qed.

Lemma nth_app_repeat0 (pre : list Z) n i :
  (length pre <= i)%nat -> nth i (pre ++ repeat 0 n) 0 = 0.
Proof.
  intros. rewrite app_nth2 by lia.
  destruct (Nat.lt_ge_cases (i - length pre) n).
  - apply nth_repeat_lt. auto.
  - rewrite nth_overflow; auto. rewrite repeat_length. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma harness_fill_inv fuel : forall draws s maxSV rw acc pre rw' d',
  0 <= s -> length acc = Z.to_nat s -> 0 <= rw -> Forall (fun c => -1 <= c) acc ->
  harness_fill fuel draws s maxSV rw acc = Some (pre, rw', d') ->
  exists s', s <= s' <= Z.max s maxSV /\ length pre = Z.to_nat s' /\ 0 <= rw' <= rw /\
             Forall (fun c => -1 <= c) pre /\ wsum pre + rw' = wsum acc + rw.
Proof.
  induction fuel; intros draws s maxSV rw acc pre rw' d' Hs Hlen Hrw Hall E; cbn [harness_fill] in E.
  - injection E as <- <- <-. exists s. repeat split; auto; lia.
  - destruct (Z.ltb_spec s maxSV); destruct (Z.ltb_spec 0 rw); cbn [andb] in E;
      try (injection E as <- <- <-; exists s; repeat split; auto; lia).
    destruct draws as [|n draws']; [discriminate|].
    destruct (Z.leb_spec (-1) n); destruct (Z.leb_spec n rw); cbn [andb] in E; try discriminate.
    match type of E with harness_fill _ ?d ?s1 ?m ?r ?ac = _ =>
      destruct (IHfuel d s1 m r ac pre rw' d') as (s' & A1 & A2 & A3 & A4 & A5) end.
    { lia. } { rewrite length_app; simpl; rewrite Hlen; lia. } { destruct (Z.ltb_spec n 0); lia. }
    { apply Forall_app; split; auto. } { exact E. }
    exists s'. rewrite wsum_app in A5. cbn [wsum] in A5.
    repeat split; auto; try lia.
    + destruct (Z.ltb_spec n 0); lia.
    + unfold weight in A5. destruct (Z.ltb_spec n 0); destruct (Z.eqb_spec n (-1)); lia.
Qed.

Lemma harness_ncount_shape L maxSV draws coin nc :
  harness_ncount L maxSV draws coin = Some nc ->
  exists pre rw d, harness_fill 256 draws 0 maxSV (2^L-1) [] = Some (pre, rw, d) /\
    nc = Zupd maxSV (if (rw+1 =? 1) && coin then -1 else rw+1) (pre ++ repeat 0 (256 - length pre)).
Proof.
  cbv beta zeta delta [harness_ncount].
  generalize (harness_fill 256 draws 0 maxSV (2 ^ L - 1) []) as o. intros o E.
  destruct o as [[[pre rw] d]|]; [|discriminate].
  exists pre, rw, d. split; [reflexivity|]. congruence.
Qed.

Theorem harness_ncount_valid tableLog maxSV draws coin nc :
  FSE_MIN_TABLELOG <= tableLog <= FSE_MAX_TABLELOG -> 0 <= maxSV <= 255 ->
  harness_ncount tableLog maxSV draws coin = Some nc ->
  valid_ncount nc maxSV tableLog.
Proof.
  unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG. intros HL HM E.
  destruct (harness_ncount_shape _ _ _ _ _ E) as (pre & rw & d & EF & Enc). clear E.
  assert (HP : 1 <= 2^tableLog) by (pose proof (pow2_pos tableLog); lia).
  destruct (harness_fill_inv 256 draws 0 maxSV (2^tableLog - 1) [] pre rw d ltac:(lia) eq_refl ltac:(lia) ltac:(constructor) EF)
    as (s' & A1 & A2 & A3 & A4 & A5).
  cbn [wsum] in A5.
  set (v := rw + 1) in Enc. set (v' := if (v =? 1) && coin then -1 else v) in Enc.
  set (nc0 := pre ++ repeat 0 (256 - length pre)) in Enc. subst nc.
  assert (Hlen0 : length nc0 = 256%nat) by (subst nc0; rewrite length_app, repeat_length; lia).
  assert (Hv' : -1 <= v' /\ v' <> 0 /\ weight v' = rw + 1).
  { subst v' v. unfold weight. destruct (Z.eqb_spec (rw+1) 1); destruct coin; cbn [andb];
      rewrite ?Z.eqb_refl; try (destruct (Z.eqb_spec (rw + 1) (-1))); lia. }
  assert (Hpre : forall i, (i < length pre)%nat -> -1 <= nth i pre 0).
  { intros i Hi. apply (Forall_nth (fun c => -1 <= c) pre); auto. }
  unfold valid_ncount, FSE_MIN_TABLELOG, FSE_MAX_TABLELOG. repeat split; try lia.
  - abstract (unfold Zupd; rewrite upd_nat_length; exact Hlen0).
  - abstract (intros i Hi; destruct (Z.eq_dec i maxSV); [
      subst i; rewrite Znth_Zupd_same; [lia|]; unfold Zlength; rewrite Hlen0; lia |
      rewrite Znth_Zupd_other by lia; unfold Znth; subst nc0;
      destruct (Nat.lt_ge_cases (Z.to_nat i) (length pre)); [
        rewrite app_nth1 by auto; apply Hpre; auto |
       rewrite nth_app_repeat0 by auto; lia ] ]).
  - abstract (rewrite Znth_Zupd_same; [lia|]; unfold Zlength; rewrite Hlen0; lia).
  - abstract (intros i Hi; rewrite Znth_Zupd_other by lia; unfold Znth; subst nc0;
    destruct (Nat.lt_ge_cases (Z.to_nat i) (length pre + (256 - length pre))); [
     apply nth_app_repeat0; lia |
     rewrite nth_overflow; auto; rewrite length_app, repeat_length; lia]).
  - abstract (unfold Zupd; replace (Z.to_nat (maxSV + 1)) with (S (Z.to_nat maxSV)) by lia;
    rewrite firstn_S_upd_nat by (rewrite Hlen0; lia);
    rewrite wsum_app; cbn [wsum]; subst nc0; rewrite firstn_app_repeat by lia;
    rewrite wsum_app, wsum_repeat0; lia).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma write_bound_le_512 maxSV tableLog :
  0 <= maxSV <= 255 -> 0 <= tableLog <= 12 -> write_bound maxSV tableLog <= 512.
Proof.
  intros. unfold write_bound, FSE_NCOUNTBOUND. destruct (Z.eqb_spec maxSV 0); [lia|].
  assert (((maxSV + 1) * tableLog + 4 + 2) / 8 <= 3078 / 8).
  { apply Z.div_le_mono; [lia|nia]. }
  change (3078 / 8) with 384 in H1. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma firstn_S_nth (l : list Z) n : (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof.
  revert l; induction n; intros [|x l] H; simpl in *; try lia; auto.
  rewrite <- IHn by lia. reflexivity.
Qed.

Lemma bytes_prefix_val l N n :
  all_bytes l -> (n <= length l)%nat ->
  (forall i, 0 <= i < Z.of_nat n -> Znth i l = byte_of N i) ->
  bytes_val (firstn n l) = N mod 2^(8 * Z.of_nat n).
Proof.
  intros HB Hn Hpre. induction n.
  - cbn [firstn bytes_val Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r. rewrite Z.mod_1_r. reflexivity.
  - rewrite firstn_S_nth by lia. rewrite bytes_val_app. rewrite IHn; [|lia|intros; apply Hpre; lia].
    cbn [bytes_val]. unfold Zlength. rewrite firstn_length_le by lia.
    specialize (Hpre (Z.of_nat n) ltac:(lia)). unfold Znth in Hpre. rewrite Nat2Z.id in Hpre. rewrite Hpre.
    unfold byte_of. rewrite Z.mul_0_r, Z.add_0_r.
    replace (8 * Z.of_nat (S n)) with (8 * Z.of_nat n + 8) by lia.
    rewrite (Z.pow_add_r 2 (8 * Z.of_nat n) 8) by lia.
    rewrite Z.rem_mul_r by (try apply pow2_pos; try apply Z.pow_nonzero; lia).
    change (2^8) with 256. reflexivity.
Qed.

Lemma stream_of_prefix l N TF n :
  all_bytes l -> (n <= length l)%nat -> 0 <= TF <= 8 * Z.of_nat n -> 0 <= N < 2^TF ->
  (forall i, 0 <= i < Z.of_nat n -> Znth i l = byte_of N i) ->
  bytes_val l mod 2^TF = N.
Proof.
  intros HB Hn HT HN Hpre.
  rewrite <- (mod_pow2_mod_pow2 (bytes_val l) (8 * Z.of_nat n) TF) by lia.
  rewrite <- bytes_val_firstn by auto. rewrite (bytes_prefix_val l N n) by auto.
  rewrite mod_pow2_mod_pow2 by lia. apply Z.mod_small.
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem write_ncount_ok nc maxSV tableLog buf0 :
  valid_ncount nc maxSV tableLog ->
  4 + 15 * (maxSV + 1) + 16 <= 8 * Zlength buf0 ->
  let TF := a_T (afinal nc maxSV tableLog) in
  let NF := a_N (afinal nc maxSV tableLog) in
  let dataSize := hdrSize nc maxSV tableLog in
  exists buf' E,
    write_ncount buf0 nc maxSV tableLog = Ok (buf', dataSize) /\
    length buf' = length buf0 /\
    8 * (dataSize - 1) < TF <= 8 * dataSize /\ 2 <= dataSize /\ 8 * dataSize <= 4 + 15 * (maxSV + 1) + 7 /\
    dataSize <= E <= dataSize + 1 /\ E <= Zlength buf0 /\
    (forall i, 0 <= i < E -> Znth i buf' = byte_of NF i) /\
    (forall i, E <= i -> Znth i buf' = Znth i buf0).
Proof.
  intros V Hroom. cbv zeta. pose proof (V_tl _ _ _ V).
  unfold write_ncount, FSE_MAX_TABLELOG, FSE_MIN_TABLELOG.
  destruct (Z.ltb_spec 12 tableLog); [lia|]. destruct (Z.ltb_spec tableLog 5); [lia|].
  destruct (Zlength buf0 <? write_bound maxSV tableLog); apply write_generic_ok; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem harness_round_trip nc maxSV tableLog data0 :
  valid_ncount nc maxSV tableLog ->
  length data0 = 512%nat ->
  let dataSize := hdrSize nc maxSV tableLog in
  (* [comment removed for export] *)
  write_bound maxSV tableLog <= 512 /\
  exists data',
    (* [comment removed for export] *)
    write_ncount data0 nc maxSV tableLog = Ok (data', dataSize) /\
    length data' = 512%nat /\ 2 <= dataSize <= 481 /\
    (* [comment removed for export] *)
    forall buff rt0,
      all_bytes buff -> dataSize <= Zlength buff ->
      (forall i, 0 <= i < dataSize -> Znth i buff = Znth i data') ->
      length rt0 = 256%nat ->
      (* [comment removed for export] *)
      exists rt,
        read_ncount rt0 255 buff = Ok (rt, maxSV, tableLog, dataSize) /\
        length rt = 256%nat /\
        (forall i, 0 <= i <= maxSV -> Znth i rt = Znth i nc) /\
        (forall i, maxSV < i <= 255 -> Znth i rt = 0).
Proof.
  intros V Hlen. cbv zeta.
  pose proof (V_tl _ _ _ V). pose proof (V_msv _ _ _ V).
  pose proof (afinal_spec nc maxSV tableLog V) as (IF & SYF & REMF & CF & TBF & NBF).
  split. { apply write_bound_le_512; lia. }
  destruct (write_ncount_ok nc maxSV tableLog data0 V) as (data' & E & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9).
  { unfold Zlength. rewrite Hlen. lia. }
  exists data'. split; [exact W1|]. split; [rewrite W2; exact Hlen|]. split; [lia|].
  intros buff rt0 HB Hsz Hpre Hrt.
  destruct (read_ncount_ok nc maxSV tableLog buff rt0 255 V HB ltac:(lia) ltac:(unfold Zlength; rewrite Hrt; lia))
    as (rt & R1 & R2 & R3 & R4 & R5).
  { unfold hdrSize in *. lia. }
  { apply (stream_of_prefix buff _ _ (Z.to_nat (hdrSize nc maxSV tableLog))); auto.
    - unfold Zlength in Hsz. lia.
    - rewrite Z2Nat.id by lia. lia.
    - intros i Hi. rewrite Z2Nat.id in Hi by lia. rewrite Hpre by lia. apply W8. lia. }
  exists rt. unfold hdrSize in *. rewrite R1. repeat split; auto. rewrite R2. exact Hrt.
Qed.

(* [comment removed for export] *)
Corollary harness_round_trip_from_draws tableLog maxSV draws coin nc data0 :
  FSE_MIN_TABLELOG <= tableLog <= FSE_MAX_TABLELOG -> 0 <= maxSV <= 255 ->
  harness_ncount tableLog maxSV draws coin = Some nc ->
  length data0 = 512%nat ->
  valid_ncount nc maxSV tableLog /\
  let dataSize := hdrSize nc maxSV tableLog in
  write_bound maxSV tableLog <= 512 /\
  exists data',
    write_ncount data0 nc maxSV tableLog = Ok (data', dataSize) /\
    length data' = 512%nat /\ 2 <= dataSize <= 481 /\
    forall buff rt0,
      all_bytes buff -> dataSize <= Zlength buff ->
      (forall i, 0 <= i < dataSize -> Znth i buff = Znth i data') ->
      length rt0 = 256%nat ->
      exists rt,
        read_ncount rt0 255 buff = Ok (rt, maxSV, tableLog, dataSize) /\
        length rt = 256%nat /\
        (forall i, 0 <= i <= maxSV -> Znth i rt = Znth i nc) /\
        (forall i, maxSV < i <= 255 -> Znth i rt = 0).
Proof.
  intros HL HM HN HD.
  pose proof (harness_ncount_valid _ _ _ _ _ HL HM HN) as V.
  split; [exact V|]. apply harness_round_trip; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition valid_stream (nc : list Z) (maxSV tableLog : Z) (bufZ : list Z) : Prop :=
  valid_ncount nc maxSV tableLog /\ all_bytes bufZ /\
  hdrSize nc maxSV tableLog <= Zlength bufZ /\
  bytes_val bufZ mod 2^(a_T (afinal nc maxSV tableLog)) = a_N (afinal nc maxSV tableLog).

Lemma valid_stream_read nc maxSV tableLog bufZ nc0 maxSVin :
  valid_stream nc maxSV tableLog bufZ -> maxSV <= maxSVin -> maxSVin + 1 <= Zlength nc0 ->
  exists ncF, read_ncount nc0 maxSVin bufZ = Ok (ncF, maxSV, tableLog, hdrSize nc maxSV tableLog) /\
              length ncF = length nc0 /\
              (forall i, 0 <= i <= maxSV -> Znth i ncF = Znth i nc) /\
              (forall i, maxSV < i <= maxSVin -> Znth i ncF = 0) /\
              (forall i, maxSVin < i -> Znth i ncF = Znth i nc0).
Proof.
  intros (V & HB & HS & HM) H1 H2. unfold hdrSize in *.
  apply (read_ncount_ok nc maxSV tableLog bufZ nc0 maxSVin V HB H1 H2 HS HM).
Qed.

Lemma valid_stream_of_prefix nc maxSV tableLog bufZ :
  valid_ncount nc maxSV tableLog -> all_bytes bufZ ->
  hdrSize nc maxSV tableLog <= Zlength bufZ ->
  (forall i, 0 <= i < hdrSize nc maxSV tableLog -> Znth i bufZ = byte_of (a_N (afinal nc maxSV tableLog)) i) ->
  valid_stream nc maxSV tableLog bufZ.
Proof.
  intros V HB HS HP. pose proof (afinal_spec nc maxSV tableLog V) as (IF & SYF & REMF & CF & TBF & NBF).
  pose proof (V_msv _ _ _ V).
  destruct (write_ncount_ok nc maxSV tableLog (repeat 0 512) V) as (buf' & E' & W1 & W2 & W3 & W4 & W5 & _).
  { unfold Zlength. rewrite repeat_length. lia. }
  split; [exact V|]. split; [exact HB|]. split; [exact HS|].
  apply (stream_of_prefix bufZ _ _ (Z.to_nat (hdrSize nc maxSV tableLog))); auto.
  - unfold Zlength in HS. lia.
  - rewrite Z2Nat.id by (unfold hdrSize in *; lia). unfold hdrSize in *. lia.
  - intros i Hi. rewrite Z2Nat.id in Hi by (unfold hdrSize in *; lia). apply HP. lia.
Qed.
