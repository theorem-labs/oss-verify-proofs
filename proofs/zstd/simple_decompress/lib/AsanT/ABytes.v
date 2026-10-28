(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import MState Mem Cells Step Arr Bytes InitMem Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma Z_to_le_bytes_le_val : forall bs : list byte,
  Z_to_le_bytes (length bs) (le_val (map bv_unsigned bs)) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length map le_val Z_to_le_bytes].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as V.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    replace ((bv_unsigned b + 256 * le_val (map bv_unsigned bs)) mod 256) with (bv_unsigned b); [reflexivity|].
    Z.div_mod_to_equations. nia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace ((bv_unsigned b + 256 * le_val (map bv_unsigned bs)) / 256) with (le_val (map bv_unsigned bs)) by (Z.div_mod_to_equations; nia).
    exact IH.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word.
  rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as V. rewrite length_map, L in V.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). change (256 ^ Z.of_nat 8) with (2^64) in V.
  rewrite Z.mod_small by lia. rewrite <- L at 1. apply Z_to_le_bytes_le_val.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le4, word_to_le_bytes, le_bytes_to_word.
  rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as V. rewrite length_map, L in V.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). change (256 ^ Z.of_nat 4) with (2^32) in V.
  rewrite Z.mod_small by lia. rewrite <- L at 1. apply Z_to_le_bytes_le_val.
Qed.
Lemma le2_of_bytes : forall bs : list byte, length bs = 2%nat -> le2 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le2, word_to_le_bytes, le_bytes_to_word.
  rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as V. rewrite length_map, L in V.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). change (256 ^ Z.of_nat 2) with (2^16) in V.
  rewrite Z.mod_small by lia. rewrite <- L at 1. apply Z_to_le_bytes_le_val.
Qed.

(* [comment removed for export] *)
Lemma c8_of_CB : forall m A bs, rw_cells bsegs m A [CB 8 bs] -> exists w : word, rw_cells bsegs m A [C8 w] /\ le8 w = bs.
Proof.
  intros m A bs H. pose proof H as H0. destruct H0 as [[[L _] _] _]. cbn in L.
  exists (le_bytes_to_word bs). split; [| apply le8_of_bytes; exact L].
  eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le8_of_bytes by exact L. reflexivity.
Qed.
Lemma c8c8_of_CB : forall m A bs, rw_cells bsegs m A [CB 16 bs] -> exists w1 w2 : word, rw_cells bsegs m A [C8 w1; C8 w2].
Proof.
  intros m A bs H. pose proof H as H0. destruct H0 as [[[L _] _] _]. cbn in L.
  exists (le_bytes_to_word (firstn 8 bs)), (le_bytes_to_word (skipn 8 bs)).
  eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite !le8_of_bytes by (rewrite ?length_firstn, ?length_skipn; lia).
  rewrite ?app_nil_r. apply firstn_skipn.
Qed.
(* [comment removed for export] *)
Lemma hdr_of_CB : forall m A bs, rw_cells bsegs m A [CB 16 bs] ->
  exists b0 b1 szh szl ctxj : Z,
    rw_cells bsegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
    /\ 0 <= b0 < 256 /\ 0 <= b1 < 256.
Proof.
  intros m A bs H. pose proof H as H0. destruct H0 as [[[L _] _] _]. cbn in L.
  destruct bs as [|x0 [|x1 bs2]]; cbn in L; try lia.
  exists (bv_unsigned x0), (bv_unsigned x1), (bv_unsigned (le_bytes_to_word (firstn 2 bs2))),
         (bv_unsigned (le_bytes_to_word (firstn 4 (skipn 2 bs2)))), (bv_unsigned (le_bytes_to_word (skipn 6 bs2))).
  pose proof (bv_unsigned_in_range 8 x0) as R0. pose proof (bv_unsigned_in_range 8 x1) as R1. unfold bv_modulus in R0, R1. cbn in R0, R1.
  split; [| lia].
  rewrite !Z_to_bv_bv_unsigned. rewrite !definitions.Z_to_bv_bv_unsigned.
  eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app].
  rewrite le2_of_bytes by (rewrite length_firstn; lia).
  rewrite le4_of_bytes by (rewrite length_firstn, length_skipn; lia).
  rewrite le8_of_bytes by (rewrite length_skipn; lia).
  cbn [app]. do 2 apply (f_equal (cons _)). rewrite ?app_nil_r.
  transitivity (firstn 2 bs2 ++ (firstn 4 (skipn 2 bs2) ++ skipn 6 bs2)); [rewrite ?app_assoc; reflexivity|].
  replace (skipn 6 bs2) with (skipn 4 (skipn 2 bs2)) by (rewrite skipn_skipn; reflexivity).
  rewrite firstn_skipn. apply firstn_skipn.
Qed.

Fixpoint words_of_bytes (bs : list byte) : list word :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest => le_bytes_to_word [b0;b1;b2;b3;b4;b5;b6;b7] :: words_of_bytes rest
  | _ => []
  end.

Lemma words_of_bytes_ok : forall k bs, length bs = (8 * k)%nat ->
  u64s (words_of_bytes bs) = bs /\ length (words_of_bytes bs) = k.
Proof.
  induction k as [|k IH]; intros bs L.
  - destruct bs; [split; reflexivity| cbn in L; lia].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 rest]]]]]]]]; cbn in L; try lia.
    destruct (IH rest ltac:(lia)) as [U Lk].
    cbn [words_of_bytes u64s length]. rewrite le8_of_bytes by reflexivity. cbn. rewrite U, Lk. split; reflexivity.
Qed.

Lemma u64arr_of_CB : forall m A k bs,
  rw_cells bsegs m A [CB (8 * k) bs] -> u64arr bsegs m A (words_of_bytes bs) /\ length (words_of_bytes bs) = k.
Proof.
  intros m A k bs [[WF BA] WR]. cbn in WF. destruct WF as [L _].
  destruct (words_of_bytes_ok k bs ltac:(lia)) as [U Lk].
  split; [|exact Lk]. split.
  - rewrite U. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. exact BA.
  - rewrite Lk. cbn [cells_size csize Nat.add] in WR. replace (8 * Z.of_nat k) with (Z.of_nat (8 * k + 0)) by lia. exact WR.
Qed.

(* [comment removed for export] *)
Lemma le8_small_split : forall z, 0 <= z < 2^32 -> le8 (Z_to_bv 64 z) = le4 (Z_to_bv 64 z) ++ le4 (Z_to_bv 64 0).
Proof.
  intros z Hz. unfold le8, le4, word_to_le_bytes. rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia.
  change (8+8) with 16. change (16+8) with 24. change (24+8) with 32. change (32+8) with 40. change (40+8) with 48. change (48+8) with 56.
  assert (E : forall k, 32 <= k -> Z.shiftr z k = 0).
  { intros k Hk. destruct (Z.eq_dec z 0) as [->|]; [apply Z.shiftr_0_l|]. apply Z.shiftr_eq_0; [lia|].
    apply Z.lt_le_trans with 32; [apply Z.log2_lt_pow2; lia| lia]. }
  rewrite (E 32), (E 40), (E 48), (E 56) by lia. rewrite !Z.shiftr_0_l. reflexivity.
Qed.

Lemma rw_cells_C8_to_C4C4_zero : forall m A,
  rw_cells bsegs m A [C8 (Z_to_bv 64 0)] -> rw_cells bsegs m A [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof.
  intros m A H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite (le8_small_split 0) by lia. rewrite app_nil_r. reflexivity.
Qed.

Lemma rw_cells_C4C4_to_C8 : forall m A z,
  0 <= z < 2^32 ->
  rw_cells bsegs m A [C4 (Z_to_bv 64 z); C4 (Z_to_bv 64 0)] -> rw_cells bsegs m A [C8 (Z_to_bv 64 z)].
Proof.
  intros m A z Hz H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite (le8_small_split z) by lia. rewrite app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Ltac take_cells k cs :=
  lazymatch k with
  | O => constr:(@nil cell)
  | S ?k' => lazymatch cs with ?c :: ?rest => let p := take_cells k' rest in constr:(c :: p) end
  end.
Ltac drop_cells k cs :=
  lazymatch k with
  | O => cs
  | S ?k' => lazymatch cs with _ :: ?rest => drop_cells k' rest end
  end.
Ltac rw_split H k H1 H2 :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let cs1 := take_cells k cs in let cs2 := drop_cells k cs in
    let sz := eval cbv in (Z.of_nat (cells_size cs1)) in
    change cs with (cs1 ++ cs2) in H; apply rw_cells_app in H; destruct H as [H1 H2];
    change (Z.of_nat (cells_size cs1)) with sz in H2;
    repeat match type of H2 with rw_cells _ _ (?X + ?a + ?b)%Z _ =>
      lazymatch a with Z0 => fail | Zpos _ => idtac | Zneg _ => idtac end;
      lazymatch b with Z0 => fail | Zpos _ => idtac | Zneg _ => idtac end;
      let c := eval vm_compute in (a + b)%Z in
      replace (X + a + b)%Z with (X + c)%Z in H2 by lia end
  end.
(* [comment removed for export] *)
Ltac rw_join H1 H2 H :=
  lazymatch type of H1 with rw_cells ?segs ?m ?A ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    let sz := eval cbv in (Z.of_nat (cells_size cs1)) in
    replace A2 with (A + sz)%Z in H2 by lia;
    pose proof (proj2 (rw_cells_app segs m A cs1 cs2) (conj H1 H2)) as H; clear H1 H2;
    cbn [app] in H
  end end.
(* [comment removed for export] *)
Ltac cb_split3 H a b c :=
  lazymatch type of H with rw_cells ?segs ?m ?A [CB ?n ?junk] =>
    apply (rw_cells_split_CB segs m A [] n junk [] [a; b; c]%nat) in H; [| cbn; lia];
    cbn [app mk_CB_cells] in H
  end.
