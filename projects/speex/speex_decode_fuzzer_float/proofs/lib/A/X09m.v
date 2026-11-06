(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1cs X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0ae.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X110.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8).
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8).
+ rewrite Z.mod_pow2_bits_low, Z.lor_spec, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
+ rewrite Z.mod_pow2_bits_high by lia. symmetry. apply (testbit_high_false _ 8); lia.
- replace (Z.lor (bv_unsigned b) (bytes_le_to_Z bs ≪ 8) ≫ 8) with (bytes_le_to_Z bs); [exact IH|].
rewrite Z.shiftr_lor, Z.shiftr_shiftl_l by lia. cbn [Z.sub Z.pos_sub]. rewrite Z.shiftl_0_r.
rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.

Lemma bytes_regroup4 : forall n (bs : list byte), length bs = (4 * n)%nat -> exists ws, u32s ws = bs /\ length ws = n.
Proof.
induction n as [|n IH]; intros bs H.
- exists []. destruct bs; [split; reflexivity| cbn in H; lia].
- destruct bs as [|b0 [|b1 [|b2 [|b3 bs']]]]; cbn in H; try lia.
destruct (IH bs' ltac:(lia)) as (ws & E & L).
exists (le_bytes_to_word [b0; b1; b2; b3] :: ws). cbn [u32s length]. rewrite E, L. split; [|reflexivity].
change (b0 :: b1 :: b2 :: b3 :: bs') with ([b0; b1; b2; b3] ++ bs'). f_equal.
unfold le4, le_bytes_to_word. rewrite unsigned_lit.
2:{ pose proof (bytes_le_to_Z_nonneg [b0; b1; b2; b3]). pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3]) as X. cbn [length Z.of_nat Z.mul Pos.mul Pos.of_succ_nat Pos.succ] in X. lia. }
apply (Z_to_le_bytes_of_bytes [b0; b1; b2; b3]).
Qed.

Lemma bytes_regroup8 : forall n (bs : list byte), length bs = (8 * n)%nat -> exists ws, u64s ws = bs /\ length ws = n.
Proof.
induction n as [|n IH]; intros bs H.
- exists []. destruct bs; [split; reflexivity| cbn in H; lia].
- destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 bs']]]]]]]]; cbn in H; try lia.
destruct (IH bs' ltac:(lia)) as (ws & E & L).
exists (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7] :: ws). cbn [u64s length]. rewrite E, L. split; [|reflexivity].
change (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs') with ([b0; b1; b2; b3; b4; b5; b6; b7] ++ bs'). f_equal.
unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite unsigned_lit.
2:{ pose proof (bytes_le_to_Z_nonneg [b0; b1; b2; b3; b4; b5; b6; b7]). pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3; b4; b5; b6; b7]) as X. cbn [length Z.of_nat Z.mul Pos.mul Pos.of_succ_nat Pos.succ] in X. lia. }
apply (Z_to_le_bytes_of_bytes [b0; b1; b2; b3; b4; b5; b6; b7]).
Qed.

Lemma u32arr_chunk : forall m A ws n, u32arr bsegs m A ws -> Z.of_nat (length ws) = n ->
rw_cells bsegs m A [CB (Z.to_nat (n * 4)) (u32s ws)].
Proof.
intros m A ws n H Hl. replace (Z.to_nat (n * 4)) with (length (u32s ws)) by (rewrite u32s_length; lia).
apply rw_cells_of_u8arr. destruct H as [HB HW]. split; [exact HB|]. rewrite u32s_length, Nat2Z.inj_mul. exact HW.
Qed.
Lemma u64arr_chunk : forall m A ws n, u64arr bsegs m A ws -> Z.of_nat (length ws) = n ->
rw_cells bsegs m A [CB (Z.to_nat (n * 8)) (u64s ws)].
Proof.
intros m A ws n H Hl. replace (Z.to_nat (n * 8)) with (length (u64s ws)) by (rewrite u64s_length; lia).
apply rw_cells_of_u8arr. destruct H as [HB HW]. split; [exact HB|]. rewrite u64s_length, Nat2Z.inj_mul. exact HW.
Qed.
Lemma chunk_u32arr : forall m A ws junk n k, rw_cells bsegs m A [CB k (u32s ws ++ junk)] -> k = Z.to_nat (n * 4) -> 0 <= n ->
(length ws <= Z.to_nat n)%nat -> exists ws', u32arr bsegs m A (ws ++ ws') /\ Z.of_nat (length (ws ++ ws')) = n.
Proof.
intros m A ws junk n k H -> Hn Hle. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [LEN _]. rewrite app_length, u32s_length in LEN.
destruct (bytes_regroup4 (Z.to_nat n - length ws) junk ltac:(lia)) as (ws' & E & L).
exists ws'. split.
- apply u8arr_of_rw_cells in H. rewrite <- E, <- u32s_app in H. destruct H as [HB HW]. split; [exact HB|].
rewrite u32s_length, Nat2Z.inj_mul in HW. exact HW.
- rewrite app_length. lia.
Qed.
Lemma chunk_u64arr : forall m A ws junk n k, rw_cells bsegs m A [CB k (u64s ws ++ junk)] -> k = Z.to_nat (n * 8) -> 0 <= n ->
(length ws <= Z.to_nat n)%nat -> exists ws', u64arr bsegs m A (ws ++ ws') /\ Z.of_nat (length (ws ++ ws')) = n.
Proof.
intros m A ws junk n k H -> Hn Hle. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [LEN _]. rewrite app_length, u64s_length in LEN.
destruct (bytes_regroup8 (Z.to_nat n - length ws) junk ltac:(lia)) as (ws' & E & L).
exists ws'. split.
- apply u8arr_of_rw_cells in H. rewrite <- E, <- u64s_app in H. destruct H as [HB HW]. split; [exact HB|].
rewrite u64s_length, Nat2Z.inj_mul in HW. exact HW.
- rewrite app_length. lia.
Qed.

Lemma u32arr_u8 : forall m A ws, u32arr bsegs m A ws -> u8arr bsegs m A (u32s ws).
Proof. intros m A ws [HB HW]. split; [exact HB|]. rewrite u32s_length, Nat2Z.inj_mul. exact HW. Qed.
Lemma u8_u32arr : forall m A ws, u8arr bsegs m A (u32s ws) -> u32arr bsegs m A ws.
Proof. intros m A ws [HB HW]. split; [exact HB|]. rewrite u32s_length, Nat2Z.inj_mul in HW. exact HW. Qed.
Lemma u64arr_u8 : forall m A ws, u64arr bsegs m A ws -> u8arr bsegs m A (u64s ws).
Proof. intros m A ws [HB HW]. split; [exact HB|]. rewrite u64s_length, Nat2Z.inj_mul. exact HW. Qed.
Lemma u8_u64arr : forall m A ws, u8arr bsegs m A (u64s ws) -> u64arr bsegs m A ws.
Proof. intros m A ws [HB HW]. split; [exact HB|]. rewrite u64s_length, Nat2Z.inj_mul in HW. exact HW. Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8).
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8).
+ rewrite Z.mod_pow2_bits_low, Z.lor_spec, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
+ rewrite Z.mod_pow2_bits_high by lia. symmetry. apply (testbit_high_false _ 8); lia.
- replace (Z.lor (bv_unsigned b) (bytes_le_to_Z bs ≪ 8) ≫ 8) with (bytes_le_to_Z bs); [exact IH|].
rewrite Z.shiftr_lor, Z.shiftr_shiftl_l by lia. cbn [Z.sub Z.pos_sub]. rewrite Z.shiftl_0_r.
rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.

Lemma bytes_regroup4 : forall n (bs : list byte), length bs = (4 * n)%nat -> exists ws, u32s ws = bs /\ length ws = n.
Proof.
induction n as [|n IH]; intros bs H.
- exists []. destruct bs; [split; reflexivity| cbn in H; lia].
- destruct bs as [|b0 [|b1 [|b2 [|b3 bs']]]]; cbn in H; try lia.
destruct (IH bs' ltac:(lia)) as (ws & E & L).
exists (le_bytes_to_word [b0; b1; b2; b3] :: ws). cbn [u32s length]. rewrite E, L. split; [|reflexivity].
change (b0 :: b1 :: b2 :: b3 :: bs') with ([b0; b1; b2; b3] ++ bs'). f_equal.
unfold le4, le_bytes_to_word. rewrite unsigned_lit.
2:{ pose proof (bytes_le_to_Z_nonneg [b0; b1; b2; b3]). pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3]) as X. cbn [length Z.of_nat Z.mul Pos.mul Pos.of_succ_nat Pos.succ] in X. lia. }
apply (Z_to_le_bytes_of_bytes [b0; b1; b2; b3]).
Qed.

Lemma bytes_regroup8 : forall n (bs : list byte), length bs = (8 * n)%nat -> exists ws, u64s ws = bs /\ length ws = n.
Proof.
induction n as [|n IH]; intros bs H.
- exists []. destruct bs; [split; reflexivity| cbn in H; lia].
- destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 bs']]]]]]]]; cbn in H; try lia.
destruct (IH bs' ltac:(lia)) as (ws & E & L).
exists (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7] :: ws). cbn [u64s length]. rewrite E, L. split; [|reflexivity].
change (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs') with ([b0; b1; b2; b3; b4; b5; b6; b7] ++ bs'). f_equal.
unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite unsigned_lit.
2:{ pose proof (bytes_le_to_Z_nonneg [b0; b1; b2; b3; b4; b5; b6; b7]). pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3; b4; b5; b6; b7]) as X. cbn [length Z.of_nat Z.mul Pos.mul Pos.of_succ_nat Pos.succ] in X. lia. }
apply (Z_to_le_bytes_of_bytes [b0; b1; b2; b3; b4; b5; b6; b7]).
Qed.

Lemma u32arr_chunk : forall m A ws n, u32arr asegs m A ws -> Z.of_nat (length ws) = n ->
rw_cells asegs m A [CB (Z.to_nat (n * 4)) (u32s ws)].
Proof.
intros m A ws n H Hl. replace (Z.to_nat (n * 4)) with (length (u32s ws)) by (rewrite u32s_length; lia).
apply rw_cells_of_u8arr. destruct H as [HB HW]. split; [exact HB|]. rewrite u32s_length, Nat2Z.inj_mul. exact HW.
Qed.
Lemma u64arr_chunk : forall m A ws n, u64arr asegs m A ws -> Z.of_nat (length ws) = n ->
rw_cells asegs m A [CB (Z.to_nat (n * 8)) (u64s ws)].
Proof.
intros m A ws n H Hl. replace (Z.to_nat (n * 8)) with (length (u64s ws)) by (rewrite u64s_length; lia).
apply rw_cells_of_u8arr. destruct H as [HB HW]. split; [exact HB|]. rewrite u64s_length, Nat2Z.inj_mul. exact HW.
Qed.
Lemma chunk_u32arr : forall m A ws junk n k, rw_cells asegs m A [CB k (u32s ws ++ junk)] -> k = Z.to_nat (n * 4) -> 0 <= n ->
(length ws <= Z.to_nat n)%nat -> exists ws', u32arr asegs m A (ws ++ ws') /\ Z.of_nat (length (ws ++ ws')) = n.
Proof.
intros m A ws junk n k H -> Hn Hle. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [LEN _]. rewrite app_length, u32s_length in LEN.
destruct (bytes_regroup4 (Z.to_nat n - length ws) junk ltac:(lia)) as (ws' & E & L).
exists ws'. split.
- apply u8arr_of_rw_cells in H. rewrite <- E, <- u32s_app in H. destruct H as [HB HW]. split; [exact HB|].
rewrite u32s_length, Nat2Z.inj_mul in HW. exact HW.
- rewrite app_length. lia.
Qed.
Lemma chunk_u64arr : forall m A ws junk n k, rw_cells asegs m A [CB k (u64s ws ++ junk)] -> k = Z.to_nat (n * 8) -> 0 <= n ->
(length ws <= Z.to_nat n)%nat -> exists ws', u64arr asegs m A (ws ++ ws') /\ Z.of_nat (length (ws ++ ws')) = n.
Proof.
intros m A ws junk n k H -> Hn Hle. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [LEN _]. rewrite app_length, u64s_length in LEN.
destruct (bytes_regroup8 (Z.to_nat n - length ws) junk ltac:(lia)) as (ws' & E & L).
exists ws'. split.
- apply u8arr_of_rw_cells in H. rewrite <- E, <- u64s_app in H. destruct H as [HB HW]. split; [exact HB|].
rewrite u64s_length, Nat2Z.inj_mul in HW. exact HW.
- rewrite app_length. lia.
Qed.

Lemma u32arr_u8 : forall m A ws, u32arr asegs m A ws -> u8arr asegs m A (u32s ws).
Proof. intros m A ws [HB HW]. split; [exact HB|]. rewrite u32s_length, Nat2Z.inj_mul. exact HW. Qed.
Lemma u8_u32arr : forall m A ws, u8arr asegs m A (u32s ws) -> u32arr asegs m A ws.
Proof. intros m A ws [HB HW]. split; [exact HB|]. rewrite u32s_length, Nat2Z.inj_mul in HW. exact HW. Qed.
Lemma u64arr_u8 : forall m A ws, u64arr asegs m A ws -> u8arr asegs m A (u64s ws).
Proof. intros m A ws [HB HW]. split; [exact HB|]. rewrite u64s_length, Nat2Z.inj_mul. exact HW. Qed.
Lemma u8_u64arr : forall m A ws, u8arr asegs m A (u64s ws) -> u64arr asegs m A ws.
Proof. intros m A ws [HB HW]. split; [exact HB|]. rewrite u64s_length, Nat2Z.inj_mul in HW. exact HW. Qed.
