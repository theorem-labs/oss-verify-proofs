(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMow. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoSL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma mod_pow2_mod_pow2 : forall z a b, 0 <= a <= b -> (z mod 2^b) mod 2^a = z mod 2^a.
Proof.
intros z a b H. replace (2^b) with (2^a * 2^(b-a)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; lia).
rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. apply Z.pow_nonzero; lia.
Qed.

Lemma b8_unsigned : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma b8_eqm : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y E. apply bv_eq. rewrite !b8_unsigned. exact E. Qed.

Lemma Z_to_le_bytes_S : forall n z, Z_to_le_bytes (S n) z = Z_to_bv 8 z :: Z_to_le_bytes n (Z.shiftr z 8).
Proof. reflexivity. Qed.

Lemma Z_to_le_bytes_eqm : forall n x y, x mod 2^(8 * Z.of_nat n) = y mod 2^(8 * Z.of_nat n) ->
Z_to_le_bytes n x = Z_to_le_bytes n y.
Proof.
intros n x y E. rewrite <- (Z_to_le_bytes_mod n x (8 * Z.of_nat n)), <- (Z_to_le_bytes_mod n y (8 * Z.of_nat n)) by lia.
rewrite E. reflexivity.
Qed.

Lemma le8_lit : forall z, le8 (Z_to_bv 64 z) = Z_to_le_bytes 8 z.
Proof.
intros z. unfold le8, word_to_le_bytes. rewrite unsigned_lit_wrap. apply Z_to_le_bytes_eqm.
apply (mod_pow2_mod_pow2 z (8 * Z.of_nat 8) 64). cbn; lia.
Qed.
Lemma le4_lit : forall z, le4 (Z_to_bv 64 z) = Z_to_le_bytes 4 z.
Proof.
intros z. unfold le4. rewrite unsigned_lit_wrap. apply Z_to_le_bytes_eqm.
apply (mod_pow2_mod_pow2 z (8 * Z.of_nat 4) 64). cbn; lia.
Qed.
Lemma le2_lit : forall z, le2 (Z_to_bv 64 z) = Z_to_le_bytes 2 z.
Proof.
intros z. unfold le2. rewrite unsigned_lit_wrap. apply Z_to_le_bytes_eqm.
apply (mod_pow2_mod_pow2 z (8 * Z.of_nat 2) 64). cbn; lia.
Qed.
Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
intros z. unfold le1. rewrite unsigned_lit_wrap. cbn [Z_to_le_bytes]. f_equal. apply b8_eqm.
apply (mod_pow2_mod_pow2 z 8 64). lia.
Qed.

Lemma le4_eqm : forall x y, x mod 2^32 = y mod 2^32 -> le4 (Z_to_bv 64 x) = le4 (Z_to_bv 64 y).
Proof. intros x y E. rewrite !le4_lit. apply Z_to_le_bytes_eqm. exact E. Qed.

Lemma Z_to_le_bytes_app : forall n k a b, 0 <= a < 2^(8 * Z.of_nat n) ->
Z_to_le_bytes (n + k) (a + 2^(8 * Z.of_nat n) * b) = Z_to_le_bytes n a ++ Z_to_le_bytes k b.
Proof.
induction n as [|n IH]; intros k a b Ha.
- cbn [Z.of_nat Z.mul Nat.add app Z_to_le_bytes] in *. rewrite Z.pow_0_r in *. f_equal. lia.
- cbn [Nat.add]. rewrite !Z_to_le_bytes_S. cbn [app].
assert (P8 : 2 ^ (8 * Z.of_nat (S n)) = 2 ^ (8 * Z.of_nat n) * 256).
{ replace (8 * Z.of_nat (S n)) with (8 * Z.of_nat n + 8) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
assert (NN : 0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
rewrite P8 in Ha |- *.
f_equal.
+ apply b8_eqm. replace (a + 2 ^ (8 * Z.of_nat n) * 256 * b) with (a + (2 ^ (8 * Z.of_nat n) * b) * 256) by lia.
rewrite Z_mod_plus_full. reflexivity.
+ rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
replace (a + 2 ^ (8 * Z.of_nat n) * 256 * b) with ((2 ^ (8 * Z.of_nat n) * b) * 256 + a) by lia.
rewrite Z.div_add_l by lia. rewrite Z.add_comm. apply IH.
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma le8_split32 : forall lo hi,
le8 (Z_to_bv 64 (lo mod 2^32 + 2^32 * hi)) = le4 (Z_to_bv 64 lo) ++ le4 (Z_to_bv 64 hi).
Proof.
intros lo hi. rewrite le8_lit, !le4_lit.
change 8%nat with (4 + 4)%nat. change (2^32) with (2^(8 * Z.of_nat 4)).
rewrite Z_to_le_bytes_app by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
f_equal. apply Z_to_le_bytes_eqm. apply Z.mod_mod. apply Z.pow_nonzero; lia.
Qed.

Lemma pair8_lo : forall a b, (a mod 256 + 256 * b) mod 256 = a mod 256.
Proof. intros. rewrite (Z.mul_comm 256 b), Z_mod_plus_full. apply Z.mod_mod. lia. Qed.
Lemma pair8_hi : forall a b, (a mod 256 + 256 * b) / 256 = b.
Proof.
intros. rewrite (Z.mul_comm 256 b), Z_div_plus_full by lia.
rewrite Z.div_small; [lia|]. apply Z.mod_pos_bound. lia.
Qed.

Lemma bv_swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. reflexivity. Qed.

Lemma bv_swrap8_eq : forall z, bv_swrap 8 z = (z + 2^7) mod 2^8 - 2^7.
Proof. intros z. reflexivity. Qed.

Lemma sx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, bv_swrap32_eq.
change (2^64) with 18446744073709551616. change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
Z.div_mod_to_equations. nia.
Qed.

Lemma zx32_small : forall e, 0 <= e < 2^32 -> zx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof. intros e He. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma sx32_u32_high : forall e, 2^31 <= e < 2^32 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 (e - 2^32).
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit by lia. rewrite bv_swrap32_eq.
change (2^64) with 18446744073709551616. change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
Z.div_mod_to_equations. nia.
Qed.

Lemma zxb_b8 : forall v, zxb (Z_to_bv 8 v) = Z_to_bv 64 (v mod 256).
Proof. intros v. unfold zxb. rewrite b8_unsigned. reflexivity. Qed.
Lemma sxb_b8 : forall v, -128 <= v < 128 -> sxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sxb. rewrite Z_to_bv_signed, bv_swrap8_eq. f_equal.
change (2^8) with 256. change (2^7) with 128. Z.div_mod_to_equations. lia.
Qed.

Lemma sx16_any : forall e, sx16 (Z_to_bv 64 e) = Z_to_bv 64 (bv_swrap 16 e).
Proof.
intros e. unfold sx16. f_equal. rewrite unsigned_lit_wrap. apply bv_swrap_congr.
unfold bv_wrap. apply (mod_pow2_mod_pow2 e 16 64). lia.
Qed.

Lemma bytes_le_to_Z_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
apply Z.lor_nonneg. split; [apply (bv_unsigned_in_range 8 b)| apply Z.shiftl_nonneg; exact IH].
Qed.
Lemma Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
rewrite lor_shiftl8_add by (first [lia | apply bytes_le_to_Z_nonneg]).
rewrite <- (Z.mod_small (bv_unsigned b) 256) at 1 2 by lia.
f_equal.
- apply bv_eq. rewrite b8_unsigned, pair8_lo. apply Z.mod_small. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite pair8_hi. exact IH.
Qed.
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof. intros bs H. rewrite le4_lit, <- H. apply Z_to_le_bytes_of_bytes. Qed.
Lemma le2_of_bytes : forall bs : list byte, length bs = 2%nat -> le2 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof. intros bs H. rewrite le2_lit, <- H. apply Z_to_le_bytes_of_bytes. Qed.
Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof. intros bs H. rewrite le8_lit, <- H. apply Z_to_le_bytes_of_bytes. Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma rw_cells_recast : forall m A cs cs',
rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
rw_cells segs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

Lemma rw_cells_recast' : forall m A cs cs',
rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
intros m A cs cs' H Hwf' Eb. eapply rw_cells_recast; [exact H| exact Hwf'| exact Eb|].
destruct H as [[Hwf _] _]. rewrite <- (cells_bytes_length cs Hwf), <- (cells_bytes_length cs' Hwf'), Eb. reflexivity.
Qed.

Lemma ro_cells_recast' : forall m A cs cs',
ro_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> ro_cells segs m A cs'.
Proof. intros m A cs cs' [Hwf Hb] Hwf' Eb. split; [exact Hwf'|]. rewrite Eb. exact Hb. Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <->
rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros m A cs1 cs2. unfold rw_cells, cells_at.
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

Lemma ro_cells_app : forall m A cs1 cs2,
ro_cells segs m A (cs1 ++ cs2) <->
ro_cells segs m A cs1 /\ ro_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros m A cs1 cs2. unfold ro_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, bytes_at_app. split.
- intros [[W1 W2] [B1 B2]]. rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros [[W1 B1] [W2 B2]]. rewrite (cells_bytes_length cs1 W1). tauto.
Qed.

Lemma rw_cells_as_CB : forall m A cs,
rw_cells segs m A cs -> rw_cells segs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
intros m A cs H. pose proof H as [[Hwf _] _]. eapply rw_cells_recast; [exact H| | |].
- cbn. split; [apply cells_bytes_length; exact Hwf| exact I].
- cbn. apply app_nil_r.
- cbn. lia.
Qed.

End WithSegs.

Ltac cell_of_bytes bs ::=
lazymatch bs with
| le8 ?v => constr:(C8 v)
| le4 ?v => constr:(C4 v)
| le2 ?v => constr:(C2 v)
| [?b] => constr:(C1 b)
| le1 (zxb ?b) => constr:(C1 b)
| le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
end. Ltac mkr__cell_of_bytes_1 bs := lazymatch bs with
| le8 ?v => constr:(C8 v)
| le4 ?v => constr:(C4 v)
| le2 ?v => constr:(C2 v)
| [?b] => constr:(C1 b)
| le1 (zxb ?b) => constr:(C1 b)
| le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
end.

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with ([Z_to_bv 8 z]); mem_after_store
end).

Ltac stepz := step; fix_lit_store.
