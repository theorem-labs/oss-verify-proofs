(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec L5Defs L5Core PmModelFacts PmCertKitG AxSymExec3 PeCRdValW.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module PECGLW.

Lemma land_mask a k : 0 <= k -> 0 <= a -> Z.land a (255 * 2 ^ k) = ((a / 2 ^ k) mod 256) * 2 ^ k.
Proof.
  intros Hk Ha.
  assert (M : 255 * 2 ^ k = Z.shiftl (Z.ones 8) k) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite M. set (c := Z.land a (Z.shiftl (Z.ones 8) k)).
  assert (C1 : Z.shiftr c k = (a / 2 ^ k) mod 256).
  { unfold c. rewrite Z.shiftr_land, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia. rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  assert (C2 : c mod 2 ^ k = 0).
  { rewrite <- Z.land_ones by lia. unfold c. rewrite <- Z.land_assoc.
    replace (Z.land (Z.shiftl (Z.ones 8) k) (Z.ones k)) with 0; [apply Z.land_0_r|].
    symmetry. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n k) as [L|L].
    - rewrite Z.shiftl_spec_low by lia. reflexivity.
    - rewrite (Z.ones_spec_high k n) by lia. apply Bool.andb_false_r. }
  assert (C0 : 0 <= c) by (unfold c; apply Z.land_nonneg; left; exact Ha).
  rewrite (Z.div_mod c (2 ^ k)) at 1 by lia. rewrite C2, Z.add_0_r. rewrite <- Z.shiftr_div_pow2 by lia. rewrite C1. lia.
Qed.
Lemma land_255 a : 0 <= a -> Z.land a 255 = a mod 256.
Proof. intros Ha. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma lor_lanes a t n : 0 <= n -> 0 <= a -> a mod 2 ^ n = 0 -> 0 <= t < 2 ^ n -> Z.lor a t = a + t.
Proof. intros H1 H2 H3 H4. exact (PECRVW.lor_disjoint a t n H1 H2 H3 H4). Qed.

Lemma shmask64 n : 0 <= n < 64 -> bv_unsigned (bv_and (Z_to_bv 64 n) (Z_to_bv 64 63)) = n.
Proof.
  intros Hn. rewrite bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite !Z.mod_small by lia. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma shmask32 n : 0 <= n < 32 -> bv_unsigned (bv_and (low32 (Z_to_bv 64 n)) (Z_to_bv 32 31)) = n.
Proof.
  intros Hn. rewrite bv_and_unsigned. unfold low32. rewrite bv_extract_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  rewrite !Z.mod_small by lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma low32_u (w : bv 64) : bv_unsigned (low32 w) = bv_unsigned w mod 2 ^ 32.
Proof. unfold low32. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. reflexivity. Qed.
Lemma sext32_u (v : bv 32) : bv_unsigned (sext 64 v) = (let r := bv_unsigned v in if r <? 2 ^ 31 then r else r + 2 ^ 64 - 2 ^ 32).
Proof.
  unfold sext. rewrite bv_sign_extend_unsigned.
  pose proof (bv_unsigned_in_range 32 v) as R. change (bv_modulus 32) with (2 ^ 32) in R.
  assert (S : bv_signed v = bv_swrap 32 (bv_unsigned v)) by (rewrite <- (Z_to_bv_signed 32 (bv_unsigned v)), Z_to_bv_bv_unsigned; reflexivity).
  rewrite S, (PECRVW.swrap32_cases _ R). cbv zeta. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.ltb_spec (bv_unsigned v) (2 ^ 31)) as [L|L].
  - apply Z.mod_small. lia.
  - replace (bv_unsigned v - 2 ^ 32) with ((bv_unsigned v + 2 ^ 64 - 2 ^ 32) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma signed_of_u (w : bv 64) : bv_signed w = (let u := bv_unsigned w in if u <? 2 ^ 63 then u else u - 2 ^ 64).
Proof.
  pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  rewrite <- (Z_to_bv_bv_unsigned 64 w) at 1. rewrite Z_to_bv_signed. cbv zeta.
  unfold bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 64) with (2 ^ 64). change (2 ^ 64 `div` 2) with (2 ^ 63).
  destruct (Z.ltb_spec (bv_unsigned w) (2 ^ 63)) as [L|L].
  - rewrite Z.mod_small by lia. lia.
  - replace (bv_unsigned w + 2 ^ 63) with ((bv_unsigned w + 2 ^ 63 - 2 ^ 64) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Section Ops.
Variable E : env.
Local Notation U e := (bv_unsigned (edenot E e)).
Lemma u_range e : 0 <= U e < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 (edenot E e)) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R. Qed.
Lemma u_lit z : 0 <= z < 2 ^ 64 -> U (ELit z) = z.
Proof. intros Hz. cbn [edenot]. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma u_or a b : U (EAlu ALU_OR a b) = Z.lor (U a) (U b).
Proof. cbn [edenot]. unfold alu64, alu. apply bv_or_unsigned. Qed.
Lemma u_and a b : U (EAlu ALU_AND a b) = Z.land (U a) (U b).
Proof. cbn [edenot]. unfold alu64, alu. apply bv_and_unsigned. Qed.
Lemma u_add a b : U (EAlu ALU_ADD a b) = (U a + U b) mod 2 ^ 64.
Proof. cbn [edenot]. unfold alu64, alu. rewrite bv_add_unsigned. reflexivity. Qed.
Lemma u_srl a n : 0 <= n < 64 -> U (EAlu ALU_SRL a (ELit n)) = U a / 2 ^ n.
Proof. intros Hn. cbn [edenot]. unfold alu64, alu. rewrite bv_shiftr_unsigned, shmask64 by lia. apply Z.shiftr_div_pow2. lia. Qed.
Lemma u_sll a n : 0 <= n < 64 -> U (EAlu ALU_SLL a (ELit n)) = (U a * 2 ^ n) mod 2 ^ 64.
Proof. intros Hn. cbn [edenot]. unfold alu64, alu. rewrite bv_shiftl_unsigned, shmask64 by lia. unfold bv_wrap. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma u_mul c a : 0 <= c < 2 ^ 64 -> U (EMd M_MUL (ELit c) a) = (c * U a) mod 2 ^ 64.
Proof. intros Hc. cbn [edenot]. unfold mul_div. cbv zeta. rewrite bv_mul_unsigned, Z_to_bv_unsigned, (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64); lia). reflexivity. Qed.
Lemma u_srlw a n : 1 <= n < 32 -> U (EAluw ALU_SRL a (ELit n)) = (U a mod 2 ^ 32) / 2 ^ n.
Proof.
  intros Hn. cbn [edenot]. rewrite sext32_u. unfold alu32, alu. rewrite bv_shiftr_unsigned, shmask32, low32_u by lia.
  rewrite Z.shiftr_div_pow2 by lia. cbv zeta.
  assert (B : 0 <= (U a mod 2 ^ 32) / 2 ^ n < 2 ^ 31).
  { pose proof (Z.mod_pos_bound (U a) (2 ^ 32) ltac:(lia)) as M. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. assert (2 ^ 32 <= 2 ^ n * 2 ^ 31) by (rewrite <- Z.pow_add_r by lia; apply Z.pow_le_mono_r; lia). lia. }
  destruct (Z.ltb_spec ((U a mod 2 ^ 32) / 2 ^ n) (2 ^ 31)); [reflexivity| lia].
Qed.
Lemma u_sllw a n : 0 <= n < 32 -> U (EAluw ALU_SLL a (ELit n)) = (let r := (U a * 2 ^ n) mod 2 ^ 32 in if r <? 2 ^ 31 then r else r + 2 ^ 64 - 2 ^ 32).
Proof.
  intros Hn. cbn [edenot]. rewrite sext32_u. unfold alu32, alu. rewrite bv_shiftl_unsigned, shmask32, low32_u by lia.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Zmult_mod_idemp_l. reflexivity.
Qed.
Lemma u_extu a (k : nat) : U (EExt false 0 k a) = (U a mod 2 ^ (8 * Z.of_nat k)) mod 2 ^ 64.
Proof.
  cbn [edenot]. unfold ext_val, ext_Z. cbv zeta. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma u_ext1s a : U (EExt true 0 1 a) = (let r := U a mod 2 ^ 8 in if r <? 2 ^ 7 then r else r + 2 ^ 64 - 2 ^ 8).
Proof.
  cbn [edenot]. unfold ext_val, ext_Z. cbv zeta. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8). change (8 * N.of_nat 1)%N with 8%N.
  rewrite Z_to_bv_unsigned. pose proof (Z.mod_pos_bound (U a) (2 ^ 8) ltac:(lia)) as M. set (r := U a mod 2 ^ 8) in *.
  unfold bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 8) with (2 ^ 8). change (2 ^ 8 `div` 2) with (2 ^ 7). change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.ltb_spec r (2 ^ 7)) as [L|L].
  - rewrite (Z.mod_small (r + 2 ^ 7)) by lia. replace (r + 2 ^ 7 - 2 ^ 7) with r by lia. apply Z.mod_small. lia.
  - replace (r + 2 ^ 7) with ((r + 2 ^ 7 - 2 ^ 8) + 1 * 2 ^ 8) by lia. rewrite Z.mod_add, (Z.mod_small (r + 2 ^ 7 - 2 ^ 8)) by lia.
    replace (r + 2 ^ 7 - 2 ^ 8 - 2 ^ 7) with ((r + 2 ^ 64 - 2 ^ 8) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma u_ext4s a : U (EExt true 0 4 a) = (let r := U a mod 2 ^ 32 in if r <? 2 ^ 31 then r else r + 2 ^ 64 - 2 ^ 32).
Proof.
  cbn [edenot]. unfold ext_val, ext_Z. cbv zeta. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). change (8 * N.of_nat 4)%N with 32%N.
  rewrite Z_to_bv_unsigned. pose proof (Z.mod_pos_bound (U a) (2 ^ 32) ltac:(lia)) as M.
  rewrite (PECRVW.swrap32_cases _ M). set (r := U a mod 2 ^ 32) in *. cbv zeta.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.ltb_spec r (2 ^ 31)) as [L|L].
  - apply Z.mod_small. lia.
  - replace (r - 2 ^ 32) with ((r + 2 ^ 64 - 2 ^ 32) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma u_slt0 a : U (EAlu ALU_SLT a (ELit 0)) = (if U a <? 2 ^ 63 then 0 else 1).
Proof.
  cbn [edenot]. unfold alu64, alu, bv_lts. rewrite (signed_of_u (edenot E a)). cbv zeta.
  change (bv_signed (Z_to_bv 64 0)) with 0.
  destruct (Z.ltb_spec (U a) (2 ^ 63)) as [L|L].
  - pose proof (u_range a). destruct (Z.ltb_spec (U a) 0); [lia| reflexivity].
  - pose proof (u_range a). destruct (Z.ltb_spec (U a - 2 ^ 64) 0); [reflexivity| lia].
Qed.
Lemma u_sra48 a : U a < 2 ^ 63 -> U (EAlu ALU_SRA a (ELit 48)) = U a / 2 ^ 48.
Proof.
  intros Ha. pose proof (u_range a) as R. cbn [edenot]. unfold alu64, alu. rewrite PECRVW.and48_63.
  assert (S : bv_signed (edenot E a `ashiftr` Z_to_bv 64 48) = U a / 2 ^ 48).
  { rewrite bv_ashiftr_signed, Z_to_bv_unsigned. change (bv_wrap 64 48) with 48. rewrite (signed_of_u (edenot E a)). cbv zeta.
    destruct (Z.ltb_spec (U a) (2 ^ 63)); [|lia]. rewrite Z.shiftr_div_pow2 by lia.
    unfold bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 64) with (2 ^ 64). change (2 ^ 64 `div` 2) with (2 ^ 63).
    assert (0 <= U a / 2 ^ 48 < 2 ^ 15) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    rewrite Z.mod_small by lia. lia. }
  rewrite (signed_of_u _) in S. cbv zeta in S.
  destruct (Z.ltb_spec (bv_unsigned (edenot E a `ashiftr` Z_to_bv 64 48)) (2 ^ 63)) as [L|L]; [exact S|].
  exfalso. assert (0 <= U a / 2 ^ 48) by (apply Z.div_pos; lia).
  pose proof (bv_unsigned_in_range 64 (edenot E a `ashiftr` Z_to_bv 64 48)) as R2. change (bv_modulus 64) with (2 ^ 64) in R2. lia.
Qed.
End Ops.

Section Bytes.
Variables b0 b1 b2 b3 b4 b5 b6 b7 : Z.
Hypothesis HB : 0 <= b0 < 256 /\ 0 <= b1 < 256 /\ 0 <= b2 < 256 /\ 0 <= b3 < 256 /\ 0 <= b4 < 256 /\ 0 <= b5 < 256 /\ 0 <= b6 < 256 /\ 0 <= b7 < 256.
Definition xle : Z := b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3 + 2 ^ 32 * b4 + 2 ^ 40 * b5 + 2 ^ 48 * b6 + 2 ^ 56 * b7.
Lemma xle_range : 0 <= xle < 2 ^ 64. Proof. unfold xle. lia. Qed.

Lemma div_eq q r m v : 0 < m -> v = q * m + r -> 0 <= r < m -> v / m = q.
Proof. intros Hm -> Hr. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. Qed.
Lemma mod_eq q r m v : 0 < m -> v = q * m + r -> 0 <= r < m -> v mod m = r.
Proof. intros Hm -> Hr. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia. Qed.

Lemma xd8 : xle / 2 ^ 8 = b1 + 2 ^ 8 * b2 + 2 ^ 16 * b3 + 2 ^ 24 * b4 + 2 ^ 32 * b5 + 2 ^ 40 * b6 + 2 ^ 48 * b7.
Proof. apply (div_eq _ b0); [lia| unfold xle; lia| lia]. Qed.
Lemma xd16 : xle / 2 ^ 16 = b2 + 2 ^ 8 * b3 + 2 ^ 16 * b4 + 2 ^ 24 * b5 + 2 ^ 32 * b6 + 2 ^ 40 * b7.
Proof. apply (div_eq _ (b0 + 2 ^ 8 * b1)); [lia| unfold xle; lia| lia]. Qed.
Lemma xd24 : xle / 2 ^ 24 = b3 + 2 ^ 8 * b4 + 2 ^ 16 * b5 + 2 ^ 24 * b6 + 2 ^ 32 * b7.
Proof. apply (div_eq _ (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2)); [lia| unfold xle; lia| lia]. Qed.
Lemma xd32 : xle / 2 ^ 32 = b4 + 2 ^ 8 * b5 + 2 ^ 16 * b6 + 2 ^ 24 * b7.
Proof. apply (div_eq _ (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3)); [lia| unfold xle; lia| lia]. Qed.
Lemma xd40 : xle / 2 ^ 40 = b5 + 2 ^ 8 * b6 + 2 ^ 16 * b7.
Proof. apply (div_eq _ (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3 + 2 ^ 32 * b4)); [lia| unfold xle; lia| lia]. Qed.
Lemma xd48 : xle / 2 ^ 48 = b6 + 2 ^ 8 * b7.
Proof. apply (div_eq _ (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3 + 2 ^ 32 * b4 + 2 ^ 40 * b5)); [lia| unfold xle; lia| lia]. Qed.
Lemma xd56 : xle / 2 ^ 56 = b7.
Proof. apply (div_eq _ (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3 + 2 ^ 32 * b4 + 2 ^ 40 * b5 + 2 ^ 48 * b6)); [lia| unfold xle; lia| lia]. Qed.
Lemma xm8 : xle mod 2 ^ 8 = b0.
Proof. apply (mod_eq (b1 + 2 ^ 8 * b2 + 2 ^ 16 * b3 + 2 ^ 24 * b4 + 2 ^ 32 * b5 + 2 ^ 40 * b6 + 2 ^ 48 * b7)); [lia| unfold xle; lia| lia]. Qed.
Lemma xm16 : xle mod 2 ^ 16 = b0 + 2 ^ 8 * b1.
Proof. apply (mod_eq (b2 + 2 ^ 8 * b3 + 2 ^ 16 * b4 + 2 ^ 24 * b5 + 2 ^ 32 * b6 + 2 ^ 40 * b7)); [lia| unfold xle; lia| lia]. Qed.
Lemma xm32 : xle mod 2 ^ 32 = b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3.
Proof. apply (mod_eq (b4 + 2 ^ 8 * b5 + 2 ^ 16 * b6 + 2 ^ 24 * b7)); [lia| unfold xle; lia| lia]. Qed.

Lemma lane_pick v k b hi : 0 <= k -> 0 <= v -> v / 2 ^ k = b + 2 ^ 8 * hi -> 0 <= b < 256 -> 0 <= hi -> Z.land v (255 * 2 ^ k) = b * 2 ^ k.
Proof.
  intros Hk Hv Hd Hb Hhi. rewrite land_mask by lia. rewrite Hd. f_equal. apply (mod_eq hi); lia.
Qed.

Variable E : env.
Variable e : expr.
Hypothesis He : bv_unsigned (edenot E e) = xle.
Local Notation U a := (bv_unsigned (edenot E a)).

Ltac to_u := apply bv_eq; rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).

Lemma val_U : edenot E (EExt false 0 1 e) = Z_to_bv 64 b0.
Proof.
  apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite u_extu, He. change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8). rewrite xm8. apply Z.mod_small. lia.
Qed.

Definition wi : Z := if b0 <? 128 then b0 else b0 + 2 ^ 64 - 2 ^ 8.
Lemma val_i : edenot E (EExt true 0 1 e) = Z_to_bv 64 wi.
Proof.
  apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); unfold wi; destruct (b0 <? 128); lia).
  rewrite u_ext1s, He. cbv zeta. rewrite xm8. unfold wi. change (2 ^ 7) with 128. reflexivity.
Qed.

Definition wI : Z := b0 * 2 ^ 56 + b1 * 2 ^ 48 + b0 * 2 ^ 40.
Lemma val_I : edenot E (EMd M_MUL (ELit 72058693549555712) (EExt false 0 2 e)) = Z_to_bv 64 wI.
Proof.
  apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); unfold wI; lia).
  rewrite u_mul by lia. rewrite u_extu, He. change (2 ^ (8 * Z.of_nat 2)) with (2 ^ 16). rewrite xm16.
  rewrite (Z.mod_small (b0 + 2 ^ 8 * b1)) by lia. unfold wI.
  apply (mod_eq b1); lia.
Qed.

Definition be4 : Z := b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3.
Definition wl : Z := if b0 <? 128 then be4 else be4 + 2 ^ 64 - 2 ^ 32.
Lemma val_l :
  edenot E (EAlu Instr.ALU_OR (EAlu Instr.ALU_OR (EAluw Instr.ALU_SLL (EExt true 0 4 e) (ELit 24)) (EMd Instr.M_MUL (ELit 256) (EAlu Instr.ALU_AND (EExt true 0 4 e) (ELit 65280))))
              (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL (EExt true 0 4 e) (ELit 8)) (ELit 65280)) (EAluw Instr.ALU_SRL (EExt true 0 4 e) (ELit 24))))
  = Z_to_bv 64 wl.
Proof.
  assert (WL : 0 <= wl < 2 ^ 64) by (unfold wl, be4; destruct (b0 <? 128); lia).
  apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  set (sx := EExt true 0 4 e).
  assert (SX : U sx = (if b3 <? 128 then xle mod 2 ^ 32 else xle mod 2 ^ 32 + 2 ^ 64 - 2 ^ 32)).
  { unfold sx. rewrite u_ext4s, He. cbv zeta. rewrite xm32.
    destruct (Z.ltb_spec b3 128) as [L|L]; destruct (Z.ltb_spec (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3) (2 ^ 31)) as [L'|L']; try reflexivity; exfalso; lia. }
  rewrite xm32 in SX.
  pose proof (u_range E sx) as SR.

  assert (T1 : U (EAluw Instr.ALU_SLL sx (ELit 24)) = (if b0 <? 128 then b0 * 2 ^ 24 else b0 * 2 ^ 24 + 2 ^ 64 - 2 ^ 32)).
  { rewrite u_sllw by lia. cbv zeta.
    assert (M : (U sx * 2 ^ 24) mod 2 ^ 32 = b0 * 2 ^ 24).
    { rewrite SX. destruct (b3 <? 128).
      - apply (mod_eq (b1 + 2 ^ 8 * b2 + 2 ^ 16 * b3)); lia.
      - apply (mod_eq (b1 + 2 ^ 8 * b2 + 2 ^ 16 * b3 + 2 ^ 56 - 2 ^ 24)); lia. }
    rewrite M. destruct (Z.ltb_spec b0 128) as [L|L]; destruct (Z.ltb_spec (b0 * 2 ^ 24) (2 ^ 31)); try reflexivity; exfalso; lia. }
  assert (T2 : U (EMd Instr.M_MUL (ELit 256) (EAlu Instr.ALU_AND sx (ELit 65280))) = b1 * 2 ^ 16).
  { rewrite u_mul by lia. rewrite u_and, u_lit by lia. change 65280 with (255 * 2 ^ 8).
    rewrite (lane_pick (U sx) 8 b1 (if b3 <? 128 then b2 + 2 ^ 8 * b3 else b2 + 2 ^ 8 * b3 + 2 ^ 48 - 2 ^ 16)); [| lia| lia| | lia| destruct (b3 <? 128); lia].
    - rewrite Z.mod_small by lia. lia.
    - rewrite SX. destruct (b3 <? 128); [apply (div_eq _ b0); lia| apply (div_eq _ b0); lia]. }
  assert (T3 : U (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL sx (ELit 8)) (ELit 65280)) = b2 * 2 ^ 8).
  { rewrite u_and, u_srl, u_lit by lia. change 65280 with (255 * 2 ^ 8).
    assert (D0 : 0 <= U sx / 2 ^ 8) by (apply Z.div_pos; lia).
    rewrite (lane_pick (U sx / 2 ^ 8) 8 b2 (if b3 <? 128 then b3 else b3 + 2 ^ 40 - 2 ^ 8)); [reflexivity| lia| exact D0| | lia| destruct (b3 <? 128); lia].
    rewrite Z.div_div by lia. change (2 ^ 8 * 2 ^ 8) with (2 ^ 16). rewrite SX.
    destruct (b3 <? 128); [apply (div_eq _ (b0 + 2 ^ 8 * b1)); lia| apply (div_eq _ (b0 + 2 ^ 8 * b1)); lia]. }
  assert (T4 : U (EAluw Instr.ALU_SRL sx (ELit 24)) = b3).
  { rewrite u_srlw by lia. rewrite SX.
    assert (M : (if b3 <? 128 then b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3 else b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3 + 2 ^ 64 - 2 ^ 32) mod 2 ^ 32
                = b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3).
    { destruct (b3 <? 128); [rewrite Z.mod_small by lia; lia| apply (mod_eq (2 ^ 32 - 1)); lia]. }
    rewrite M. apply (div_eq _ (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2)); lia. }
  rewrite !u_or. rewrite T1, T2, T3, T4.
  rewrite (lor_lanes _ (b1 * 2 ^ 16) 24); [| lia| destruct (b0 <? 128); lia| destruct (b0 <? 128); [apply (mod_eq b0); lia| apply (mod_eq (b0 + 2 ^ 40 - 2 ^ 8)); lia]| lia].
  rewrite (lor_lanes _ b3 8); [| lia| lia| apply (mod_eq b2); lia| lia].
  rewrite (lor_lanes _ (b2 * 2 ^ 8 + b3) 16); [| lia| destruct (b0 <? 128); lia| | lia].
  2:{ destruct (b0 <? 128); [apply (mod_eq (b0 * 2 ^ 8 + b1)); lia| apply (mod_eq (b0 * 2 ^ 8 + b1 + 2 ^ 48 - 2 ^ 16)); lia]. }
  unfold wl, be4. destruct (b0 <? 128); lia.
Qed.

Definition be8 : Z := b0 * 2 ^ 56 + b1 * 2 ^ 48 + b2 * 2 ^ 40 + b3 * 2 ^ 32 + b4 * 2 ^ 24 + b5 * 2 ^ 16 + b6 * 2 ^ 8 + b7.
Lemma val_L :
  edenot E (EAlu Instr.ALU_OR (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 72057594037927936) e) (EMd Instr.M_MUL (ELit 1099511627776) (EAlu Instr.ALU_AND e (ELit 65280))))
                (EAlu Instr.ALU_OR (EMd Instr.M_MUL (ELit 16777216) (EAlu Instr.ALU_AND e (ELit 16711680))) (EMd Instr.M_MUL (ELit 4294967296) (EAluw Instr.ALU_SRL e (ELit 24)))))
              (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL e (ELit 24)) (ELit 16711680)) (EMd Instr.M_MUL (ELit 16777216) (EAluw Instr.ALU_SRL (EAlu Instr.ALU_SRL e (ELit 8)) (ELit 24))))
                (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL e (ELit 40)) (ELit 65280)) (EAlu Instr.ALU_SRL e (ELit 56)))))
  = Z_to_bv 64 be8.
Proof.
  assert (WL : 0 <= be8 < 2 ^ 64) by (unfold be8; lia).
  pose proof xle_range as XR.
  apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  assert (T1 : U (EMd Instr.M_MUL (ELit 72057594037927936) e) = b0 * 2 ^ 56).
  { rewrite u_mul, He by lia. apply (mod_eq (b1 + 2 ^ 8 * b2 + 2 ^ 16 * b3 + 2 ^ 24 * b4 + 2 ^ 32 * b5 + 2 ^ 40 * b6 + 2 ^ 48 * b7)); [lia| unfold xle; lia| lia]. }
  assert (T2 : U (EMd Instr.M_MUL (ELit 1099511627776) (EAlu Instr.ALU_AND e (ELit 65280))) = b1 * 2 ^ 48).
  { rewrite u_mul, u_and, u_lit, He by lia. change 65280 with (255 * 2 ^ 8).
    rewrite (lane_pick xle 8 b1 (b2 + 2 ^ 8 * b3 + 2 ^ 16 * b4 + 2 ^ 24 * b5 + 2 ^ 32 * b6 + 2 ^ 40 * b7)); [rewrite Z.mod_small by lia; lia| lia| lia| rewrite xd8; lia| lia| lia]. }
  assert (T3 : U (EMd Instr.M_MUL (ELit 16777216) (EAlu Instr.ALU_AND e (ELit 16711680))) = b2 * 2 ^ 40).
  { rewrite u_mul, u_and, u_lit, He by lia. change 16711680 with (255 * 2 ^ 16).
    rewrite (lane_pick xle 16 b2 (b3 + 2 ^ 8 * b4 + 2 ^ 16 * b5 + 2 ^ 24 * b6 + 2 ^ 32 * b7)); [rewrite Z.mod_small by lia; lia| lia| lia| rewrite xd16; lia| lia| lia]. }
  assert (T4 : U (EMd Instr.M_MUL (ELit 4294967296) (EAluw Instr.ALU_SRL e (ELit 24))) = b3 * 2 ^ 32).
  { rewrite u_mul, u_srlw, He by lia. rewrite xm32. rewrite (div_eq b3 (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2) (2 ^ 24)); [rewrite Z.mod_small by lia; lia| lia| lia| lia]. }
  assert (T5 : U (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL e (ELit 24)) (ELit 16711680)) = b5 * 2 ^ 16).
  { rewrite u_and, u_srl, u_lit, He by lia. change 16711680 with (255 * 2 ^ 16). rewrite xd24.
    rewrite (lane_pick _ 16 b5 (b6 + 2 ^ 8 * b7)); [reflexivity| lia| lia| apply (div_eq _ (b3 + 2 ^ 8 * b4)); lia| lia| lia]. }
  assert (T6 : U (EMd Instr.M_MUL (ELit 16777216) (EAluw Instr.ALU_SRL (EAlu Instr.ALU_SRL e (ELit 8)) (ELit 24))) = b4 * 2 ^ 24).
  { rewrite u_mul, u_srlw, u_srl, He by lia. rewrite xd8.
    rewrite (mod_eq (b5 + 2 ^ 8 * b6 + 2 ^ 16 * b7) (b1 + 2 ^ 8 * b2 + 2 ^ 16 * b3 + 2 ^ 24 * b4) (2 ^ 32)); [| lia| lia| lia].
    rewrite (div_eq b4 (b1 + 2 ^ 8 * b2 + 2 ^ 16 * b3) (2 ^ 24)); [rewrite Z.mod_small by lia; lia| lia| lia| lia]. }
  assert (T7 : U (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL e (ELit 40)) (ELit 65280)) = b6 * 2 ^ 8).
  { rewrite u_and, u_srl, u_lit, He by lia. change 65280 with (255 * 2 ^ 8). rewrite xd40.
    rewrite (lane_pick _ 8 b6 b7); [reflexivity| lia| lia| apply (div_eq _ b5); lia| lia| lia]. }
  assert (T8 : U (EAlu Instr.ALU_SRL e (ELit 56)) = b7).
  { rewrite u_srl, He by lia. apply xd56. }
  rewrite !u_or, !u_add. rewrite T1, T2, T3, T4, T5, T6, T7, T8.
  rewrite (Z.mod_small (b0 * 2 ^ 56 + b1 * 2 ^ 48)) by lia. rewrite (Z.mod_small (b5 * 2 ^ 16 + b4 * 2 ^ 24)) by lia.
  rewrite (lor_lanes _ (b3 * 2 ^ 32) 40); [| lia| lia| apply (mod_eq b2); lia| lia].
  rewrite (lor_lanes _ (b2 * 2 ^ 40 + b3 * 2 ^ 32) 48); [| lia| lia| apply (mod_eq (b0 * 2 ^ 8 + b1)); lia| lia].
  rewrite (lor_lanes _ b7 8); [| lia| lia| apply (mod_eq b6); lia| lia].
  rewrite (lor_lanes _ (b6 * 2 ^ 8 + b7) 16); [| lia| lia| apply (mod_eq (b5 + b4 * 2 ^ 8)); lia| lia].
  rewrite (lor_lanes _ (b5 * 2 ^ 16 + b4 * 2 ^ 24 + (b6 * 2 ^ 8 + b7)) 32); [| lia| lia| apply (mod_eq (b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3)); lia| lia].
  unfold be8. lia.
Qed.
End Bytes.

Lemma slt0_of (E : env) (a : expr) (w : Z) : 0 <= w < 2 ^ 64 -> edenot E a = Z_to_bv 64 w ->
  bv_unsigned (edenot E (EAlu ALU_SLT a (ELit 0))) = (if w <? 2 ^ 63 then 0 else 1).
Proof.
  intros Hw Ha. rewrite u_slt0, Ha, Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). reflexivity.
Qed.
Lemma sra48_of (E : env) (a : expr) (w : Z) : 0 <= w < 2 ^ 63 -> edenot E a = Z_to_bv 64 w ->
  edenot E (EAlu ALU_SRA a (ELit 48)) = Z_to_bv 64 (w / 2 ^ 48).
Proof.
  intros Hw Ha. assert (0 <= w / 2 ^ 48 < 2 ^ 15) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite u_sra48; rewrite Ha, Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia); [reflexivity| lia].
Qed.

Lemma wI_shift b0 b1 : 0 <= b0 < 256 -> 0 <= b1 < 256 -> (b0 * 2 ^ 56 + b1 * 2 ^ 48 + b0 * 2 ^ 40) / 2 ^ 48 = b0 * 2 ^ 8 + b1.
Proof.
  intros H0 H1. replace (b0 * 2 ^ 56 + b1 * 2 ^ 48 + b0 * 2 ^ 40) with ((b0 * 2 ^ 8 + b1) * 2 ^ 48 + b0 * 2 ^ 40) by lia.
  rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Section Mem.
Variable segs : list MemImageType.Segment.
Definition lane (x : Z) (i : nat) : Z := (x / 2 ^ (8 * Z.of_nat i)) mod 256.
Lemma lane_range x i : 0 <= lane x i < 256.
Proof. unfold lane. apply Z.mod_pos_bound. lia. Qed.
Lemma le_bytes_seq n : forall z, Z_to_le_bytes n z = map (fun i : nat => Z_to_bv 8 (z / 2 ^ (8 * Z.of_nat i))) (seq 0 n).
Proof.
  induction n as [|n IH]; intros z; [reflexivity|].
  cbn [Z_to_le_bytes seq map]. rewrite <- seq_shift, map_map. f_equal.
  - change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. reflexivity.
  - rewrite IH. apply map_ext. intros i. f_equal. rewrite Z.shiftr_div_pow2, Z.div_div by lia. f_equal.
    rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma nth_map_seq (f : nat -> Z) len : forall start i, (i < len)%nat -> nth i (map f (seq start len)) 0 = f (start + i)%nat.
Proof.
  induction len as [|len IH]; intros start i Hi; [lia|]. cbn [seq map]. destruct i as [|i]; cbn [nth]; [rewrite Nat.add_0_r; reflexivity|].
  rewrite IH by lia. f_equal. lia.
Qed.

Lemma lane_of_bytes (M : word -> option byte) a x bs (i : nat) :
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= x < 2 ^ 64 -> L5.u64_at segs M a x -> L5.bytes_at segs M a bs -> (length bs <= 8)%nat ->
  Forall (fun b => 0 <= b < 256) bs -> (i < length bs)%nat -> lane x i = nth i bs 0.
Proof.
  intros Ha Ha8 Hx U8 BY Hl Hbs Hi.
  assert (BX : L5.bytes_at segs M a (map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 x)))).
  { apply (L5C.rdn_bytes_at segs M); [lia| cbn; lia| exact U8]. }
  pose proof (BY i Hi) as B1. pose proof (BX i ltac:(cbn; lia)) as B2.
  unfold word_to_le_bytes in B2. rewrite Z_to_bv_unsigned, bv_wrap_small, le_bytes_seq, map_map in B2 by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite nth_map_seq in B2 by lia. cbn [Nat.add] in B2.
  rewrite Z_to_bv_unsigned in B2.
  pose proof (PMCG.u8_at_fun segs M (a + Z.of_nat i) _ _ B2 B1) as E.
  pose proof (proj1 (Forall_nth _ _) Hbs i 0 Hi) as R. cbv beta in R.
  unfold bv_wrap in E. change (bv_modulus 8) with 256 in E. rewrite Z.mod_mod in E by lia. rewrite (Z.mod_small (nth i bs 0)) in E by exact R.
  unfold lane. exact E.
Qed.

Lemma xle_of_lanes x : 0 <= x < 2 ^ 64 -> xle (lane x 0) (lane x 1) (lane x 2) (lane x 3) (lane x 4) (lane x 5) (lane x 6) (lane x 7) = x.
Proof.
  intros Hx. unfold xle, lane. change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 3) with 24.
  change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 5) with 40. change (8 * Z.of_nat 6) with 48. change (8 * Z.of_nat 7) with 56. change (2 ^ 0) with 1. rewrite Z.div_1_r.
  pose proof (Z.div_mod x (2 ^ 8) ltac:(lia)) as E0.
  pose proof (Z.div_mod (x / 2 ^ 8) (2 ^ 8) ltac:(lia)) as E1. rewrite Z.div_div in E1 by lia. change (2 ^ 8 * 2 ^ 8) with (2 ^ 16) in E1.
  pose proof (Z.div_mod (x / 2 ^ 16) (2 ^ 8) ltac:(lia)) as E2. rewrite Z.div_div in E2 by lia. change (2 ^ 16 * 2 ^ 8) with (2 ^ 24) in E2.
  pose proof (Z.div_mod (x / 2 ^ 24) (2 ^ 8) ltac:(lia)) as E3. rewrite Z.div_div in E3 by lia. change (2 ^ 24 * 2 ^ 8) with (2 ^ 32) in E3.
  pose proof (Z.div_mod (x / 2 ^ 32) (2 ^ 8) ltac:(lia)) as E4. rewrite Z.div_div in E4 by lia. change (2 ^ 32 * 2 ^ 8) with (2 ^ 40) in E4.
  pose proof (Z.div_mod (x / 2 ^ 40) (2 ^ 8) ltac:(lia)) as E5. rewrite Z.div_div in E5 by lia. change (2 ^ 40 * 2 ^ 8) with (2 ^ 48) in E5.
  pose proof (Z.div_mod (x / 2 ^ 48) (2 ^ 8) ltac:(lia)) as E6. rewrite Z.div_div in E6 by lia. change (2 ^ 48 * 2 ^ 8) with (2 ^ 56) in E6.
  assert (E7 : (x / 2 ^ 56) mod 256 = x / 2 ^ 56).
  { apply Z.mod_small. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  change (2 ^ 8) with 256 in *. rewrite E7.
  set (q8 := x / 256) in *. set (q16 := x / 2 ^ 16) in *. set (q24 := x / 2 ^ 24) in *. set (q32 := x / 2 ^ 32) in *.
  set (q40 := x / 2 ^ 40) in *. set (q48 := x / 2 ^ 48) in *. set (q56 := x / 2 ^ 56) in *.
  set (r0 := x mod 256) in *. set (r1 := q8 mod 256) in *. set (r2 := q16 mod 256) in *. set (r3 := q24 mod 256) in *.
  set (r4 := q32 mod 256) in *. set (r5 := q40 mod 256) in *. set (r6 := q48 mod 256) in *.
  clearbody q8 q16 q24 q32 q40 q48 q56 r0 r1 r2 r3 r4 r5 r6. lia.
Qed.
End Mem.

Lemma slice_cons p pos n : 0 <= pos -> 1 <= n -> pos + n <= blen p -> UbjRef.slice p pos n = bat p pos :: UbjRef.slice p (pos + 1) (n - 1).
Proof.
  intros Hp Hn Hl. unfold UbjRef.slice, bat, blen in *. replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
  rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. rewrite Nat.add_1_r.
  remember (Z.to_nat pos) as i. remember (Z.to_nat (n - 1)) as m.
  assert (Hi : (i < length p)%nat) by lia. clear Hp Hn Hl Heqi Heqm pos n.
  revert p Hi. induction i as [|i IH]; intros p Hi.
  - destruct p as [|c q]; [cbn in Hi; lia|]. reflexivity.
  - destruct p as [|c q]; [cbn in Hi; lia|]. cbn [skipn nth]. apply IH. cbn in Hi. lia.
Qed.
Lemma slice_nil p pos : UbjRef.slice p pos 0 = [].
Proof. reflexivity. Qed.
Lemma rd_be_1 p pos : 0 <= pos -> pos + 1 <= blen p -> rd_be p pos 1 = bat p pos.
Proof.
  intros. unfold rd_be.
  rewrite (slice_cons p (pos) 1) by lia.
  replace (1 - 1) with 0 by reflexivity.
  rewrite slice_nil. cbn [be_val]. lia.
Qed.
Lemma rd_be_2 p pos : 0 <= pos -> pos + 2 <= blen p -> rd_be p pos 2 = bat p pos * 2 ^ 8 + bat p (pos + 1).
Proof.
  intros. unfold rd_be.
  rewrite (slice_cons p (pos) 2) by lia.
  replace (2 - 1) with 1 by reflexivity.
  rewrite (slice_cons p (pos + 1) 1) by lia.
  replace (1 - 1) with 0 by reflexivity.
  rewrite slice_nil. cbn [be_val]. lia.
Qed.
Lemma rd_be_4 p pos : 0 <= pos -> pos + 4 <= blen p ->
  rd_be p pos 4 = bat p pos * 2 ^ 24 + bat p (pos + 1) * 2 ^ 16 + bat p (pos + 1 + 1) * 2 ^ 8 + bat p (pos + 1 + 1 + 1).
Proof.
  intros. unfold rd_be.
  rewrite (slice_cons p (pos) 4) by lia.
  replace (4 - 1) with 3 by reflexivity.
  rewrite (slice_cons p (pos + 1) 3) by lia.
  replace (3 - 1) with 2 by reflexivity.
  rewrite (slice_cons p (pos + 1 + 1) 2) by lia.
  replace (2 - 1) with 1 by reflexivity.
  rewrite (slice_cons p (pos + 1 + 1 + 1) 1) by lia.
  replace (1 - 1) with 0 by reflexivity.
  rewrite slice_nil. cbn [be_val]. lia.
Qed.
Lemma rd_be_8 p pos : 0 <= pos -> pos + 8 <= blen p ->
  rd_be p pos 8 = bat p pos * 2 ^ 56 + bat p (pos + 1) * 2 ^ 48 + bat p (pos + 1 + 1) * 2 ^ 40 + bat p (pos + 1 + 1 + 1) * 2 ^ 32
                  + bat p (pos + 1 + 1 + 1 + 1) * 2 ^ 24 + bat p (pos + 1 + 1 + 1 + 1 + 1) * 2 ^ 16 + bat p (pos + 1 + 1 + 1 + 1 + 1 + 1) * 2 ^ 8
                  + bat p (pos + 1 + 1 + 1 + 1 + 1 + 1 + 1).
Proof.
  intros. unfold rd_be.
  rewrite (slice_cons p (pos) 8) by lia.
  replace (8 - 1) with 7 by reflexivity.
  rewrite (slice_cons p (pos + 1) 7) by lia.
  replace (7 - 1) with 6 by reflexivity.
  rewrite (slice_cons p (pos + 1 + 1) 6) by lia.
  replace (6 - 1) with 5 by reflexivity.
  rewrite (slice_cons p (pos + 1 + 1 + 1) 5) by lia.
  replace (5 - 1) with 4 by reflexivity.
  rewrite (slice_cons p (pos + 1 + 1 + 1 + 1) 4) by lia.
  replace (4 - 1) with 3 by reflexivity.
  rewrite (slice_cons p (pos + 1 + 1 + 1 + 1 + 1) 3) by lia.
  replace (3 - 1) with 2 by reflexivity.
  rewrite (slice_cons p (pos + 1 + 1 + 1 + 1 + 1 + 1) 2) by lia.
  replace (2 - 1) with 1 by reflexivity.
  rewrite (slice_cons p (pos + 1 + 1 + 1 + 1 + 1 + 1 + 1) 1) by lia.
  replace (1 - 1) with 0 by reflexivity.
  rewrite slice_nil. cbn [be_val]. lia.
Qed.

Lemma nth_slice p pos n (i : nat) : 0 <= pos -> Z.of_nat i < n -> pos + n <= blen p -> nth i (UbjRef.slice p pos n) 0 = bat p (pos + Z.of_nat i).
Proof.
  intros Hp Hi Hn. revert pos n Hp Hi Hn. induction i as [|i IH]; intros pos n Hp Hi Hn.
  - rewrite slice_cons by lia. cbn [nth]. rewrite Z.add_0_r. reflexivity.
  - rewrite slice_cons by lia. cbn [nth]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma gl_none_end p pos : blen p <= pos -> UbjRef.get_length p pos = None.
Proof. intros H. unfold UbjRef.get_length. destruct (Z.leb_spec (blen p) pos); [reflexivity| lia]. Qed.
Lemma gl_none_type p pos : pos < blen p -> int_width (bat p pos) = 0 -> UbjRef.get_length p pos = None.
Proof. intros H W. unfold UbjRef.get_length. destruct (Z.leb_spec (blen p) pos); [lia|]. rewrite W. reflexivity. Qed.
Lemma gl_eval p pos t k : pos < blen p -> bat p pos = t -> int_width t = k -> 1 <= k ->
  UbjRef.get_length p pos =
    (if blen p <? pos + 1 + k then None
     else if (if t =? 85 then rd_be p (pos + 1) k else sgn k (rd_be p (pos + 1) k)) <? 0 then None
     else Some ((if t =? 85 then rd_be p (pos + 1) k else sgn k (rd_be p (pos + 1) k)), pos + 1 + k)).
Proof.
  intros H Ht W Hk. unfold UbjRef.get_length. destruct (Z.leb_spec (blen p) pos); [lia|]. rewrite Ht, W.
  destruct (Z.eqb_spec k 0); [lia|]. reflexivity.
Qed.
Lemma int_width_0 t : 0 <= t <= 72 \/ 74 <= t <= 75 \/ 77 <= t <= 84 \/ 86 <= t <= 104 \/ 106 <= t <= 107 \/ 109 <= t -> int_width t = 0.
Proof.
  intros H. unfold int_width.
  destruct (Z.eqb_spec t 105); [lia|]. destruct (Z.eqb_spec t 85); [lia|]. destruct (Z.eqb_spec t 73); [lia|].
  destruct (Z.eqb_spec t 108); [lia|]. destruct (Z.eqb_spec t 76); [lia|]. reflexivity.
Qed.

Lemma sgn_cases k b rest : (k = 1 \/ k = 2 \/ k = 4 \/ k = 8) -> 0 <= b < 256 -> 0 <= rest < 2 ^ (8 * k - 8) ->
  (sgn k (b * 2 ^ (8 * k - 8) + rest) <? 0) = (128 <=? b)
  /\ (b < 128 -> sgn k (b * 2 ^ (8 * k - 8) + rest) = b * 2 ^ (8 * k - 8) + rest).
Proof.
  intros Hk Hb Hr. unfold sgn.
  assert (P : 2 ^ (8 * k - 1) = 128 * 2 ^ (8 * k - 8)) by (change 128 with (2 ^ 7); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite P. assert (Q : 2 ^ (8 * k) = 256 * 2 ^ (8 * k - 8)) by (change 256 with (2 ^ 8); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Q. assert (0 < 2 ^ (8 * k - 8)) by (apply Z.pow_pos_nonneg; lia).
  split.
  - destruct (Z.ltb_spec (b * 2 ^ (8 * k - 8) + rest) (128 * 2 ^ (8 * k - 8))) as [L|L];
    destruct (Z.leb_spec 128 b) as [L'|L']; [exfalso; nia| destruct (Z.ltb_spec (b * 2 ^ (8 * k - 8) + rest) 0); [lia|reflexivity]
                                              | destruct (Z.ltb_spec (b * 2 ^ (8 * k - 8) + rest - 256 * 2 ^ (8 * k - 8)) 0); [reflexivity| nia] | exfalso; nia].
  - intros L. destruct (Z.ltb_spec (b * 2 ^ (8 * k - 8) + rest) (128 * 2 ^ (8 * k - 8))) as [L'|L']; [reflexivity| exfalso; nia].
Qed.

Lemma sgn1_cases b0 : 0 <= b0 < 256 -> (sgn 1 b0 <? 0) = (128 <=? b0) /\ (b0 < 128 -> sgn 1 b0 = b0).
Proof. intros H0. pose proof (sgn_cases 1 b0 0 ltac:(lia) H0 ltac:(cbn; lia)) as C. change (2 ^ (8 * 1 - 8)) with 1 in C. rewrite Z.mul_1_r, Z.add_0_r in C. exact C. Qed.
Lemma sgn2_cases b0 b1 : 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  (sgn 2 (b0 * 2 ^ 8 + b1) <? 0) = (128 <=? b0) /\ (b0 < 128 -> sgn 2 (b0 * 2 ^ 8 + b1) = b0 * 2 ^ 8 + b1).
Proof. intros H0 H1. exact (sgn_cases 2 b0 b1 ltac:(lia) H0 ltac:(change (2 ^ (8 * 2 - 8)) with 256; lia)). Qed.
Lemma sgn4_cases b0 b1 b2 b3 : 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  (sgn 4 (b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3) <? 0) = (128 <=? b0)
  /\ (b0 < 128 -> sgn 4 (b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3) = b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3).
Proof.
  intros H0 H1 H2 H3. replace (b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3) with (b0 * 2 ^ (8 * 4 - 8) + (b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3)) by (change (2 ^ (8 * 4 - 8)) with (2 ^ 24); lia).
  exact (sgn_cases 4 b0 (b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3) ltac:(lia) H0 ltac:(change (2 ^ (8 * 4 - 8)) with (2 ^ 24); lia)).
Qed.
Lemma sgn8_cases b0 b1 b2 b3 b4 b5 b6 b7 : 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 ->
  (sgn 8 (be8 b0 b1 b2 b3 b4 b5 b6 b7) <? 0) = (128 <=? b0) /\ (b0 < 128 -> sgn 8 (be8 b0 b1 b2 b3 b4 b5 b6 b7) = be8 b0 b1 b2 b3 b4 b5 b6 b7).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7. unfold be8.
  replace (b0 * 2 ^ 56 + b1 * 2 ^ 48 + b2 * 2 ^ 40 + b3 * 2 ^ 32 + b4 * 2 ^ 24 + b5 * 2 ^ 16 + b6 * 2 ^ 8 + b7)
     with (b0 * 2 ^ (8 * 8 - 8) + (b1 * 2 ^ 48 + b2 * 2 ^ 40 + b3 * 2 ^ 32 + b4 * 2 ^ 24 + b5 * 2 ^ 16 + b6 * 2 ^ 8 + b7)) by (change (2 ^ (8 * 8 - 8)) with (2 ^ 56); lia).
  exact (sgn_cases 8 b0 (b1 * 2 ^ 48 + b2 * 2 ^ 40 + b3 * 2 ^ 32 + b4 * 2 ^ 24 + b5 * 2 ^ 16 + b6 * 2 ^ 8 + b7) ltac:(lia) H0 ltac:(change (2 ^ (8 * 8 - 8)) with (2 ^ 56); lia)).
Qed.

Lemma gl_eval_s p pos t k : pos < blen p -> bat p pos = t -> int_width t = k -> 1 <= k -> t <> 85 ->
  UbjRef.get_length p pos =
    (if blen p <? pos + 1 + k then None else if sgn k (rd_be p (pos + 1) k) <? 0 then None else Some (sgn k (rd_be p (pos + 1) k), pos + 1 + k)).
Proof. intros H Ht W Hk N. rewrite (gl_eval p pos t k H Ht W Hk). destruct (Z.eqb_spec t 85); [lia| reflexivity]. Qed.
Lemma gl_eval_u p pos : bytes_ok p -> 0 <= pos < blen p -> bat p pos = 85 ->
  UbjRef.get_length p pos = (if blen p <? pos + 1 + 1 then None else Some (bat p (pos + 1), pos + 1 + 1)).
Proof.
  intros BOK H Ht. rewrite (gl_eval p pos 85 1 ltac:(lia) Ht eq_refl ltac:(lia)). rewrite Z.eqb_refl.
  destruct (Z.ltb_spec (blen p) (pos + 1 + 1)) as [L|L]; [reflexivity|]. rewrite rd_be_1 by lia.
  pose proof (proj1 (Forall_nth _ _) BOK (Z.to_nat (pos + 1)) 0 ltac:(unfold blen in *; lia)) as B. cbv beta in B. unfold bat.
  destruct (Z.ltb_spec (nth (Z.to_nat (pos + 1)) p 0) 0); [lia| reflexivity].
Qed.

End PECGLW.
