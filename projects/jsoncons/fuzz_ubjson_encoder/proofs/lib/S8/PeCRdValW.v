(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import AxSymExec3.
Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECRVW.

Lemma lor_lt_pow2 a b n : 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Na]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Nb]; [rewrite Z.lor_0_r; lia|].
  assert (Hn : 0 <= n). { destruct (Z_lt_le_dec n 0) as [X|X]; [|exact X]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  assert (P : 0 < Z.lor a b).
  { pose proof (proj2 (Z.lor_nonneg a b) (conj (proj1 Ha) (proj1 Hb))). assert (Z.lor a b <> 0) by (intros E; apply Z.lor_eq_0_iff in E; lia). lia. }
  apply Z.log2_lt_pow2; [exact P|]. rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.
Lemma land_le_r (a b : Z) : 0 <= a -> 0 <= b -> 0 <= Z.land a b <= b.
Proof.
  intros Ha Hb. rewrite <- (Z2N.id a Ha), <- (Z2N.id b Hb). rewrite <- N2Z.inj_land.
  pose proof (N.land_le_r (Z.to_N a) (Z.to_N b)). lia.
Qed.
Lemma lor_disjoint a t n : 0 <= n -> 0 <= a -> a mod 2 ^ n = 0 -> 0 <= t < 2 ^ n -> Z.lor a t = a + t.
Proof.
  intros Hn Ha Hm Ht.
  assert (L0 : Z.land a t = 0).
  { replace t with (Z.land t (Z.ones n)) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
    rewrite (Z.land_comm t), Z.land_assoc, Z.land_ones by lia. rewrite Hm. apply Z.land_0_l. }
  rewrite <- Z.lxor_lor by exact L0. symmetry. apply Z.add_nocarry_lxor. exact L0.
Qed.

Lemma and48_63 : bv_and (Z_to_bv 64 48) (Z_to_bv 64 63) = Z_to_bv 64 48. Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma and8_63 : bv_and (Z_to_bv 64 8) (Z_to_bv 64 63) = Z_to_bv 64 8. Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma low32_24 : bv_and (low32 (Z_to_bv 64 24)) (Z_to_bv 32 31) = Z_to_bv 32 24. Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma wid_sext8 (E : env) (e : expr) : exists v, -128 <= v < 128 /\ edenot E (EExt true 0 1 e) = Z_to_bv 64 v.
Proof.
  cbn [edenot]. unfold ext_val, ext_Z. cbv zeta. cbn [Z.of_nat N.of_nat Z.mul Pos.mul Pos.of_succ_nat].
  set (u := (bv_unsigned (edenot E e) / 2 ^ 0) mod 2 ^ 8).
  exists (bv_swrap 8 u). split; [|reflexivity].
  rewrite <- (Z_to_bv_signed 8 u). pose proof (bv_signed_in_range 8 (Z_to_bv 8 u) ltac:(discriminate)) as H.
  unfold bv_half_modulus in H. change (bv_modulus 8 `div` 2) with 128 in H. lia.
Qed.

Lemma wid_sra48 (E : env) (e : expr) : exists v, - 2 ^ 15 <= v < 2 ^ 15 /\ edenot E (EAlu Instr.ALU_SRA e (ELit 48)) = Z_to_bv 64 v.
Proof.
  cbn [edenot]. unfold alu64, alu. rewrite and48_63.
  set (a := edenot E e). exists (bv_signed a ≫ 48). split.
  - rewrite Z.shiftr_div_pow2 by lia. pose proof (bv_signed_in_range 64 a ltac:(discriminate)) as H.
    unfold bv_half_modulus in H. change (bv_modulus 64 `div` 2) with (2 ^ 63) in H.
    split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia].
  - apply (proj2 (bv_eq_signed 64 _ _)). rewrite bv_ashiftr_signed, Z_to_bv_signed, Z_to_bv_unsigned. reflexivity.
Qed.

Lemma swrap32_cases (z : Z) : 0 <= z < 2 ^ 32 -> bv_swrap 32 z = (if z <? 2 ^ 31 then z else z - 2 ^ 32).
Proof.
  intros Hz. unfold bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  destruct (Z.ltb_spec z (2 ^ 31)) as [L|L].
  - rewrite Z.mod_small by lia. lia.
  - replace (z + 2 ^ 31) with ((z + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma wrap64_cases (z : Z) : - 2 ^ 63 <= z < 2 ^ 63 -> bv_wrap 64 z = (if z <? 0 then z + 2 ^ 64 else z).
Proof.
  intros Hz. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). destruct (Z.ltb_spec z 0) as [L|L].
  - replace z with ((z + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - apply Z.mod_small. lia.
Qed.

Lemma sllw24_facts (w : bv 64) :
  let A := sext 64 (alu32 Instr.ALU_SLL (low32 w) (low32 (Z_to_bv 64 24))) in
  exists m, 0 <= m < 256 /\ bv_unsigned A = (if m <? 128 then m * 2 ^ 24 else 2 ^ 64 - 2 ^ 32 + m * 2 ^ 24).
Proof.
  cbv zeta. unfold alu32, alu, sext. rewrite low32_24. rewrite bv_sign_extend_unsigned.
  set (x := bv_unsigned (low32 w)). pose proof (bv_unsigned_in_range 32 (low32 w)) as XR. change (bv_modulus 32) with (2 ^ 32) in XR. fold x in XR.
  set (m := x mod 256). exists m. pose proof (Z.mod_pos_bound x 256 ltac:(lia)) as MR. fold m in MR. split; [exact MR|].
  assert (BU : bv_unsigned (low32 w ≪ Z_to_bv 32 24)%bv = m * 2 ^ 24).
  { rewrite bv_shiftl_unsigned, Z_to_bv_unsigned. change (bv_wrap 32 24) with 24. rewrite Z.shiftl_mul_pow2 by lia. fold x.
    unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
    rewrite (Z.div_mod x 256) at 1 by lia. fold m.
    replace ((256 * (x `div` 256) + m) * 2 ^ 24) with (m * 2 ^ 24 + (x `div` 256) * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  unfold bv_signed. rewrite BU. rewrite swrap32_cases by lia.
  destruct (Z.ltb_spec (m * 2 ^ 24) (2 ^ 31)) as [L|L]; destruct (Z.ltb_spec m 128) as [L'|L']; try (exfalso; lia).
  - rewrite wrap64_cases by lia. destruct (Z.ltb_spec (m * 2 ^ 24) 0); lia.
  - rewrite wrap64_cases by lia. destruct (Z.ltb_spec (m * 2 ^ 24 - 2 ^ 32) 0); lia.
Qed.

Lemma srlw24_small (w : bv 64) : 0 <= bv_unsigned (sext 64 (alu32 Instr.ALU_SRL (low32 w) (low32 (Z_to_bv 64 24)))) < 2 ^ 8.
Proof.
  unfold alu32, alu, sext. rewrite low32_24. rewrite bv_sign_extend_unsigned.
  pose proof (bv_unsigned_in_range 32 (low32 w)) as XR. change (bv_modulus 32) with (2 ^ 32) in XR.
  assert (SU : bv_unsigned (low32 w ≫ Z_to_bv 32 24)%bv < 2 ^ 8 /\ 0 <= bv_unsigned (low32 w ≫ Z_to_bv 32 24)%bv).
  { rewrite bv_shiftr_unsigned, Z_to_bv_unsigned. change (bv_wrap 32 24) with 24. rewrite Z.shiftr_div_pow2 by lia.
    split; [apply Z.div_lt_upper_bound; lia| apply Z.div_pos; lia]. }
  unfold bv_signed. rewrite swrap32_cases by lia. destruct (Z.ltb_spec (bv_unsigned (low32 w ≫ Z_to_bv 32 24)%bv) (2 ^ 31)); [|exfalso; lia].
  rewrite wrap64_cases by lia. destruct (Z.ltb_spec (bv_unsigned (low32 w ≫ Z_to_bv 32 24)%bv) 0); lia.
Qed.

Lemma wid_sext32 (E : env) (e : expr) : exists v, - 2 ^ 31 <= v < 2 ^ 31 /\
  edenot E (EAlu Instr.ALU_OR (EAlu Instr.ALU_OR (EAluw Instr.ALU_SLL e (ELit 24)) (EMd Instr.M_MUL (ELit 256) (EAlu Instr.ALU_AND e (ELit 65280))))
                     (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL e (ELit 8)) (ELit 65280)) (EAluw Instr.ALU_SRL e (ELit 24)))) = Z_to_bv 64 v.
Proof.
  cbn [edenot]. set (w := edenot E e).
  destruct (sllw24_facts w) as (m & Hm & HA). cbv zeta in HA.
  set (A := sext 64 (alu32 Instr.ALU_SLL (low32 w) (low32 (Z_to_bv 64 24)))) in *.
  set (B := mul_div Instr.M_MUL (Z_to_bv 64 256) (alu64 Instr.ALU_AND w (Z_to_bv 64 65280))).
  set (C1 := alu64 Instr.ALU_AND (alu64 Instr.ALU_SRL w (Z_to_bv 64 8)) (Z_to_bv 64 65280)).
  set (C2 := sext 64 (alu32 Instr.ALU_SRL (low32 w) (low32 (Z_to_bv 64 24)))).
  pose proof (bv_unsigned_in_range 64 w) as WR. change (bv_modulus 64) with (2 ^ 64) in WR.
  assert (HB : 0 <= bv_unsigned B < 2 ^ 24).
  { unfold B, mul_div, alu64, alu. rewrite bv_mul_unsigned, bv_and_unsigned, !Z_to_bv_unsigned. change (bv_wrap 64 256) with 256. change (bv_wrap 64 65280) with 65280.
    pose proof (land_le_r (bv_unsigned w) 65280 ltac:(lia) ltac:(lia)) as L. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_small by lia. lia. }
  assert (HC1 : 0 <= bv_unsigned C1 < 2 ^ 16).
  { unfold C1, alu64, alu. rewrite and8_63. rewrite bv_and_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 65280) with 65280.
    pose proof (bv_unsigned_in_range 64 (w ≫ Z_to_bv 64 8)%bv) as R8.
    pose proof (land_le_r (bv_unsigned (w ≫ Z_to_bv 64 8)%bv) 65280 ltac:(lia) ltac:(lia)) as L. lia. }
  pose proof (srlw24_small w) as HC2. fold C2 in HC2.
  assert (HC : 0 <= Z.lor (bv_unsigned C1) (bv_unsigned C2) < 2 ^ 24).
  { pose proof (lor_lt_pow2 (bv_unsigned C1) (bv_unsigned C2) 24 ltac:(lia) ltac:(lia)). lia. }
  set (t := Z.lor (bv_unsigned B) (Z.lor (bv_unsigned C1) (bv_unsigned C2))).
  assert (HT : 0 <= t < 2 ^ 24) by (unfold t; apply lor_lt_pow2; lia).
  assert (A0 : 0 <= bv_unsigned A) by (pose proof (bv_unsigned_in_range 64 A); lia).
  assert (AM : bv_unsigned A mod 2 ^ 24 = 0).
  { rewrite HA. destruct (m <? 128).
    - apply Z.mod_mul. lia.
    - replace (2 ^ 64 - 2 ^ 32 + m * 2 ^ 24) with ((2 ^ 40 - 2 ^ 8 + m) * 2 ^ 24) by lia. apply Z.mod_mul. lia. }
  assert (HU : bv_unsigned (alu64 Instr.ALU_OR (alu64 Instr.ALU_OR A B) (alu64 Instr.ALU_OR C1 C2)) = bv_unsigned A + t).
  { unfold alu64, alu. rewrite !bv_or_unsigned. rewrite <- Z.lor_assoc. change (Z.lor (bv_unsigned B) (Z.lor (bv_unsigned C1) (bv_unsigned C2))) with t.
    exact (lor_disjoint (bv_unsigned A) t 24 ltac:(lia) A0 AM HT). }
  exists (if m <? 128 then m * 2 ^ 24 + t else m * 2 ^ 24 + t - 2 ^ 32). split.
  - destruct (Z.ltb_spec m 128); lia.
  - apply bv_eq. rewrite HU, Z_to_bv_unsigned, HA. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). destruct (Z.ltb_spec m 128).
    + symmetry. apply Z.mod_small. lia.
    + replace (m * 2 ^ 24 + t - 2 ^ 32) with ((2 ^ 64 - 2 ^ 32 + m * 2 ^ 24 + t) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
      symmetry. apply Z.mod_small. lia.
Qed.
End PECRVW.
