(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma swrap32_small : forall u, 0 <= u < 2^31 -> bv_swrap (8 * N.of_nat 4) u = u.
Proof.
  intros u H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (8 * N.of_nat 4)%N with 32%N.
  change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ (Z.of_N 32 - 1)) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma ext_Z_lo32_small : forall z, 0 <= z < 2^31 -> ext_Z true 0 4 z = z.
Proof.
  intros z H. unfold ext_Z. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  change (2 ^ (8 * Z.of_nat 4)) with 4294967296. rewrite Z.mod_small by lia. apply swrap32_small. lia.
Qed.

Lemma ext_Z_hi32_zero : forall z, 0 <= z < 2^32 -> ext_Z true 4 4 z = 0.
Proof.
  intros z H. unfold ext_Z. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
  rewrite Z.div_small by lia. rewrite Zmod_0_l. apply swrap32_small. lia.
Qed.

Lemma u_wa64 : forall z, 0 <= z < 2^64 -> bv_unsigned (wa z) = z.
Proof. intros z H. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma hdr_frame : forall E e sz, 1 <= sz <= 255 -> bv_unsigned (edenot E e) = sz ->
  edenot E (EAlu ALU_OR (EAluw ALU_SLL (EExt true 4 4 e) (ELit 8)) (EExt true 0 4 e)) = wa sz.
Proof.
  intros E e sz Hs He. cbn [edenot]. unfold ext_val. rewrite He.
  rewrite ext_Z_hi32_zero by lia. rewrite ext_Z_lo32_small by lia.
  unfold alu64, alu32, sext, low32. cbn [alu64 alu32].
  lazymatch goal with |- alu _ ALU_OR ?A _ = _ => replace A with (Z_to_bv 64 0) by (vm_compute; reflexivity) end.
  cbn [alu]. rewrite bv_or_0_l by reflexivity. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma aluw_add_small : forall E ea eb a b, 0 <= a -> 0 <= b -> a + b < 2^31 -> a < 2^31 ->
  bv_unsigned (edenot E ea) = a -> bv_unsigned (edenot E eb) = b ->
  edenot E (EAluw ALU_ADD (EExt true 0 4 ea) eb) = wa (a + b).
Proof.
  intros E ea eb a b Ha Hb Hab Ha2 HA HB. cbn [edenot]. unfold ext_val. rewrite HA.
  rewrite ext_Z_lo32_small by lia. apply bv_eq. unfold alu64, alu32, sext, low32. cbn [alu].
  rewrite bv_sign_extend_unsigned, bv_add_signed, !bv_extract_signed, HB, Z_to_bv_unsigned.
  unfold wa. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648. rewrite !Z.shiftr_0_r.
  rewrite (Z.mod_small a 18446744073709551616) by lia.
  rewrite (Z.mod_small (a + 2147483648) 4294967296) by lia. rewrite (Z.mod_small (b + 2147483648) 4294967296) by lia.
  replace (a + 2147483648 - 2147483648 + (b + 2147483648 - 2147483648) + 2147483648) with (a + b + 2147483648) by lia.
  rewrite (Z.mod_small (a + b + 2147483648) 4294967296) by lia.
  replace (a + b + 2147483648 - 2147483648) with (a + b) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pack_zero : forall E esz est sz st, 0 <= sz -> 0 <= st -> sz + st + 1 < 2^20 ->
  bv_unsigned (edenot E esz) = sz -> bv_unsigned (edenot E est) = st ->
  edenot E (EAlu ALU_SLTU (EAlu ALU_XOR (EAlu ALU_ADD (EAlu ALU_ADD esz (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) (EExt true 0 4 est)) (ELit 32))) (ELit 1)) (ELit 1048576)) (ELit 1)) = wa 0.
Proof.
  intros E esz est sz st Hs Ht Hb HS HT. cbn [edenot]. unfold ext_val. rewrite HT. rewrite ext_Z_lo32_small by lia.
  unfold alu64, mul_div. cbn [alu].
  assert (E1 : bv_unsigned (bv_shiftr (bv_mul (Z_to_bv 64 4294967296) (Z_to_bv 64 st)) (bv_and (Z_to_bv 64 32) (Z_to_bv 64 63))) = st).
  { rewrite bv_shiftr_unsigned, bv_and_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with 18446744073709551616. change (Z.land (32 mod 18446744073709551616) (63 mod 18446744073709551616)) with 32.
    rewrite (Z.mod_small st) by lia. change (4294967296 mod 18446744073709551616) with 4294967296.
    rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. rewrite Z.mul_comm, Z.div_mul by lia.
    reflexivity. }
  set (X := bv_shiftr (bv_mul (Z_to_bv 64 4294967296) (Z_to_bv 64 st)) (bv_and (Z_to_bv 64 32) (Z_to_bv 64 63))) in *.
  assert (E2 : bv_unsigned (bv_add (bv_add (edenot E esz) X) (Z_to_bv 64 1)) = sz + st + 1).
  { rewrite !bv_add_unsigned, HS, E1, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    change (1 mod 18446744073709551616) with 1. rewrite (Z.mod_small (sz + st)) by lia. rewrite Z.mod_small by lia. reflexivity. }
  set (Y := bv_add (bv_add (edenot E esz) X) (Z_to_bv 64 1)) in *.
  assert (E3 : bv_unsigned (bv_xor Y (Z_to_bv 64 1048576)) <> 0).
  { rewrite bv_xor_unsigned, E2, Z_to_bv_unsigned. change (bv_wrap 64 1048576) with 1048576. intros H.
    apply Z.lxor_eq in H. lia. }
  unfold bv_ltu. replace (bv_unsigned (bv_xor Y (Z_to_bv 64 1048576)) <? bv_unsigned (Z_to_bv 64 1)) with false.
  - reflexivity.
  - symmetry. apply Z.ltb_ge. change (bv_unsigned (Z_to_bv 64 1)) with 1. pose proof (bv_unsigned_in_range _ (bv_xor Y (Z_to_bv 64 1048576))). lia.
Qed.

Lemma add_lit_u : forall E e x k, 0 <= x -> 0 <= k -> x + k < 2^64 -> bv_unsigned (edenot E e) = x ->
  bv_unsigned (edenot E (EAlu ALU_ADD e (ELit k))) = x + k.
Proof.
  intros E e x k Hx Hk Hxk He. cbn [edenot]. unfold alu64. cbn [alu]. rewrite bv_add_unsigned, He, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite (Z.mod_small k) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
(* [comment removed for export] *)
