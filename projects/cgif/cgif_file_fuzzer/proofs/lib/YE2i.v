(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK1b YP0m YP0e YP09 YI04 YI00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma rdn_of_mbytes : forall segs mem bs a,
(forall j, (j < length bs)%nat -> mbyte segs mem (a + Z.of_nat j) = Some (nth j bs (Z_to_bv 8 0))) ->
rdn segs mem (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
intros segs mem bs. induction bs as [|b bs IH]; intros a H; [reflexivity|].
cbn [length rdn]. pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn [nth Z.of_nat] in H0. rewrite Z.add_0_r in H0.
unfold mbyte in H0. rewrite H0. rewrite Z_to_bv64_add1. rewrite (IH (a + 1)); [reflexivity|].
intros j Hj. specialize (H (S j) ltac:(cbn; lia)). cbn [nth] in H. rewrite <- H. f_equal. lia.
Qed.
Lemma rdn_of_garr8 : forall segs mem a X, garr8 segs mem a X ->
rdn segs mem (Z_to_bv 64 a) (length X) = Some (map (fun z => Z_to_bv 8 z) X).
Proof.
intros segs mem a X HG. rewrite <- (length_map (fun z => Z_to_bv 8 z) X) at 1. apply rdn_of_mbytes. intros j Hj. rewrite length_map in Hj.
rewrite (garr8_mbyte segs mem a X j HG Hj).
change (Z_to_bv 8 0) with ((fun z => Z_to_bv 8 z) 0). rewrite map_nth. reflexivity.
Qed.
Lemma word_to_nat_len : forall n : nat, Z.of_nat n < 2 ^ 64 -> word_to_nat (Z_to_bv 64 (Z.of_nat n)) = n.
Proof.
intros n Hn. unfold word_to_nat. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.mod_small by lia. apply Nat2Z.id.
Qed.
Lemma word_to_nat_lit : forall z, 0 <= z < 2 ^ 64 -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof.
intros z Hz. unfold word_to_nat. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma U_iovcnt : forall E a b,
U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR a b)) (SLit 1)) (SLit 0)) = (if U E a =? U E b then 1 else 2).
Proof.
intros E a b. pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold M64 in *.
rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 0), (zcanon_id 1) by (unfold M64; lia).
pose proof (Z_lxor_range (U E a) (U E b) Ra Rb) as Hx.
rewrite (zcanon_id (Z.lxor (U E a) (U E b))) by (unfold M64; exact Hx).
destruct (Z.eqb_spec (U E a) (U E b)) as [Eab|Nab].
- rewrite Eab, Z.lxor_nilpotent. cbn. reflexivity.
- assert (Z.lxor (U E a) (U E b) <> 0) by (intros H0; apply Z.lxor_eq in H0; contradiction).
replace (0 <? Z.lxor (U E a) (U E b)) with true by (symmetry; apply Z.ltb_lt; lia). cbn. reflexivity.
Qed.
Lemma U_sub_form_gen : forall E a b z, z mod 2 ^ 64 = 2 ^ 64 - 1 -> U E b <= U E a -> U E (SAlu ALU_ADD a (SMd M_MUL b (SLit z))) = U E a - U E b.
Proof.
intros E a b z Hz Hle. pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold M64 in *.
rewrite U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64. rewrite Hz.
rewrite Zplus_mod_idemp_r.
replace (U E a + U E b * (2 ^ 64 - 1)) with (U E a - U E b + U E b * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma U_add_mod : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. reflexivity. Qed.
