(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: bit-level and arithmetic facts that musl fread's walk (libreac/fuzz_pcap,
   ASan build, fread 0x8ee5c) needs about the RISC-V value functions, and the facts about
   rread_k / rmread_fill (lib/A/Stdio/PFreadM.v:275-277).

   rule 24: no function proved. These are auxiliary lemmas, not a function walk.

   THE VALUE FUNCTIONS (the ones the step lemmas produce):
     mul  s6,s2,s1   (0x8eec4)  Mul M_MUL    -> YK11.step_mul    : YK11.v_mul (YK11.v:115)
     divu a0,a0,s1   (0x8ef60)  Mul M_DIVU   -> YK14.step_divu   : YK14.v_divu (YK14.v:459);
                                the semantics' own function is Sem.mul_div M_DIVU, equal to
                                v_divu for a nonzero divisor (YK14.m_divu).
     seqz a0,s1      (0x8ef2c)  OpImm ALU_SLTU 10 9 1     -> YK11.step_sltiu : YK11.v_sltiu (YK11.v:128)
     addi a0,a0,-1   (0x8ef30)  OpImm ALU_ADD 10 10 4095  -> YK11.step_addi  : YK11.v_addi  (YK11.v:112)
     and  a0,a0,s2   (0x8ef34)  Op ALU_AND 10 10 18       -> YK11.step_and   : YK11.v_and   (YK11.v:119)
   In fread s1 = size and s2 = nmemb. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK14.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadM.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section fa.
Context {fx : YK11.FPState}.

Lemma fa_u64_small : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. exact Hz. Qed.

(* 1. size * nmemb at 0x8eec4 with size = 1 (mul s6, s2, s1: rs1 = nmemb, rs2 = size). *)
Lemma v_mul_one : forall z, 0 <= z < 2 ^ 64 -> v_mul (Z_to_bv 64 z) (Z_to_bv 64 1) = Z_to_bv 64 z.
Proof.
intros z Hz. unfold v_mul. rewrite (fa_u64_small z Hz), (fa_u64_small 1) by lia.
rewrite Z.mul_1_r. reflexivity.
Qed.

(* 2. divu a0, a0, s1 at 0x8ef60 with s1 = size = 1: over YK14.v_divu (what YK14.step_divu
   yields), and over the semantics' Sem.mul_div M_DIVU. *)
Lemma v_divu_one : forall z, 0 <= z < 2 ^ 64 -> v_divu (Z_to_bv 64 z) (Z_to_bv 64 1) = Z_to_bv 64 z.
Proof.
intros z Hz. unfold v_divu. rewrite (fa_u64_small z Hz), (fa_u64_small 1) by lia.
rewrite Z.div_1_r. reflexivity.
Qed.

Lemma divu_one_nz : bv_unsigned (Z_to_bv 64 1) <> 0.
Proof. rewrite fa_u64_small by lia. lia. Qed.

Lemma mul_div_divu_one : forall z, 0 <= z < 2 ^ 64 ->
  mul_div M_DIVU (Z_to_bv 64 z) (Z_to_bv 64 1) = Z_to_bv 64 z.
Proof. intros z Hz. rewrite (m_divu _ _ divu_one_nz). apply v_divu_one. exact Hz. Qed.

(* 3. The zero-size return chain at 0x8ef2c-0x8ef34 with s1 = 1 and s2 = z:
     seqz a0,s1    = sltiu a0,s1,1   (decoded OpImm ALU_SLTU 10 9 1)
     addi a0,a0,-1                   (decoded OpImm ALU_ADD 10 10 4095)
     and  a0,a0,s2                   (decoded Op ALU_AND 10 10 18)
   Each step value as the step lemma states it. *)
Lemma seqz_one : v_sltiu (Z_to_bv 64 1) 1 = Z_to_bv 64 0.
Proof. unfold v_sltiu. rewrite fa_u64_small by lia. rewrite bv_wrap64_mod. reflexivity. Qed.

Lemma addi_m1_zero : v_addi (Z_to_bv 64 0) (-1) = Z_to_bv 64 (-1).
Proof. unfold v_addi. rewrite fa_u64_small by lia. reflexivity. Qed.

Lemma and_m1 : forall z, 0 <= z < 2 ^ 64 -> v_and (Z_to_bv 64 (-1)) (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros z Hz. unfold v_and. rewrite (fa_u64_small z Hz).
rewrite Z_to_bv_unsigned. change (bv_wrap 64 (-1)) with (Z.ones 64).
rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by exact Hz. reflexivity.
Qed.

(* The chain with the immediates as integers (seqz's 1 and addi's -1). *)
Lemma seqz_chain_one : forall z, 0 <= z < 2 ^ 64 ->
  v_and (v_addi (v_sltiu (Z_to_bv 64 1) 1) (-1)) (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. rewrite seqz_one, addi_m1_zero. apply and_m1. exact Hz. Qed.

(* The chain exactly as YK11.step_sltiu / step_addi / step_and state it on the decoded
   instructions: the immediates are bv_signed of the decoded bv 12 literals 1 and 4095. *)
Lemma imm12_1 : bv_signed (1%bv : bv 12) = 1.
Proof. reflexivity. Qed.
Lemma imm12_4095 : bv_signed (4095%bv : bv 12) = -1.
Proof. reflexivity. Qed.

Lemma seqz_chain_one_dec : forall z, 0 <= z < 2 ^ 64 ->
  v_and (v_addi (v_sltiu (Z_to_bv 64 1) (bv_signed (1%bv : bv 12))) (bv_signed (4095%bv : bv 12)))
        (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. rewrite imm12_1, imm12_4095. apply seqz_chain_one. exact Hz. Qed.

End fa.

(* The instruction forms used above, decoded from the words at 0x8eec4, 0x8ef2c-0x8ef34 and
   0x8ef60 (the asan listing of fread). *)
Section fa_dec.
Local Open Scope bv_scope.
Local Ltac fa_vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Lemma fa_D_8eec4 : decode_any (0x02990b33 : bv 32) = Some (Mul M_MUL 22 18 9, 4%Z).
Proof. fa_vm_refl. Qed.
Lemma fa_D_8ef2c : decode_any (0x0014b513 : bv 32) = Some (OpImm ALU_SLTU 10 9 1, 4%Z).
Proof. fa_vm_refl. Qed.
Lemma fa_D_8ef30 : decode_any (0xfff50513 : bv 32) = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. fa_vm_refl. Qed.
Lemma fa_D_8ef34 : decode_any (0x01257533 : bv 32) = Some (Op ALU_AND 10 10 18, 4%Z).
Proof. fa_vm_refl. Qed.
Lemma fa_D_8ef60 : decode_any (0x02955533 : bv 32) = Some (Mul M_DIVU 10 10 9, 4%Z).
Proof. fa_vm_refl. Qed.
End fa_dec.

(* 4-8. rread_k (PFreadM.v:275) and rmread_fill (PFreadM.v:277). *)
Lemma rread_k_bounds : forall l n p, 0 <= l -> 0 <= p <= n ->
  0 <= rread_k l n p <= l /\ rread_k l n p <= n - p.
Proof. intros l n p Hl Hp. unfold rread_k. lia. Qed.

Lemma rread_k_full : forall l n p, 0 <= l -> 0 <= p <= n -> l <= n - p -> rread_k l n p = l.
Proof. intros l n p Hl Hp Hle. unfold rread_k. lia. Qed.

Lemma rread_k_short : forall l n p, 0 <= l -> 0 <= p <= n -> n - p < l -> rread_k l n p = n - p.
Proof. intros l n p Hl Hp Hlt. unfold rread_k. lia. Qed.

(* True as written: min l2 (n - (p + l1)) + l1 = min (l1 + l2) (n - p) for all integers. *)
Lemma rread_k_split : forall l1 l2 n p, 0 <= l1 -> 0 <= l2 -> 0 <= p -> p + l1 <= n ->
  rread_k l2 n (p + l1) + l1 = rread_k (l1 + l2) n p.
Proof. intros l1 l2 n p H1 H2 Hp Hn. unfold rread_k. lia. Qed.

Lemma rmread_fill_bounds : forall l n p, 0 <= l -> 0 <= p <= n ->
  0 <= rmread_fill l n p <= SRC_BUFSIZ /\ p + rread_k l n p + rmread_fill l n p <= n.
Proof. intros l n p Hl Hp. unfold rmread_fill, rread_k, SRC_BUFSIZ. lia. Qed.
