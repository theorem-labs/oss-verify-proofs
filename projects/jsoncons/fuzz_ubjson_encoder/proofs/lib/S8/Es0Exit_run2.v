(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic Es0ExitBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Es0_code_r4b000_4c000 Es0_code_r4d000_4e000 Es0_code_r4e000_4f000 Es0_code_r58000_59000.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x9be64)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0xa14ac)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x9be64 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0xb94a8 wp1 rp1 ->
  file_clean mem 0xb93b8 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0xa149c : word) mem rom)
                 (mkst regs' (0x9bb08 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr)
         (F1l & F1wp & F1wb & F1rp & F1re) (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  unfold mem_w3a. eexists. split.
  -
    stepn F_a1450 D_a1450. rewrite Hsp. sp_renorm.
    stepST F_a1454 D_a1454 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9be64) ltac:(sok_stack SOK).
    stepST F_a1458 D_a1458 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).

    stepn F_a145c D_a145c.
    stepn F_a1878 D_a1878. sp_renorm.
    stepST F_a187c D_a187c (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0xa14ac) ltac:(sok_stack SOK).
    stepST F_a1880 D_a1880 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_a1884 D_a1884.
    stepn F_a1888 D_a1888.
    stepn F_a188c D_a188c.

    stepn F_a1890 D_a1890.
    stepn F_ad0d0 D_ad0d0.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
    stepret F_ad2c8 D_ad2c8 (0xa18e0 : word) ltac:(bveq).

    stepn F_a1894 D_a1894.
    stepLD8 F_a1898 D_a1898 (Z_to_bv 64 0xa14ac).
    stepLD8 F_a189c D_a189c code.
    stepn F_a18a0 D_a18a0. sp_renorm.
    stepret F_a18a4 D_a18a4 (0xa14ac : word) ltac:(bveq).

    stepLD8 F_a1460 D_a1460 (Z_to_bv 64 0).
    stepb_ft F_a1464 D_a1464 ltac:(cond_compute).

    stepn F_a1468 D_a1468.
    stepLD8 F_a146c D_a146c (Z_to_bv 64 0).
    stepb_tk F_a1470 D_a1470 ltac:(cond_compute).

    stepn F_a14c4 D_a14c4.
    stepLD8 F_a14c8 D_a14c8 (Z_to_bv 64 0xb94a8).
    stepb_ft F_a14cc D_a14cc ltac:(cond_compute).

    stepLD F_a14d0 D_a14d0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_a14d4 D_a14d4 ltac:(cond_compute).

    stepLD8 F_a14e0 D_a14e0 wp1.
    stepLD8 F_a14e4 D_a14e4 wp1.
    stepb_tk F_a14e8 D_a14e8 ltac:(apply c_eq_refl).

    stepLD8 F_a1500 D_a1500 rp1.
    stepLD8 F_a1504 D_a1504 rp1.
    stepb_tk F_a1508 D_a1508 ltac:(apply c_eq_refl).

    stepn F_a1520 D_a1520.
    stepLD8 F_a1524 D_a1524 (Z_to_bv 64 0xb93b8).
    stepb_ft F_a1528 D_a1528 ltac:(cond_compute).
    stepLD F_a152c D_a152c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_a1530 D_a1530 ltac:(cond_compute).
    stepLD8 F_a153c D_a153c wp2.
    stepLD8 F_a1540 D_a1540 wp2.
    stepb_tk F_a1544 D_a1544 ltac:(apply c_eq_refl).
    stepLD8 F_a155c D_a155c rp2.
    stepLD8 F_a1560 D_a1560 rp2.
    stepb_tk F_a1564 D_a1564 ltac:(apply c_eq_refl).

    stepLD8 F_a15e4 D_a15e4 (Z_to_bv 64 0x9be64).
    stepLD8 F_a15e8 D_a15e8 code.
    stepn F_a15ec D_a15ec. sp_renorm.
    stepret F_a15f0 D_a15f0 (0x9be64 : word) ltac:(bveq).

    stepn F_9be18 D_9be18.
    stepn F_9be1c D_9be1c.
    stepn F_9bab4 D_9bab4.
    stepn F_9bab8 D_9bab8.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
