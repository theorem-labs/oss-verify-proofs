(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0ExitBase_u Bs0_code_r4b000_4c000_u Bs0_code_r4d000_4e000_u Bs0_code_r4e000_4f000_u Bs0_code_r58000_59000_u      .
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x9ae5c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0xa0408)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x9ae5c ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0xb83f0 wp1 rp1 ->
  file_clean mem 0xb8300 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0xa03f8 : word) mem rom)
                 (mkst regs' (0x9ab00 : word) (mem_w3a mem sp code) rom)
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
  - (* [comment removed for export] *)
    stepn F_9edc4 D_9edc4. rewrite Hsp. sp_renorm.
    stepST F_9edc8 D_9edc8 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9ae5c) ltac:(sok_stack SOK).
    stepST F_9edcc D_9edcc (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_9edd0 D_9edd0.
    stepn F_9f1ec D_9f1ec. sp_renorm.
    stepST F_9f1f0 D_9f1f0 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0xa0408) ltac:(sok_stack SOK).
    stepST F_9f1f4 D_9f1f4 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_9f1f8 D_9f1f8.
    stepn F_9f1fc D_9f1fc.
    stepn F_9f200 D_9f200.
    (* [comment removed for export] *)
    stepn F_9f204 D_9f204.
    stepn F_aaadc D_aaadc.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
    stepret F_aacd4 D_aacd4 (0xa083c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_9f208 D_9f208.
    stepLD8 F_9f20c D_9f20c (Z_to_bv 64 0xa0408).
    stepLD8 F_9f210 D_9f210 code.
    stepn F_9f214 D_9f214. sp_renorm.
    stepret F_9f218 D_9f218 (0xa0408 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_9edd4 D_9edd4 (Z_to_bv 64 0).
    stepb_ft F_9edd8 D_9edd8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_9eddc D_9eddc.
    stepLD8 F_9ede0 D_9ede0 (Z_to_bv 64 0).
    stepb_tk F_9ede4 D_9ede4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_9ee38 D_9ee38.
    stepLD8 F_9ee3c D_9ee3c (Z_to_bv 64 0xb83f0).
    stepb_ft F_9ee40 D_9ee40 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_9ee44 D_9ee44 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_9ee48 D_9ee48 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_9ee54 D_9ee54 wp1.
    stepLD8 F_9ee58 D_9ee58 wp1.
    stepb_tk F_9ee5c D_9ee5c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_9ee74 D_9ee74 rp1.
    stepLD8 F_9ee78 D_9ee78 rp1.
    stepb_tk F_9ee7c D_9ee7c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_9ee94 D_9ee94.
    stepLD8 F_9ee98 D_9ee98 (Z_to_bv 64 0xb8300).
    stepb_ft F_9ee9c D_9ee9c ltac:(cond_compute).
    stepLD F_9eea0 D_9eea0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_9eea4 D_9eea4 ltac:(cond_compute).
    stepLD8 F_9eeb0 D_9eeb0 wp2.
    stepLD8 F_9eeb4 D_9eeb4 wp2.
    stepb_tk F_9eeb8 D_9eeb8 ltac:(apply c_eq_refl).
    stepLD8 F_9eed0 D_9eed0 rp2.
    stepLD8 F_9eed4 D_9eed4 rp2.
    stepb_tk F_9eed8 D_9eed8 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_9ef58 D_9ef58 (Z_to_bv 64 0x9ae5c).
    stepLD8 F_9ef5c D_9ef5c code.
    stepn F_9ef60 D_9ef60. sp_renorm.
    stepret F_9ef64 D_9ef64 (0x9ae5c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_99828 D_99828.
    stepn F_9982c D_9982c.
    stepn F_994c4 D_994c4.
    stepn F_994c8 D_994c8.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
