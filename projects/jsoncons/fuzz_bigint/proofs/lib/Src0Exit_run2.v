(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  Src0ExitBase Src0_code_4b104_4b654 Src0_code_4dfcc_4e3c8 Src0_code_4e5b8_4e7dc Src0_code_58828_59540      .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.


Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x4b4c8)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x4e234)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x4b4c8 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x5f770 wp1 rp1 ->
  file_clean mem 0x5f680 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x4e224 : word) mem rom)
                 (mkst regs' (0x4b234 : word) (mem_w3a mem sp code) rom)
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
    stepn F_4e224 D_4e224. rewrite Hsp. sp_renorm.
    stepST F_4e228 D_4e228 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x4b4c8) ltac:(sok_stack SOK).
    stepST F_4e22c D_4e22c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_4e230 D_4e230.
    stepn F_4e5b8 D_4e5b8. sp_renorm.
    stepST F_4e5bc D_4e5bc (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x4e234) ltac:(sok_stack SOK).
    stepST F_4e5c0 D_4e5c0 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_4e5c4 D_4e5c4.
    stepn F_4e5c8 D_4e5c8.
    stepn F_4e5cc D_4e5cc.
    (* [comment removed for export] *)
    stepn F_4e5d0 D_4e5d0.
    stepn F_59228 D_59228.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_5922c | reflexivity | exact D_5922c | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_59230 D_59230 ltac:(cond_compute).
    stepret F_59420 D_59420 (0x4e5d4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_4e5d4 D_4e5d4.
    stepLD8 F_4e5d8 D_4e5d8 (Z_to_bv 64 0x4e234).
    stepLD8 F_4e5dc D_4e5dc code.
    stepn F_4e5e0 D_4e5e0. sp_renorm.
    stepret F_4e5e4 D_4e5e4 (0x4e234 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_4e234 D_4e234 (Z_to_bv 64 0).
    stepb_ft F_4e238 D_4e238 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_4e23c D_4e23c.
    stepLD8 F_4e240 D_4e240 (Z_to_bv 64 0).
    stepb_tk F_4e244 D_4e244 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_4e298 D_4e298.
    stepLD8 F_4e29c D_4e29c (Z_to_bv 64 0x5f770).
    stepb_ft F_4e2a0 D_4e2a0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_4e2a4 D_4e2a4 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_4e2a8 D_4e2a8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_4e2b4 D_4e2b4 wp1.
    stepLD8 F_4e2b8 D_4e2b8 wp1.
    stepb_tk F_4e2bc D_4e2bc ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_4e2d4 D_4e2d4 rp1.
    stepLD8 F_4e2d8 D_4e2d8 rp1.
    stepb_tk F_4e2dc D_4e2dc ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_4e2f4 D_4e2f4.
    stepLD8 F_4e2f8 D_4e2f8 (Z_to_bv 64 0x5f680).
    stepb_ft F_4e2fc D_4e2fc ltac:(cond_compute).
    stepLD F_4e300 D_4e300 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_4e304 D_4e304 ltac:(cond_compute).
    stepLD8 F_4e310 D_4e310 wp2.
    stepLD8 F_4e314 D_4e314 wp2.
    stepb_tk F_4e318 D_4e318 ltac:(apply c_eq_refl).
    stepLD8 F_4e330 D_4e330 rp2.
    stepLD8 F_4e334 D_4e334 rp2.
    stepb_tk F_4e338 D_4e338 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_4e3b8 D_4e3b8 (Z_to_bv 64 0x4b4c8).
    stepLD8 F_4e3bc D_4e3bc code.
    stepn F_4e3c0 D_4e3c0. sp_renorm.
    stepret F_4e3c4 D_4e3c4 (0x4b4c8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_4b4c8 D_4b4c8.
    stepn F_4b4cc D_4b4cc.
    stepn F_4b22c D_4b22c.
    stepn F_4b230 D_4b230.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
