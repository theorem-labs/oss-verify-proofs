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
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require WalkTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require WalkTac.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.WalkTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.StreamSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.MmapSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.WalkTac.LibAtomic.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import RefExitBase.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Ref_code_224ec_22638 Ref_code_50584_51020 Ref_code_53b20_54498 Ref_code_5eb5c_5ee80.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1.
Context {fx : FPState}.
Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x50e94)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x53c00)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

#[using="Type"] Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x50e94 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x64f10 wp1 rp1 ->
  file_clean mem 0x64e20 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x53bf0 : word) mem rom)
                 (mkst regs' (0x50c00 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem rom sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr)
         (F1l & F1wp & F1wb & F1rp & F1re) (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_53bf0 D_53bf0. rewrite Hsp. sp_renorm.
    stepST F_53bf4 D_53bf4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x50e94) ltac:(sok_stack SOK).
    stepST F_53bf8 D_53bf8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_53bfc D_53bfc.
    stepn F_53f84 D_53f84. sp_renorm.
    stepST F_53f88 D_53f88 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x53c00) ltac:(sok_stack SOK).
    stepST F_53f8c D_53f8c (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_53f90 D_53f90.
    stepn F_53f94 D_53f94.
    stepn F_53f98 D_53f98.
    (* [comment removed for export] *)
    stepn F_53f9c D_53f9c.
    stepn F_5eb5c D_5eb5c.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_5eb60 | reflexivity | exact D_5eb60 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_5eb64 D_5eb64 ltac:(cond_compute).
    stepret F_5ed54 D_5ed54 (0x53fa0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_53fa0 D_53fa0.
    stepLD8 F_53fa4 D_53fa4 (Z_to_bv 64 0x53c00).
    stepLD8 F_53fa8 D_53fa8 code.
    stepn F_53fac D_53fac. sp_renorm.
    stepret F_53fb0 D_53fb0 (0x53c00 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_53c00 D_53c00 (Z_to_bv 64 0).
    stepb_ft F_53c04 D_53c04 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_53c08 D_53c08.
    stepLD8 F_53c0c D_53c0c (Z_to_bv 64 0).
    stepb_tk F_53c10 D_53c10 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_53c64 D_53c64.
    stepLD8 F_53c68 D_53c68 (Z_to_bv 64 0x64f10).
    stepb_ft F_53c6c D_53c6c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_53c70 D_53c70 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_53c74 D_53c74 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_53c80 D_53c80 wp1.
    stepLD8 F_53c84 D_53c84 wp1.
    stepb_tk F_53c88 D_53c88 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_53ca0 D_53ca0 rp1.
    stepLD8 F_53ca4 D_53ca4 rp1.
    stepb_tk F_53ca8 D_53ca8 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_53cc0 D_53cc0.
    stepLD8 F_53cc4 D_53cc4 (Z_to_bv 64 0x64e20).
    stepb_ft F_53cc8 D_53cc8 ltac:(cond_compute).
    stepLD F_53ccc D_53ccc (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_53cd0 D_53cd0 ltac:(cond_compute).
    stepLD8 F_53cdc D_53cdc wp2.
    stepLD8 F_53ce0 D_53ce0 wp2.
    stepb_tk F_53ce4 D_53ce4 ltac:(apply c_eq_refl).
    stepLD8 F_53cfc D_53cfc rp2.
    stepLD8 F_53d00 D_53d00 rp2.
    stepb_tk F_53d04 D_53d04 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_53d84 D_53d84 (Z_to_bv 64 0x50e94).
    stepLD8 F_53d88 D_53d88 code.
    stepn F_53d8c D_53d8c. sp_renorm.
    stepret F_53d90 D_53d90 (0x50e94 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_50e94 D_50e94.
    stepn F_50e98 D_50e98.
    stepn F_50bf8 D_50bf8.
    stepn F_50bfc D_50bfc.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
End WithFP1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

