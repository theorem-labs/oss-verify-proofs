(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import LibAtomic UbExitBase Ub_code_1b104_1c2fc Ub_code_1d2fc_1e5e4 Ub_code_1e5e4_1f5f0 Ub_code_235f0_245f0  .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x1c00c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x1e23c)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x1c00c ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x269f0 wp1 rp1 ->
  file_clean mem 0x26810 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x1e22c : word) mem rom)
                 (mkst regs' (0x1bda8 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr & Ghd & Glk & Gdso & Gil & Giw & Gib & Gir & Gie)
         (F1l & F1wp & F1wb & F1rp & F1re) (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1e22c D_1e22c. rewrite Hsp. sp_renorm.
    stepST F_1e230 D_1e230 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1c00c) ltac:(sok_stack SOK).
    stepST F_1e234 D_1e234 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1e238 D_1e238.
    stepn F_1e808 D_1e808. sp_renorm.
    stepST F_1e80c D_1e80c (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x1e23c) ltac:(sok_stack SOK).
    stepST F_1e810 D_1e810 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_1e814 D_1e814.
    stepn F_1e818 D_1e818.
    stepn F_1e81c D_1e81c.
    (* [comment removed for export] *)
    stepn F_1e820 D_1e820.
    stepn F_24228 D_24228.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_2422c | reflexivity | exact D_2422c | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_24230 D_24230 ltac:(cond_compute).
    stepret F_24420 D_24420 (0x1e824 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1e824 D_1e824.
    stepLD8 F_1e828 D_1e828 (Z_to_bv 64 0x1e23c).
    stepLD8 F_1e82c D_1e82c code.
    stepn F_1e830 D_1e830. sp_renorm.
    stepret F_1e834 D_1e834 (0x1e23c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_1e23c D_1e23c (Z_to_bv 64 0).
    stepb_ft F_1e240 D_1e240 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1e244 D_1e244.
    stepLD8 F_1e248 D_1e248 (Z_to_bv 64 0x26900).
    stepb_ft F_1e24c D_1e24c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_1e250 D_1e250 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1e254 D_1e254 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1e260 D_1e260 (Z_to_bv 64 0).
    stepLD8 F_1e264 D_1e264 (Z_to_bv 64 0).
    stepb_tk F_1e268 D_1e268 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1e280 D_1e280 (Z_to_bv 64 0).
    stepLD8 F_1e284 D_1e284 (Z_to_bv 64 0).
    stepb_tk F_1e288 D_1e288 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1e2a0 D_1e2a0.
    stepLD8 F_1e2a4 D_1e2a4 (Z_to_bv 64 0x269f0).
    stepb_ft F_1e2a8 D_1e2a8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_1e2ac D_1e2ac (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1e2b0 D_1e2b0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1e2bc D_1e2bc wp1.
    stepLD8 F_1e2c0 D_1e2c0 wp1.
    stepb_tk F_1e2c4 D_1e2c4 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_1e2dc D_1e2dc rp1.
    stepLD8 F_1e2e0 D_1e2e0 rp1.
    stepb_tk F_1e2e4 D_1e2e4 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_1e2fc D_1e2fc.
    stepLD8 F_1e300 D_1e300 (Z_to_bv 64 0x26810).
    stepb_ft F_1e304 D_1e304 ltac:(cond_compute).
    stepLD F_1e308 D_1e308 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1e30c D_1e30c ltac:(cond_compute).
    stepLD8 F_1e318 D_1e318 wp2.
    stepLD8 F_1e31c D_1e31c wp2.
    stepb_tk F_1e320 D_1e320 ltac:(apply c_eq_refl).
    stepLD8 F_1e338 D_1e338 rp2.
    stepLD8 F_1e33c D_1e33c rp2.
    stepb_tk F_1e340 D_1e340 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_1e3c0 D_1e3c0 (Z_to_bv 64 0x1c00c).
    stepLD8 F_1e3c4 D_1e3c4 code.
    stepn F_1e3c8 D_1e3c8. sp_renorm.
    stepret F_1e3cc D_1e3cc (0x1c00c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1c00c D_1c00c.
    stepn F_1c010 D_1c010.
    stepn F_1bda0 D_1bda0.
    stepn F_1bda4 D_1bda4.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
