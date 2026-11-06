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
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  Ub0ExitBase Ub0_code_4b6b4_4c150 Ub0_code_4dfcc_4e304 Ub0_code_4ed20_4f2d8 Ub0_code_59324_59540       Ub0_code_59540_5a048.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.


Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x4bfc4)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x4ed30)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x4bfc4 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x60268 wp1 rp1 ->
  file_clean mem 0x60178 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x4ed20 : word) mem rom)
                 (mkst regs' (0x4bd30 : word) (mem_w3a mem sp code) rom)
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
    stepn F_4ed20 D_4ed20. rewrite Hsp. sp_renorm.
    stepST F_4ed24 D_4ed24 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x4bfc4) ltac:(sok_stack SOK).
    stepST F_4ed28 D_4ed28 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_4ed2c D_4ed2c.
    stepn F_4f0b4 D_4f0b4. sp_renorm.
    stepST F_4f0b8 D_4f0b8 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x4ed30) ltac:(sok_stack SOK).
    stepST F_4f0bc D_4f0bc (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_4f0c0 D_4f0c0.
    stepn F_4f0c4 D_4f0c4.
    stepn F_4f0c8 D_4f0c8.
    (* [comment removed for export] *)
    stepn F_4f0cc D_4f0cc.
    stepn F_59d24 D_59d24.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_59d28 | reflexivity | exact D_59d28 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_59d2c D_59d2c ltac:(cond_compute).
    stepret F_59f1c D_59f1c (0x4f0d0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_4f0d0 D_4f0d0.
    stepLD8 F_4f0d4 D_4f0d4 (Z_to_bv 64 0x4ed30).
    stepLD8 F_4f0d8 D_4f0d8 code.
    stepn F_4f0dc D_4f0dc. sp_renorm.
    stepret F_4f0e0 D_4f0e0 (0x4ed30 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_4ed30 D_4ed30 (Z_to_bv 64 0).
    stepb_ft F_4ed34 D_4ed34 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_4ed38 D_4ed38.
    stepLD8 F_4ed3c D_4ed3c (Z_to_bv 64 0).
    stepb_tk F_4ed40 D_4ed40 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_4ed94 D_4ed94.
    stepLD8 F_4ed98 D_4ed98 (Z_to_bv 64 0x60268).
    stepb_ft F_4ed9c D_4ed9c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_4eda0 D_4eda0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_4eda4 D_4eda4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_4edb0 D_4edb0 wp1.
    stepLD8 F_4edb4 D_4edb4 wp1.
    stepb_tk F_4edb8 D_4edb8 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_4edd0 D_4edd0 rp1.
    stepLD8 F_4edd4 D_4edd4 rp1.
    stepb_tk F_4edd8 D_4edd8 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_4edf0 D_4edf0.
    stepLD8 F_4edf4 D_4edf4 (Z_to_bv 64 0x60178).
    stepb_ft F_4edf8 D_4edf8 ltac:(cond_compute).
    stepLD F_4edfc D_4edfc (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_4ee00 D_4ee00 ltac:(cond_compute).
    stepLD8 F_4ee0c D_4ee0c wp2.
    stepLD8 F_4ee10 D_4ee10 wp2.
    stepb_tk F_4ee14 D_4ee14 ltac:(apply c_eq_refl).
    stepLD8 F_4ee2c D_4ee2c rp2.
    stepLD8 F_4ee30 D_4ee30 rp2.
    stepb_tk F_4ee34 D_4ee34 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_4eeb4 D_4eeb4 (Z_to_bv 64 0x4bfc4).
    stepLD8 F_4eeb8 D_4eeb8 code.
    stepn F_4eebc D_4eebc. sp_renorm.
    stepret F_4eec0 D_4eec0 (0x4bfc4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_4bfc4 D_4bfc4.
    stepn F_4bfc8 D_4bfc8.
    stepn F_4bd28 D_4bd28.
    stepn F_4bd2c D_4bd2c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
