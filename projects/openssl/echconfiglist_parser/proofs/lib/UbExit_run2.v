(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Ubsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic UbExitBase Ub_code_2b52bc_2b5e0c Ub_code_2b94c4_2ba44c Ub_code_2c1140_2c1650.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b5d24)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b9510)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x2b5d24 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdin_clean mem ->
  file_clean mem 0x3233c0 wp1 rp1 ->
  file_clean mem 0x3231e0 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b9500 : word) mem rom)
                 (mkst regs' (0x2b5ac0 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F0l & F0wp & F0wb & F0rp & F0re)
         (F1l & F1wp & F1wb & F1rp & F1re) (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_2b94c4 D_2b94c4. rewrite Hsp. sp_renorm.
    stepST F_2b94c8 D_2b94c8 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2b5d24) ltac:(sok_stack SOK).
    stepST F_2b94cc D_2b94cc (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_2b94d0 D_2b94d0.
    stepn F_2ba410 D_2ba410. sp_renorm.
    stepST F_2ba414 D_2ba414 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x2b9510) ltac:(sok_stack SOK).
    stepST F_2ba418 D_2ba418 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_2ba41c D_2ba41c.
    stepn F_2ba420 D_2ba420.
    stepn F_2ba424 D_2ba424.
    (* [comment removed for export] *)
    stepn F_2ba428 D_2ba428.
    stepn F_2c1354 D_2c1354.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_2c1358 | reflexivity | exact D_2c1358 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_2c135c D_2c135c ltac:(cond_compute).
    stepret F_2c154c D_2c154c (0x2ba468 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_2ba42c D_2ba42c.
    stepLD8 F_2ba430 D_2ba430 (Z_to_bv 64 0x2b9510).
    stepLD8 F_2ba434 D_2ba434 code.
    stepn F_2ba438 D_2ba438. sp_renorm.
    stepret F_2ba43c D_2ba43c (0x2b9510 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_2b94d4 D_2b94d4 (Z_to_bv 64 0).
    stepb_ft F_2b94d8 D_2b94d8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2b94dc D_2b94dc.
    stepLD8 F_2b94e0 D_2b94e0 (Z_to_bv 64 0x3232d0).
    stepb_ft F_2b94e4 D_2b94e4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_2b94e8 D_2b94e8 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_2b94ec D_2b94ec ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_2b94f8 D_2b94f8 (Z_to_bv 64 0).
    stepLD8 F_2b94fc D_2b94fc (Z_to_bv 64 0).
    stepb_tk F_2b9500 D_2b9500 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_2b9518 D_2b9518 (Z_to_bv 64 0).
    stepLD8 F_2b951c D_2b951c (Z_to_bv 64 0).
    stepb_tk F_2b9520 D_2b9520 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_2b9538 D_2b9538.
    stepLD8 F_2b953c D_2b953c (Z_to_bv 64 0x3233c0).
    stepb_ft F_2b9540 D_2b9540 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_2b9544 D_2b9544 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_2b9548 D_2b9548 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_2b9554 D_2b9554 wp1.
    stepLD8 F_2b9558 D_2b9558 wp1.
    stepb_tk F_2b955c D_2b955c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_2b9574 D_2b9574 rp1.
    stepLD8 F_2b9578 D_2b9578 rp1.
    stepb_tk F_2b957c D_2b957c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_2b9594 D_2b9594.
    stepLD8 F_2b9598 D_2b9598 (Z_to_bv 64 0x3231e0).
    stepb_ft F_2b959c D_2b959c ltac:(cond_compute).
    stepLD F_2b95a0 D_2b95a0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_2b95a4 D_2b95a4 ltac:(cond_compute).
    stepLD8 F_2b95b0 D_2b95b0 wp2.
    stepLD8 F_2b95b4 D_2b95b4 wp2.
    stepb_tk F_2b95b8 D_2b95b8 ltac:(apply c_eq_refl).
    stepLD8 F_2b95d0 D_2b95d0 rp2.
    stepLD8 F_2b95d4 D_2b95d4 rp2.
    stepb_tk F_2b95d8 D_2b95d8 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_2b9658 D_2b9658 (Z_to_bv 64 0x2b5d24).
    stepLD8 F_2b965c D_2b965c code.
    stepn F_2b9660 D_2b9660. sp_renorm.
    stepret F_2b9664 D_2b9664 (0x2b5d24 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_2b5ce8 D_2b5ce8.
    stepn F_2b5cec D_2b5cec.
    stepn F_2b5a7c D_2b5a7c.
    stepn F_2b5a80 D_2b5a80.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
