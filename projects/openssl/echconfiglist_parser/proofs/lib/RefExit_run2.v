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
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  RefExitBase Ref_code_26e688_26f1d8 Ref_code_272890_273818 Ref_code_27a50c_27aa1c          .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x26f0f0)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x2728dc)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x26f0f0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdin_clean mem ->
  file_clean mem 0x2dc7a0 wp1 rp1 ->
  file_clean mem 0x2dc5c0 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x2728cc : word) mem rom)
                 (mkst regs' (0x26ee8c : word) (mem_w3a mem sp code) rom)
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
    stepn F_272890 D_272890. rewrite Hsp. sp_renorm.
    stepST F_272894 D_272894 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x26f0f0) ltac:(sok_stack SOK).
    stepST F_272898 D_272898 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_27289c D_27289c.
    stepn F_2737dc D_2737dc. sp_renorm.
    stepST F_2737e0 D_2737e0 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x2728dc) ltac:(sok_stack SOK).
    stepST F_2737e4 D_2737e4 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_2737e8 D_2737e8.
    stepn F_2737ec D_2737ec.
    stepn F_2737f0 D_2737f0.
    (* [comment removed for export] *)
    stepn F_2737f4 D_2737f4.
    stepn F_27a720 D_27a720.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_27a724 | reflexivity | exact D_27a724 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_27a728 D_27a728 ltac:(cond_compute).
    stepret F_27a918 D_27a918 (0x273834 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_2737f8 D_2737f8.
    stepLD8 F_2737fc D_2737fc (Z_to_bv 64 0x2728dc).
    stepLD8 F_273800 D_273800 code.
    stepn F_273804 D_273804. sp_renorm.
    stepret F_273808 D_273808 (0x2728dc : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_2728a0 D_2728a0 (Z_to_bv 64 0).
    stepb_ft F_2728a4 D_2728a4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2728a8 D_2728a8.
    stepLD8 F_2728ac D_2728ac (Z_to_bv 64 0x2dc6b0).
    stepb_ft F_2728b0 D_2728b0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_2728b4 D_2728b4 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_2728b8 D_2728b8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_2728c4 D_2728c4 (Z_to_bv 64 0).
    stepLD8 F_2728c8 D_2728c8 (Z_to_bv 64 0).
    stepb_tk F_2728cc D_2728cc ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_2728e4 D_2728e4 (Z_to_bv 64 0).
    stepLD8 F_2728e8 D_2728e8 (Z_to_bv 64 0).
    stepb_tk F_2728ec D_2728ec ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_272904 D_272904.
    stepLD8 F_272908 D_272908 (Z_to_bv 64 0x2dc7a0).
    stepb_ft F_27290c D_27290c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_272910 D_272910 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_272914 D_272914 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_272920 D_272920 wp1.
    stepLD8 F_272924 D_272924 wp1.
    stepb_tk F_272928 D_272928 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_272940 D_272940 rp1.
    stepLD8 F_272944 D_272944 rp1.
    stepb_tk F_272948 D_272948 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_272960 D_272960.
    stepLD8 F_272964 D_272964 (Z_to_bv 64 0x2dc5c0).
    stepb_ft F_272968 D_272968 ltac:(cond_compute).
    stepLD F_27296c D_27296c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_272970 D_272970 ltac:(cond_compute).
    stepLD8 F_27297c D_27297c wp2.
    stepLD8 F_272980 D_272980 wp2.
    stepb_tk F_272984 D_272984 ltac:(apply c_eq_refl).
    stepLD8 F_27299c D_27299c rp2.
    stepLD8 F_2729a0 D_2729a0 rp2.
    stepb_tk F_2729a4 D_2729a4 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_272a24 D_272a24 (Z_to_bv 64 0x26f0f0).
    stepLD8 F_272a28 D_272a28 code.
    stepn F_272a2c D_272a2c. sp_renorm.
    stepret F_272a30 D_272a30 (0x26f0f0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_26f0b4 D_26f0b4.
    stepn F_26f0b8 D_26f0b8.
    stepn F_26ee48 D_26ee48.
    stepn F_26ee4c D_26ee4c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
