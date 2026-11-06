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
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require WalkTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require WalkTac.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.WalkTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.StreamSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.MmapSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.WalkTac.LibAtomic.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UbExitBase UbExit_run2.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Ub_code_22780_228cc Ub_code_5233c_52dd8 Ub_code_558d8_56250 Ub_code_60914_60c38.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section WithFP1.
Context {fx : FPState}.
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0x66cc8 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x66cc8 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x66cc8 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x66cc8 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x55e08)).

#[using="Type"] Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x52c4c ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0x559a8 : word) mem rom)
                 (mkst regs' (0x55e08 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x66cc8
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x55a58
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x66cc8
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_559a8 D_559a8. rewrite Hsp. sp_renorm.
    stepST F_559ac D_559ac (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x52c4c) ltac:(sok_stack SOK).
    stepST F_559b0 D_559b0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_559b4 D_559b4.
    stepn F_55d3c D_55d3c. sp_renorm.
    stepST F_55d40 D_55d40 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x559b8) ltac:(sok_stack SOK).
    stepST F_55d44 D_55d44 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_55d48 D_55d48.
    stepn F_55d4c D_55d4c.
    stepn F_55d50 D_55d50.
    (* [comment removed for export] *)
    stepn F_55d54 D_55d54.
    stepn F_60914 D_60914.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_60918 | reflexivity | exact D_60918 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_6091c D_6091c ltac:(cond_compute).
    stepret F_60b0c D_60b0c (0x55d58 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_55d58 D_55d58.
    stepLD8 F_55d5c D_55d5c (Z_to_bv 64 0x559b8).
    stepLD8 F_55d60 D_55d60 code.
    stepn F_55d64 D_55d64. sp_renorm.
    stepret F_55d68 D_55d68 (0x559b8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_559b8 D_559b8 (Z_to_bv 64 0).
    stepb_ft F_559bc D_559bc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_559c0 D_559c0.
    stepLD8 F_559c4 D_559c4 (Z_to_bv 64 0).
    stepb_tk F_559c8 D_559c8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_55a1c D_55a1c.
    stepLD8 F_55a20 D_55a20 (Z_to_bv 64 0x66cc8).
    stepb_ft F_55a24 D_55a24 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_55a28 D_55a28 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_55a2c D_55a2c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_55a38 D_55a38 (Z_to_bv 64 wp).
    stepLD8 F_55a3c D_55a3c (Z_to_bv 64 wb).
    stepb_ft F_55a40 D_55a40 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_55a44 D_55a44 (Z_to_bv 64 0x55e08).
    stepn F_55a48 D_55a48.
    stepn F_55a4c D_55a4c.
    stepn F_55a50 D_55a50.
    stepjr F_55a54 D_55a54 (Z_to_bv 64 0x55e08) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x66cc8 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x52c4c)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0x66cc8 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0x66cc8 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0x66cc0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x66bd8)) ->
  file_clean mem 0x66bd8 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x55a58 : word) mem rom)
                 (mkst regs' (0x529b8 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_55a58 D_55a58 rp1.
    stepLD8 F_55a5c D_55a5c rp1.
    stepb_tk F_55a60 D_55a60 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_55a78 D_55a78.
    stepLD8 F_55a7c D_55a7c (Z_to_bv 64 0x66bd8).
    stepb_ft F_55a80 D_55a80 ltac:(cond_compute).
    stepLD F_55a84 D_55a84 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_55a88 D_55a88 ltac:(cond_compute).
    stepLD8 F_55a94 D_55a94 wp2.
    stepLD8 F_55a98 D_55a98 wp2.
    stepb_tk F_55a9c D_55a9c ltac:(apply c_eq_refl).
    stepLD8 F_55ab4 D_55ab4 rp2.
    stepLD8 F_55ab8 D_55ab8 rp2.
    stepb_tk F_55abc D_55abc ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_55b3c D_55b3c (Z_to_bv 64 0x52c4c).
    stepLD8 F_55b40 D_55b40 code.
    stepn F_55b44 D_55b44. rewrite Hsp. sp_renorm.
    stepret F_55b48 D_55b48 (0x52c4c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_52c4c D_52c4c.
    stepn F_52c50 D_52c50.
    stepn F_529b0 D_529b0.
    stepn F_529b4 D_529b4.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

End WithFP1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

