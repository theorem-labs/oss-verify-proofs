(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic Ub_code_6b4a8_6bc18 Ub_code_6ee40_6f2f4 Ub_code_79f8c_7a2d4.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RefExitBase RefExit_run2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0x84e38 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x84e38 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x84e38 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x84e38 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6f2f4)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x6bc10 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0x6ee94 : word) mem rom)
                 (mkst regs' (0x6f2f4 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x84e38
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x6ef44
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x84e38
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_6ee94 D_6ee94. rewrite Hsp. sp_renorm.
    stepST F_6ee98 D_6ee98 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x6bc10) ltac:(sok_stack SOK).
    stepST F_6ee9c D_6ee9c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_6eea0 D_6eea0.
    stepn F_6f228 D_6f228. sp_renorm.
    stepST F_6f22c D_6f22c (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x6eea4) ltac:(sok_stack SOK).
    stepST F_6f230 D_6f230 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_6f234 D_6f234.
    stepn F_6f238 D_6f238.
    stepn F_6f23c D_6f23c.
    (* [comment removed for export] *)
    stepn F_6f240 D_6f240.
    stepn F_79f8c D_79f8c.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_79f90 | reflexivity | exact D_79f90 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_79f94 D_79f94 ltac:(cond_compute).
    stepret F_7a184 D_7a184 (0x6f244 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_6f244 D_6f244.
    stepLD8 F_6f248 D_6f248 (Z_to_bv 64 0x6eea4).
    stepLD8 F_6f24c D_6f24c code.
    stepn F_6f250 D_6f250. sp_renorm.
    stepret F_6f254 D_6f254 (0x6eea4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_6eea4 D_6eea4 (Z_to_bv 64 0).
    stepb_ft F_6eea8 D_6eea8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_6eeac D_6eeac.
    stepLD8 F_6eeb0 D_6eeb0 (Z_to_bv 64 0).
    stepb_tk F_6eeb4 D_6eeb4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_6ef08 D_6ef08.
    stepLD8 F_6ef0c D_6ef0c (Z_to_bv 64 0x84e38).
    stepb_ft F_6ef10 D_6ef10 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_6ef14 D_6ef14 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_6ef18 D_6ef18 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_6ef24 D_6ef24 (Z_to_bv 64 wp).
    stepLD8 F_6ef28 D_6ef28 (Z_to_bv 64 wb).
    stepb_ft F_6ef2c D_6ef2c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_6ef30 D_6ef30 (Z_to_bv 64 0x6f2f4).
    stepn F_6ef34 D_6ef34.
    stepn F_6ef38 D_6ef38.
    stepn F_6ef3c D_6ef3c.
    stepjr F_6ef40 D_6ef40 (Z_to_bv 64 0x6f2f4) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x84e38 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6bc10)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0x84e38 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0x84e38 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0x84e30) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x84d48)) ->
  file_clean mem 0x84d48 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x6ef44 : word) mem rom)
                 (mkst regs' (0x6b97c : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_6ef44 D_6ef44 rp1.
    stepLD8 F_6ef48 D_6ef48 rp1.
    stepb_tk F_6ef4c D_6ef4c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_6ef64 D_6ef64.
    stepLD8 F_6ef68 D_6ef68 (Z_to_bv 64 0x84d48).
    stepb_ft F_6ef6c D_6ef6c ltac:(cond_compute).
    stepLD F_6ef70 D_6ef70 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_6ef74 D_6ef74 ltac:(cond_compute).
    stepLD8 F_6ef80 D_6ef80 wp2.
    stepLD8 F_6ef84 D_6ef84 wp2.
    stepb_tk F_6ef88 D_6ef88 ltac:(apply c_eq_refl).
    stepLD8 F_6efa0 D_6efa0 rp2.
    stepLD8 F_6efa4 D_6efa4 rp2.
    stepb_tk F_6efa8 D_6efa8 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_6f028 D_6f028 (Z_to_bv 64 0x6bc10).
    stepLD8 F_6f02c D_6f02c code.
    stepn F_6f030 D_6f030. rewrite Hsp. sp_renorm.
    stepret F_6f034 D_6f034 (0x6bc10 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_6bc10 D_6bc10.
    stepn F_6bc14 D_6bc14.
    stepn F_6b974 D_6b974.
    stepn F_6b978 D_6b978.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
