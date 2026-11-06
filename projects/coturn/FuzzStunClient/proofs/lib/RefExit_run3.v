(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import LibAtomic RefExitBase RefExit_run2 Ref_code_1b104_1c2fc Ref_code_1d2fc_1e5f0 Ref_code_235f0_2427c.
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

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0x26548 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x26548 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x26548 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x26548 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1df28)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x1bb64 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0x1dd84 : word) mem rom)
                 (mkst regs' (0x1df28 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x26548
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x1de34
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x26548
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr & Ghd & Glk & Gdso & Gil & Giw & Gib & Gir & Gie) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1dd84 D_1dd84. rewrite Hsp. sp_renorm.
    stepST F_1dd88 D_1dd88 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1bb64) ltac:(sok_stack SOK).
    stepST F_1dd8c D_1dd8c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1dd90 D_1dd90.
    stepn F_1e360 D_1e360. sp_renorm.
    stepST F_1e364 D_1e364 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x1dd94) ltac:(sok_stack SOK).
    stepST F_1e368 D_1e368 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_1e36c D_1e36c.
    stepn F_1e370 D_1e370.
    stepn F_1e374 D_1e374.
    (* [comment removed for export] *)
    stepn F_1e378 D_1e378.
    stepn F_23d80 D_23d80.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_23d84 | reflexivity | exact D_23d84 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_23d88 D_23d88 ltac:(cond_compute).
    stepret F_23f78 D_23f78 (0x1e37c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1e37c D_1e37c.
    stepLD8 F_1e380 D_1e380 (Z_to_bv 64 0x1dd94).
    stepLD8 F_1e384 D_1e384 code.
    stepn F_1e388 D_1e388. sp_renorm.
    stepret F_1e38c D_1e38c (0x1dd94 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_1dd94 D_1dd94 (Z_to_bv 64 0).
    stepb_ft F_1dd98 D_1dd98 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1dd9c D_1dd9c.
    stepLD8 F_1dda0 D_1dda0 (Z_to_bv 64 0x26458).
    stepb_ft F_1dda4 D_1dda4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_1dda8 D_1dda8 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1ddac D_1ddac ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1ddb8 D_1ddb8 (Z_to_bv 64 0).
    stepLD8 F_1ddbc D_1ddbc (Z_to_bv 64 0).
    stepb_tk F_1ddc0 D_1ddc0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1ddd8 D_1ddd8 (Z_to_bv 64 0).
    stepLD8 F_1dddc D_1dddc (Z_to_bv 64 0).
    stepb_tk F_1dde0 D_1dde0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1ddf8 D_1ddf8.
    stepLD8 F_1ddfc D_1ddfc (Z_to_bv 64 0x26548).
    stepb_ft F_1de00 D_1de00 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_1de04 D_1de04 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1de08 D_1de08 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1de14 D_1de14 (Z_to_bv 64 wp).
    stepLD8 F_1de18 D_1de18 (Z_to_bv 64 wb).
    stepb_ft F_1de1c D_1de1c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_1de20 D_1de20 (Z_to_bv 64 0x1df28).
    stepn F_1de24 D_1de24.
    stepn F_1de28 D_1de28.
    stepn F_1de2c D_1de2c.
    stepjr F_1de30 D_1de30 (Z_to_bv 64 0x1df28) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x26548 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1bb64)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0x26548 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0x26548 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0x26450) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x26368)) ->
  file_clean mem 0x26368 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x1de34 : word) mem rom)
                 (mkst regs' (0x1b900 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_1de34 D_1de34 rp1.
    stepLD8 F_1de38 D_1de38 rp1.
    stepb_tk F_1de3c D_1de3c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_1de54 D_1de54.
    stepLD8 F_1de58 D_1de58 (Z_to_bv 64 0x26368).
    stepb_ft F_1de5c D_1de5c ltac:(cond_compute).
    stepLD F_1de60 D_1de60 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1de64 D_1de64 ltac:(cond_compute).
    stepLD8 F_1de70 D_1de70 wp2.
    stepLD8 F_1de74 D_1de74 wp2.
    stepb_tk F_1de78 D_1de78 ltac:(apply c_eq_refl).
    stepLD8 F_1de90 D_1de90 rp2.
    stepLD8 F_1de94 D_1de94 rp2.
    stepb_tk F_1de98 D_1de98 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_1df18 D_1df18 (Z_to_bv 64 0x1bb64).
    stepLD8 F_1df1c D_1df1c code.
    stepn F_1df20 D_1df20. rewrite Hsp. sp_renorm.
    stepret F_1df24 D_1df24 (0x1bb64 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1bb64 D_1bb64.
    stepn F_1bb68 D_1bb68.
    stepn F_1b8f8 D_1b8f8.
    stepn F_1b8fc D_1b8fc.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
