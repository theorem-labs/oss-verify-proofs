(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  RefExitBase RefExit_run2 Ref_code_6717c_678ec Ref_code_6ab14_6afc8 Ref_code_75c60_75fa8       .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0x80b10 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x80b10 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x80b10 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x80b10 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6afc8)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x678e4 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0x6ab68 : word) mem rom)
                 (mkst regs' (0x6afc8 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x80b10
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x6ac18
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x80b10
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_6ab68 D_6ab68. rewrite Hsp. sp_renorm.
    stepST F_6ab6c D_6ab6c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x678e4) ltac:(sok_stack SOK).
    stepST F_6ab70 D_6ab70 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_6ab74 D_6ab74.
    stepn F_6aefc D_6aefc. sp_renorm.
    stepST F_6af00 D_6af00 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x6ab78) ltac:(sok_stack SOK).
    stepST F_6af04 D_6af04 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_6af08 D_6af08.
    stepn F_6af0c D_6af0c.
    stepn F_6af10 D_6af10.
    (* [comment removed for export] *)
    stepn F_6af14 D_6af14.
    stepn F_75c60 D_75c60.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_75c64 | reflexivity | exact D_75c64 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_75c68 D_75c68 ltac:(cond_compute).
    stepret F_75e58 D_75e58 (0x6af18 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_6af18 D_6af18.
    stepLD8 F_6af1c D_6af1c (Z_to_bv 64 0x6ab78).
    stepLD8 F_6af20 D_6af20 code.
    stepn F_6af24 D_6af24. sp_renorm.
    stepret F_6af28 D_6af28 (0x6ab78 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_6ab78 D_6ab78 (Z_to_bv 64 0).
    stepb_ft F_6ab7c D_6ab7c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_6ab80 D_6ab80.
    stepLD8 F_6ab84 D_6ab84 (Z_to_bv 64 0).
    stepb_tk F_6ab88 D_6ab88 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_6abdc D_6abdc.
    stepLD8 F_6abe0 D_6abe0 (Z_to_bv 64 0x80b10).
    stepb_ft F_6abe4 D_6abe4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_6abe8 D_6abe8 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_6abec D_6abec ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_6abf8 D_6abf8 (Z_to_bv 64 wp).
    stepLD8 F_6abfc D_6abfc (Z_to_bv 64 wb).
    stepb_ft F_6ac00 D_6ac00 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_6ac04 D_6ac04 (Z_to_bv 64 0x6afc8).
    stepn F_6ac08 D_6ac08.
    stepn F_6ac0c D_6ac0c.
    stepn F_6ac10 D_6ac10.
    stepjr F_6ac14 D_6ac14 (Z_to_bv 64 0x6afc8) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x80b10 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x678e4)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0x80b10 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0x80b10 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0x80b08) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x80a20)) ->
  file_clean mem 0x80a20 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x6ac18 : word) mem rom)
                 (mkst regs' (0x67650 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_6ac18 D_6ac18 rp1.
    stepLD8 F_6ac1c D_6ac1c rp1.
    stepb_tk F_6ac20 D_6ac20 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_6ac38 D_6ac38.
    stepLD8 F_6ac3c D_6ac3c (Z_to_bv 64 0x80a20).
    stepb_ft F_6ac40 D_6ac40 ltac:(cond_compute).
    stepLD F_6ac44 D_6ac44 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_6ac48 D_6ac48 ltac:(cond_compute).
    stepLD8 F_6ac54 D_6ac54 wp2.
    stepLD8 F_6ac58 D_6ac58 wp2.
    stepb_tk F_6ac5c D_6ac5c ltac:(apply c_eq_refl).
    stepLD8 F_6ac74 D_6ac74 rp2.
    stepLD8 F_6ac78 D_6ac78 rp2.
    stepb_tk F_6ac7c D_6ac7c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_6acfc D_6acfc (Z_to_bv 64 0x678e4).
    stepLD8 F_6ad00 D_6ad00 code.
    stepn F_6ad04 D_6ad04. rewrite Hsp. sp_renorm.
    stepret F_6ad08 D_6ad08 (0x678e4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_678e4 D_678e4.
    stepn F_678e8 D_678e8.
    stepn F_67648 D_67648.
    stepn F_6764c D_6764c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
