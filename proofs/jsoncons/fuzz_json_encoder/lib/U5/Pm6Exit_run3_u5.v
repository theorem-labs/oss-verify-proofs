(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6ExitBase_u5 Pm6Exit_run2_u5 Pm6_code_a9000_aa000_u5 Pm6_code_af000_b0000_u5 Pm6_code_bb000_bc000_u5             .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.


(* [comment removed for export] *)
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0xcb428 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xcb428 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xcb428 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xcb428 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb2bb8)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0xad980 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0xb3058 : word) mem rom)
                 (mkst regs' (0xb2bb8 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0xcb428
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0xb3108
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0xcb428
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_af630 D_af630. rewrite Hsp. sp_renorm.
    stepST F_af634 D_af634 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0xad980) ltac:(sok_stack SOK).
    stepST F_af638 D_af638 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_af63c D_af63c.
    stepn F_afa58 D_afa58. sp_renorm.
    stepST F_afa5c D_afa5c (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0xb3068) ltac:(sok_stack SOK).
    stepST F_afa60 D_afa60 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_afa64 D_afa64.
    stepn F_afa68 D_afa68.
    stepn F_afa6c D_afa6c.
    (* [comment removed for export] *)
    stepn F_afa70 D_afa70.
    stepn F_bb2b0 D_bb2b0.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_bb2b4 | reflexivity | exact D_bb2b4 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_bb2b8 D_bb2b8 ltac:(cond_compute).
    stepret F_bb4a8 D_bb4a8 (0xb349c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_afa74 D_afa74.
    stepLD8 F_afa78 D_afa78 (Z_to_bv 64 0xb3068).
    stepLD8 F_afa7c D_afa7c code.
    stepn F_afa80 D_afa80. sp_renorm.
    stepret F_afa84 D_afa84 (0xb3068 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_af640 D_af640 (Z_to_bv 64 0).
    stepb_ft F_af644 D_af644 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_af648 D_af648.
    stepLD8 F_af64c D_af64c (Z_to_bv 64 0).
    stepb_tk F_af650 D_af650 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_af6a4 D_af6a4.
    stepLD8 F_af6a8 D_af6a8 (Z_to_bv 64 0xcb428).
    stepb_ft F_af6ac D_af6ac ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_af6b0 D_af6b0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_af6b4 D_af6b4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_af6c0 D_af6c0 (Z_to_bv 64 wp).
    stepLD8 F_af6c4 D_af6c4 (Z_to_bv 64 wb).
    stepb_ft F_af6c8 D_af6c8 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_af6cc D_af6cc (Z_to_bv 64 0xb2bb8).
    stepn F_af6d0 D_af6d0.
    stepn F_af6d4 D_af6d4.
    stepn F_af6d8 D_af6d8.
    stepjr F_af6dc D_af6dc (Z_to_bv 64 0xb2bb8) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0xcb428 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xad980)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0xcb428 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0xcb428 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0xcb420) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xcb338)) ->
  file_clean mem 0xcb338 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0xb3108 : word) mem rom)
                 (mkst regs' (0xad624 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_af6e0 D_af6e0 rp1.
    stepLD8 F_af6e4 D_af6e4 rp1.
    stepb_tk F_af6e8 D_af6e8 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_af700 D_af700.
    stepLD8 F_af704 D_af704 (Z_to_bv 64 0xcb338).
    stepb_ft F_af708 D_af708 ltac:(cond_compute).
    stepLD F_af70c D_af70c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_af710 D_af710 ltac:(cond_compute).
    stepLD8 F_af71c D_af71c wp2.
    stepLD8 F_af720 D_af720 wp2.
    stepb_tk F_af724 D_af724 ltac:(apply c_eq_refl).
    stepLD8 F_af73c D_af73c rp2.
    stepLD8 F_af740 D_af740 rp2.
    stepb_tk F_af744 D_af744 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_af7c4 D_af7c4 (Z_to_bv 64 0xad980).
    stepLD8 F_af7c8 D_af7c8 code.
    stepn F_af7cc D_af7cc. rewrite Hsp. sp_renorm.
    stepret F_af7d0 D_af7d0 (0xad980 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_a9ff8 D_a9ff8.
    stepn F_a9ffc D_a9ffc.
    stepn F_a9c94 D_a9c94.
    stepn F_a9c98 D_a9c98.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
