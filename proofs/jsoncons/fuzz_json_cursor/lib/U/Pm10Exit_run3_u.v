(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10ExitBase_u Pm10Exit_run2_u Pm10_code_a5000_a6000_u Pm10_code_aa000_ab000_u Pm10_code_b6000_b7000_u             .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.

Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0xc4c58 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xc4c58 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xc4c58 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xc4c58 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xac404)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0xa71cc ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0xac8a4 : word) mem rom)
                 (mkst regs' (0xac404 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0xc4c58
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0xac954
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0xc4c58
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  -
    stepn F_aaa14 D_aaa14. rewrite Hsp. sp_renorm.
    stepST F_aaa18 D_aaa18 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0xa71cc) ltac:(sok_stack SOK).
    stepST F_aaa1c D_aaa1c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).

    stepn F_aaa20 D_aaa20.
    stepn F_aae3c D_aae3c. sp_renorm.
    stepST F_aae40 D_aae40 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0xac8b4) ltac:(sok_stack SOK).
    stepST F_aae44 D_aae44 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_aae48 D_aae48.
    stepn F_aae4c D_aae4c.
    stepn F_aae50 D_aae50.

    stepn F_aae54 D_aae54.
    stepn F_b6694 D_b6694.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_b6698 | reflexivity | exact D_b6698 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_b669c D_b669c ltac:(cond_compute).
    stepret F_b688c D_b688c (0xacce8 : word) ltac:(bveq).

    stepn F_aae58 D_aae58.
    stepLD8 F_aae5c D_aae5c (Z_to_bv 64 0xac8b4).
    stepLD8 F_aae60 D_aae60 code.
    stepn F_aae64 D_aae64. sp_renorm.
    stepret F_aae68 D_aae68 (0xac8b4 : word) ltac:(bveq).

    stepLD8 F_aaa24 D_aaa24 (Z_to_bv 64 0).
    stepb_ft F_aaa28 D_aaa28 ltac:(cond_compute).

    stepn F_aaa2c D_aaa2c.
    stepLD8 F_aaa30 D_aaa30 (Z_to_bv 64 0).
    stepb_tk F_aaa34 D_aaa34 ltac:(cond_compute).

    stepn F_aaa88 D_aaa88.
    stepLD8 F_aaa8c D_aaa8c (Z_to_bv 64 0xc4c58).
    stepb_ft F_aaa90 D_aaa90 ltac:(cond_compute).

    stepLD F_aaa94 D_aaa94 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_aaa98 D_aaa98 ltac:(cond_compute).

    stepLD8 F_aaaa4 D_aaaa4 (Z_to_bv 64 wp).
    stepLD8 F_aaaa8 D_aaaa8 (Z_to_bv 64 wb).
    stepb_ft F_aaaac D_aaaac ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).

    stepLD8 F_aaab0 D_aaab0 (Z_to_bv 64 0xac404).
    stepn F_aaab4 D_aaab4.
    stepn F_aaab8 D_aaab8.
    stepn F_aaabc D_aaabc.
    stepjr F_aaac0 D_aaac0 (Z_to_bv 64 0xac404) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0xc4c58 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa71cc)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0xc4c58 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0xc4c58 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0xc4c50) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc4b68)) ->
  file_clean mem 0xc4b68 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0xac954 : word) mem rom)
                 (mkst regs' (0xa6e70 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  -
    stepLD8 F_aaac4 D_aaac4 rp1.
    stepLD8 F_aaac8 D_aaac8 rp1.
    stepb_tk F_aaacc D_aaacc ltac:(apply c_eq_refl).

    stepn F_aaae4 D_aaae4.
    stepLD8 F_aaae8 D_aaae8 (Z_to_bv 64 0xc4b68).
    stepb_ft F_aaaec D_aaaec ltac:(cond_compute).
    stepLD F_aaaf0 D_aaaf0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_aaaf4 D_aaaf4 ltac:(cond_compute).
    stepLD8 F_aab00 D_aab00 wp2.
    stepLD8 F_aab04 D_aab04 wp2.
    stepb_tk F_aab08 D_aab08 ltac:(apply c_eq_refl).
    stepLD8 F_aab20 D_aab20 rp2.
    stepLD8 F_aab24 D_aab24 rp2.
    stepb_tk F_aab28 D_aab28 ltac:(apply c_eq_refl).

    stepLD8 F_aaba8 D_aaba8 (Z_to_bv 64 0xa71cc).
    stepLD8 F_aabac D_aabac code.
    stepn F_aabb0 D_aabb0. rewrite Hsp. sp_renorm.
    stepret F_aabb4 D_aabb4 (0xa71cc : word) ltac:(bveq).

    stepn F_a53dc D_a53dc.
    stepn F_a53e0 D_a53e0.
    stepn F_a5078 D_a5078.
    stepn F_a507c D_a507c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
