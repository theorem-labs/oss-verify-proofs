(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_15000_16000 RCode_17000_18000 RCode_1c000_1d000 RCode_1d000_1d348.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac ExitBase Exit_run2.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 72)) 8%nat = Some (word_to_le_bytes 8 (rl dF_178c0 0x178c0)).
End GD_1.

Section VP1.
  Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL} {RD : RelocData RL} {RW : RelocRW RL RD}.
Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = rl dF_15800 0x1586c ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (rl dF_1771c 0x1771c) mem rom)
                 (mkst regs' (rl dF_178c0 0x178c0) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = rl dA_1f440 0x1f530
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = rl dF_1771c 0x177cc
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = rl dA_1f440 0x1f530
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  rl_dwin_bounds.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  rl_zaddr F1l; rl_zaddr F1wp; rl_zaddr F1wb; rl_zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1771c D_1771c. rewrite Hsp. sp_renorm.
    stepST F_17720 D_17720 (Z_to_bv 64 (bv_unsigned sp - 24)) (rl dF_15800 0x1586c) ltac:(sok_stack SOK).
    stepST F_17724 D_17724 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_17728 D_17728.
    stepn F_17d8c D_17d8c. sp_renorm.
    stepST F_17d90 D_17d90 (Z_to_bv 64 (bv_unsigned sp - 40)) (rl dF_1771c 0x1772c) ltac:(sok_stack SOK).
    stepST F_17d94 D_17d94 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_17d98 D_17d98.
    stepn F_17d9c D_17d9c.
    stepn F_17da0 D_17da0.
    (* [comment removed for export] *)
    stepn F_17da4 D_17da4.
    stepn F_1cf84 D_1cf84.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1cf88 | reflexivity | exact D_1cf88 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1cf8c D_1cf8c ltac:(rl_cond).
    stepretF F_1d17c D_1d17c F_17da8.
    (* [comment removed for export] *)
    stepn F_17da8 D_17da8.
    stepLD8 F_17dac D_17dac (rl dF_1771c 0x1772c).
    stepLD8 F_17db0 D_17db0 code.
    stepn F_17db4 D_17db4. sp_renorm.
    stepretF F_17db8 D_17db8 F_1772c.
    (* [comment removed for export] *)
    stepLD8 F_1772c D_1772c (Z_to_bv 64 0).
    stepb_ft F_17730 D_17730 ltac:(rl_cond).
    (* [comment removed for export] *)
    stepn F_17734 D_17734.
    stepLD8 F_17738 D_17738 (Z_to_bv 64 0).
    stepb_tk F_1773c D_1773c ltac:(rl_cond).
    (* [comment removed for export] *)
    stepn F_17790 D_17790.
    stepLD8 F_17794 D_17794 (rl dA_1f440 0x1f530).
    stepb_ft F_17798 D_17798 ltac:(rl_cond).
    (* [comment removed for export] *)
    stepLD F_1779c D_1779c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_177a0 D_177a0 ltac:(rl_cond).
    (* [comment removed for export] *)
    stepLD8 F_177ac D_177ac (Z_to_bv 64 wp).
    stepLD8 F_177b0 D_177b0 (Z_to_bv 64 wb).
    stepb_ft F_177b4 D_177b4 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_177b8 D_177b8 (rl dF_178c0 0x178c0).
    stepn F_177bc D_177bc.
    stepn F_177c0 D_177c0.
    stepn F_177c4 D_177c4.
    stepjrK F_177c8 D_177c8 F_178c0 ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VP1.

(* [comment removed for export] *)
Section VP2.
  Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL} {RD : RelocData RL} {RW : RelocRW RL RD}.
Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = rl dA_1f440 0x1f530 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (rl dF_15800 0x1586c)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (rl dA_1f440 0x1f528) 8%nat = Some (word_to_le_bytes 8 (rl dA_1f440 0x1f440)) ->
  file_clean mem (0x1f440 + dA_1f440) wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (rl dF_1771c 0x177cc) mem rom)
                 (mkst regs' (rl dF_15794 0x1579c) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  rl_dwin_bounds.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  rl_zaddr F1rp; rl_zaddr F1re. rl_zaddr F2l; rl_zaddr F2wp; rl_zaddr F2wb; rl_zaddr F2rp; rl_zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_177cc D_177cc rp1.
    stepLD8 F_177d0 D_177d0 rp1.
    stepb_tk F_177d4 D_177d4 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_177ec D_177ec.
    stepLD8 F_177f0 D_177f0 (rl dA_1f440 0x1f440).
    stepb_ft F_177f4 D_177f4 ltac:(rl_cond).
    stepLD F_177f8 D_177f8 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_177fc D_177fc ltac:(rl_cond).
    stepLD8 F_17808 D_17808 wp2.
    stepLD8 F_1780c D_1780c wp2.
    stepb_tk F_17810 D_17810 ltac:(apply c_eq_refl).
    stepLD8 F_17828 D_17828 rp2.
    stepLD8 F_1782c D_1782c rp2.
    stepb_tk F_17830 D_17830 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_178b0 D_178b0 (rl dF_15800 0x1586c).
    stepLD8 F_178b4 D_178b4 code.
    stepn F_178b8 D_178b8. rewrite Hsp. sp_renorm.
    stepretF F_178bc D_178bc F_1586c.
    (* [comment removed for export] *)
    stepn F_1586c D_1586c.
    stepn F_15870 D_15870.
    stepn F_15794 D_15794.
    stepn F_15798 D_15798.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VP2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
