(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_13084_14000 RCode_15000_16000 RCode_17000_18000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Import MuslTac ExitBase.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Definition mem_w1 (mem : word -> option byte) (sp ra s0 : word) (tid : Z) :=
  wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (rl dA_2f840 0x2f840) (word_to_le_bytes 4 (Z_to_bv 64 tid)).
End GD_1.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section GD_2.
  Context {RL : Reloc}.
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (rl dF_15800 0x15868)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (rl dF_157b4 0x157e4)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (rl dA_1e348 0x1e350)))
    (rl dA_1f630 0x1f678) [Z_to_bv 8 1].
End GD_2.

Section VP2.
  Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL} {RD : RelocData RL} {RW : RelocRW RL RD}.
Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = rl dF_15800 0x15868 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (rl dA_1e3b8 0x1e3e8) 8%nat = Some (word_to_le_bytes 8 (rl dA_1e348 0x1e358)) ->
  rdn RSEGS mem (rl dA_1e3b8 0x1e3f0) 8%nat = Some (word_to_le_bytes 8 (rl dA_1e348 0x1e350)) ->
  rdn RSEGS mem (rl dA_1e348 0x1e350) 8%nat = Some (word_to_le_bytes 8 (rl dF_13140 0x13140)) ->
  rdn RSEGS mem (rl dA_1f630 0x1f678) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (rl dA_1e368 0x1e390) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (rl dA_1e368 0x1e398) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (rl dF_157b4 0x157b4) mem rom)
                 (mkst regs' (rl dF_1771c 0x1771c) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = rl dF_15800 0x1586c
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  rl_dwin_bounds.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_157b4 D_157b4. rewrite Hsp. sp_renorm.
    stepST F_157b8 D_157b8 (Z_to_bv 64 (bv_unsigned sp - 24)) (rl dF_15800 0x15868) ltac:(sok_stack SOK).
    stepST F_157bc D_157bc (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_157c0 D_157c0 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_157c4 D_157c4.
    stepn F_157c8 D_157c8.
    stepLD8 F_157cc D_157cc (rl dA_1e348 0x1e358).
    stepLD8 F_157d0 D_157d0 (rl dA_1e348 0x1e350).
    (* [comment removed for export] *)
    stepb_ft F_157d4 D_157d4 ltac:(rl_cond).
    (* [comment removed for export] *)
    stepLD8 F_157d8 D_157d8 (rl dF_13140 0x13140).
    stepn F_157dc D_157dc.
    stepjrK F_157e0 D_157e0 F_13140 ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_13140 D_13140. sp_renorm.
    stepST F_13144 D_13144 (Z_to_bv 64 (bv_unsigned sp - 56)) (rl dF_157b4 0x157e4) ltac:(sok_stack SOK).
    stepST F_13148 D_13148 (Z_to_bv 64 (bv_unsigned sp - 64)) (rl dA_1e348 0x1e350) ltac:(sok_stack SOK).
    stepn F_1314c D_1314c.
    stepn F_13150 D_13150.
    stepn F_13154 D_13154.
    (* [comment removed for export] *)
    stepLBU F_13158 D_13158 (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_1315c D_1315c.
    stepb_tk F_13160 D_13160 ltac:(rl_cond).
    stepn F_1316c D_1316c.
    stepn F_13170 D_13170.
    stepn F_13174 D_13174.
    (* [comment removed for export] *)
    stepST F_13178 D_13178 (rl dA_1f630 0x1f678) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_1317c D_1317c.
    stepLD8 F_13180 D_13180 (Z_to_bv 64 0).
    stepb_tk F_13184 D_13184 ltac:(rl_cond).
    (* [comment removed for export] *)
    stepn F_131a0 D_131a0.
    stepLD8 F_131a4 D_131a4 (Z_to_bv 64 0).
    stepb_tk F_131a8 D_131a8 ltac:(rl_cond).
    (* [comment removed for export] *)
    stepLD8 F_131c0 D_131c0 (rl dF_157b4 0x157e4).
    stepLD8 F_131c4 D_131c4 (rl dA_1e348 0x1e350).
    stepn F_131c8 D_131c8. sp_renorm.
    stepretF F_131cc D_131cc F_157e4.
    (* [comment removed for export] *)
    stepn F_157e4 D_157e4.
    stepb_ft F_157e8 D_157e8 ltac:(rl_cond).
    stepLD8 F_157ec D_157ec (rl dF_15800 0x15868).
    stepLD8 F_157f0 D_157f0 code.
    stepLD8 F_157f4 D_157f4 s1v.
    stepn F_157f8 D_157f8. sp_renorm.
    (* [comment removed for export] *)
    stepn F_157fc D_157fc.
    stepretF F_157b0 D_157b0 F_15868.
    stepn F_15868 D_15868.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VP2.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
