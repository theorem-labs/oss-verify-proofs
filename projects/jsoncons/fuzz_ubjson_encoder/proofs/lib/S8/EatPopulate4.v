(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtTac EatLeaf EatAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r41498_42984 Ea0_code_r3ef18_4052c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000080. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_gfa_popa_fn : forall regs (M rom : word -> option byte) (ia r chp n nf a0v : Z),
  getr regs 8 = Z_to_bv 64 r -> getr regs 9 = Z_to_bv 64 ia -> getr regs 10 = Z_to_bv 64 a0v -> getr regs 13 = Z_to_bv 64 chp -> getr regs 14 = Z_to_bv 64 n ->
  0 <= r -> r + 128 < 2 ^ 64 -> 0 <= nf < n -> n < 2 ^ 32 -> 0 <= ia < 2 ^ 64 -> 0 <= chp < 2 ^ 64 -> 0 <= a0v < 2 ^ 64 ->
  cellA M (r + 16) 8 nf ->
  msteps ASEGS (mkst regs (0x57ec4 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x58030 : bv 64)%bv) 10 (Z_to_bv 64 ia)) 13 (Z_to_bv 64 r)) 14 (Z_to_bv 64 (n - nf))) 15 (Z_to_bv 64 nf)) 18 (Z_to_bv 64 a0v)) 21 (Z_to_bv 64 chp)) 22 (Z_to_bv 64 n)) (0x5807c : word) M rom).
Proof.
  intros regs M rom ia r chp n nf a0v H8 H9 H10 H13 H14 Hr Hr' Hnf Hn Hia Hchp Ha0 Cnf.
  zld F_57e74 D_57e74 (r + 16) Cnf.
  zbtk F_57e78 D_57e78.
  zstep F_57fc4 D_57fc4. zstep F_57fc8 D_57fc8. zstep F_57fcc D_57fcc. zstep F_57fd0 D_57fd0. zstep F_57fd4 D_57fd4. zstep F_57fd8 D_57fd8.
  stepn F_57fdc D_57fdc.
  zret.
Qed.

#[using="Type"] Lemma art_gfa_popb_fn : forall regs (M rom : word -> option byte) (r fa chp n nf2 a0v : Z),
  getr regs 10 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 r -> getr regs 18 = Z_to_bv 64 a0v -> getr regs 20 = Z_to_bv 64 fa -> getr regs 21 = Z_to_bv 64 chp -> getr regs 22 = Z_to_bv 64 n ->
  0 <= r -> r + 128 < 2 ^ 64 -> 0 <= fa -> fa + 4 * nf2 < 2 ^ 64 -> 0 <= chp -> chp + 4 * n < 2 ^ 64 -> 1 <= n <= nf2 -> nf2 < 2 ^ 40 -> 0 <= a0v < 2 ^ 64 ->
  wrA M r 128 -> cellA M (r + 16) 8 nf2 ->
  msteps ASEGS (mkst regs (0x58030 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 a0v)) 11 (Z_to_bv 64 (chp + n * 2 ^ 2))) 13 (Z_to_bv 64 chp)) 14 (Z_to_bv 64 n)) 15 (Z_to_bv 64 ((nf2 - n) * 2 ^ 2))) 20 (Z_to_bv 64 (fa + (nf2 - n) * 2 ^ 2)))
          (0x57ee8 : word) (Wn 8 M (r + 16) (nf2 - n)) rom).
Proof.
  intros regs M rom r fa chp n nf2 a0v H10 H8 H18 H20 H21 H22 Hr Hr' Hfa Hfa' Hchp Hchp' Hn Hnf Ha0 Wr Cnf.
  zbft F_57fe0 D_57fe0.
  zld F_57fe4 D_57fe4 (r + 16) Cnf.
  zstep F_57fe8 D_57fe8.
  zbft F_57fec D_57fec.
  zstep F_57ff0 D_57ff0. zstep F_57ff4 D_57ff4.
  zsd F_57ff8 D_57ff8 (r + 16) (nf2 - n) ltac:(rewok Wr).
  zstep F_57ffc D_57ffc.
  stepn F_58000 D_58000.
  zstep F_57e88 D_57e88. zstep F_57e8c D_57e8c. zstep F_57e90 D_57e90. zstep F_57e94 D_57e94.
  zret.
Qed.
End FPX.
