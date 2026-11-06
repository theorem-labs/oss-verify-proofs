(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtLeaf ArtAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_415bc_42aa8 As0_code_3f03c_40650.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_gfa_popa_fn : forall regs (M rom : word -> option byte) (ia r chp n nf a0v : Z),
  getr regs 8 = Z_to_bv 64 r -> getr regs 9 = Z_to_bv 64 ia -> getr regs 10 = Z_to_bv 64 a0v -> getr regs 13 = Z_to_bv 64 chp -> getr regs 14 = Z_to_bv 64 n ->
  0 <= r -> r + 128 < 2 ^ 64 -> 0 <= nf < n -> n < 2 ^ 32 -> 0 <= ia < 2 ^ 64 -> 0 <= chp < 2 ^ 64 -> 0 <= a0v < 2 ^ 64 ->
  cellA M (r + 16) 8 nf ->
  msteps ASEGS (mkst regs (0x42468 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x425d4 : bv 64)%bv) 10 (Z_to_bv 64 ia)) 13 (Z_to_bv 64 r)) 14 (Z_to_bv 64 (n - nf))) 15 (Z_to_bv 64 nf)) 18 (Z_to_bv 64 a0v)) 21 (Z_to_bv 64 chp)) 22 (Z_to_bv 64 n)) (0x42620 : word) M rom).
Proof.
  intros regs M rom ia r chp n nf a0v H8 H9 H10 H13 H14 Hr Hr' Hnf Hn Hia Hchp Ha0 Cnf.
  zld F_42468 D_42468 (r + 16) Cnf.
  zbtk F_4246c D_4246c.
  zstep F_425b8 D_425b8. zstep F_425bc D_425bc. zstep F_425c0 D_425c0. zstep F_425c4 D_425c4. zstep F_425c8 D_425c8. zstep F_425cc D_425cc.
  stepn F_425d0 D_425d0.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_gfa_popb_fn : forall regs (M rom : word -> option byte) (r fa chp n nf2 a0v : Z),
  getr regs 10 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 r -> getr regs 18 = Z_to_bv 64 a0v -> getr regs 20 = Z_to_bv 64 fa -> getr regs 21 = Z_to_bv 64 chp -> getr regs 22 = Z_to_bv 64 n ->
  0 <= r -> r + 128 < 2 ^ 64 -> 0 <= fa -> fa + 4 * nf2 < 2 ^ 64 -> 0 <= chp -> chp + 4 * n < 2 ^ 64 -> 1 <= n <= nf2 -> nf2 < 2 ^ 40 -> 0 <= a0v < 2 ^ 64 ->
  wrA M r 128 -> cellA M (r + 16) 8 nf2 ->
  msteps ASEGS (mkst regs (0x425d4 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 a0v)) 11 (Z_to_bv 64 (chp + n * 2 ^ 2))) 13 (Z_to_bv 64 chp)) 14 (Z_to_bv 64 n)) 15 (Z_to_bv 64 ((nf2 - n) * 2 ^ 2))) 20 (Z_to_bv 64 (fa + (nf2 - n) * 2 ^ 2)))
          (0x4248c : word) (Wn 8 M (r + 16) (nf2 - n)) rom).
Proof.
  intros regs M rom r fa chp n nf2 a0v H10 H8 H18 H20 H21 H22 Hr Hr' Hfa Hfa' Hchp Hchp' Hn Hnf Ha0 Wr Cnf.
  zbft F_425d4 D_425d4.
  zld F_425d8 D_425d8 (r + 16) Cnf.
  zstep F_425dc D_425dc.
  zbft F_425e0 D_425e0.
  zstep F_425e4 D_425e4. zstep F_425e8 D_425e8.
  zsd F_425ec D_425ec (r + 16) (nf2 - n) ltac:(rewok Wr).
  zstep F_425f0 D_425f0.
  stepn F_425f4 D_425f4.
  zstep F_4247c D_4247c. zstep F_42480 D_42480. zstep F_42484 D_42484. zstep F_42488 D_42488.
  zret.
Qed.
End FPX.
