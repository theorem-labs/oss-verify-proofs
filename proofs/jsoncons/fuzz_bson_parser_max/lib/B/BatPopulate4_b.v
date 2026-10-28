(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r41498_42984_b Ba0_code_r3ef18_4052c_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_gfa_popa_fn : forall regs (M rom : word -> option byte) (ia r chp n nf a0v : Z),
  getr regs 8 = Z_to_bv 64 r -> getr regs 9 = Z_to_bv 64 ia -> getr regs 10 = Z_to_bv 64 a0v -> getr regs 13 = Z_to_bv 64 chp -> getr regs 14 = Z_to_bv 64 n ->
  0 <= r -> r + 128 < 2 ^ 64 -> 0 <= nf < n -> n < 2 ^ 32 -> 0 <= ia < 2 ^ 64 -> 0 <= chp < 2 ^ 64 -> 0 <= a0v < 2 ^ 64 ->
  cellA M (r + 16) 8 nf ->
  msteps ASEGS (mkst regs (0x576dc : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x57848 : bv 64)%bv) 10 (Z_to_bv 64 ia)) 13 (Z_to_bv 64 r)) 14 (Z_to_bv 64 (n - nf))) 15 (Z_to_bv 64 nf)) 18 (Z_to_bv 64 a0v)) 21 (Z_to_bv 64 chp)) 22 (Z_to_bv 64 n)) (0x57894 : word) M rom).
Proof.
  intros regs M rom ia r chp n nf a0v H8 H9 H10 H13 H14 Hr Hr' Hnf Hn Hia Hchp Ha0 Cnf.
  zld F_572c4 D_572c4 (r + 16) Cnf.
  zbtk F_572c8 D_572c8.
  zstep F_57414 D_57414. zstep F_57418 D_57418. zstep F_5741c D_5741c. zstep F_57420 D_57420. zstep F_57424 D_57424. zstep F_57428 D_57428.
  stepn F_5742c D_5742c.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_gfa_popb_fn : forall regs (M rom : word -> option byte) (r fa chp n nf2 a0v : Z),
  getr regs 10 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 r -> getr regs 18 = Z_to_bv 64 a0v -> getr regs 20 = Z_to_bv 64 fa -> getr regs 21 = Z_to_bv 64 chp -> getr regs 22 = Z_to_bv 64 n ->
  0 <= r -> r + 128 < 2 ^ 64 -> 0 <= fa -> fa + 4 * nf2 < 2 ^ 64 -> 0 <= chp -> chp + 4 * n < 2 ^ 64 -> 1 <= n <= nf2 -> nf2 < 2 ^ 40 -> 0 <= a0v < 2 ^ 64 ->
  wrA M r 128 -> cellA M (r + 16) 8 nf2 ->
  msteps ASEGS (mkst regs (0x57848 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 a0v)) 11 (Z_to_bv 64 (chp + n * 2 ^ 2))) 13 (Z_to_bv 64 chp)) 14 (Z_to_bv 64 n)) 15 (Z_to_bv 64 ((nf2 - n) * 2 ^ 2))) 20 (Z_to_bv 64 (fa + (nf2 - n) * 2 ^ 2)))
          (0x57700 : word) (Wn 8 M (r + 16) (nf2 - n)) rom).
Proof.
  intros regs M rom r fa chp n nf2 a0v H10 H8 H18 H20 H21 H22 Hr Hr' Hfa Hfa' Hchp Hchp' Hn Hnf Ha0 Wr Cnf.
  zbft F_57430 D_57430.
  zld F_57434 D_57434 (r + 16) Cnf.
  zstep F_57438 D_57438.
  zbft F_5743c D_5743c.
  zstep F_57440 D_57440. zstep F_57444 D_57444.
  zsd F_57448 D_57448 (r + 16) (nf2 - n) ltac:(rewok Wr).
  zstep F_5744c D_5744c.
  stepn F_57450 D_57450.
  zstep F_572d8 D_572d8. zstep F_572dc D_572dc. zstep F_572e0 D_572e0. zstep F_572e4 D_572e4.
  zret.
Qed.
End FPX.
