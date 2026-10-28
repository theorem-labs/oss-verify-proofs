(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCachePop_b BatCombAlloc_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r41498_42984_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_ca_sec_pre_fn : forall regs (M rom : word -> option byte) (sp ia s : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 s -> getr regs 13 = Z_to_bv 64 8 ->
  48 <= sp -> sp < 2 ^ 64 -> 65536 < s < 2 ^ 40 -> 0 <= ia -> ia + 4096 < 2 ^ 64 ->
  wrA M (sp - 48) 48 ->
  msteps ASEGS (mkst regs (0x56d3c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x56de4 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 8)) 10 (Z_to_bv 64 (ia + 64)))
             11 (Z_to_bv 64 (ia + 688))) 12 (Z_to_bv 64 s)) 14 (Z_to_bv 64 (ia + 64))) 15 (Z_to_bv 64 65536))
          (0x57014 : word)
          (art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) rom).
Proof.
  intros regs M rom sp ia s H2 H10 H12 H13 Hsp Hsp' Hs Hia Hia' W.
  zstep F_56924 D_56924.
  zsd F_56928 D_56928 (sp - 8) (U (getr regs 1)) ltac:(rewok W).
  zsd F_5692c D_5692c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_56930 D_56930 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_56934 D_56934 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_56938 D_56938 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_5693c D_5693c (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_56940 D_56940.
  zstep F_56944 D_56944.
  zstep F_56948 D_56948.
  zbtk F_5694c D_5694c.
  zstep F_56970 D_56970.
  zstep F_56974 D_56974.
  zbtk F_56978 D_56978.
  zstep F_56998 D_56998.
  zbft F_5699c D_5699c.
  zbtk F_569a0 D_569a0.
  zstep F_569b8 D_569b8. zstep F_569bc D_569bc. zstep F_569c0 D_569c0. zstep F_569c4 D_569c4.
  stepn F_569c8 D_569c8.
  zret.
Qed.

(* [comment removed for export] *)
#[local] Ltac post_kept :=
  intros r Hr; unfold art_pop_kept in Hr; destruct Hr as (?&?&?&?&?&?&?&?&?); gres; try reflexivity;
  repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.

#[using="Type"] Lemma art_ca_sec_post : forall regs (M rom : word -> option byte) (sp : Z) (raw : word) (s0v s1v s2v s3v s4v : Z),
  getr regs 8 = Z_to_bv 64 8 -> getr regs 2 = Z_to_bv 64 sp -> 0 <= sp -> sp + 48 < 2 ^ 64 ->
  cellA M (sp + 40) 8 (bv_unsigned raw) -> ret_ok raw ->
  cellA M (sp + 32) 8 s0v -> cellA M (sp + 24) 8 s1v -> cellA M (sp + 16) 8 s2v -> cellA M (sp + 8) 8 s3v -> cellA M sp 8 s4v ->
  exists regs',
    msteps ASEGS (mkst regs (0x56de4 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp + 48) /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v
    /\ getr regs' 19 = Z_to_bv 64 s3v /\ getr regs' 20 = Z_to_bv 64 s4v
    /\ (forall r : reg, art_pop_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw s0v s1v s2v s3v s4v H8 H2 Hsp Hsp' Cra Hret C0 C1 C2 C3 C4.
  eexists. split.
  - zstep F_569cc D_569cc.
    zstep F_569d0 D_569d0.
    zbft F_569d4 D_569d4.
    stepn F_569d8 D_569d8.
    zld F_56b28 D_56b28 (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_56b2c D_56b2c (sp + 32) C0.
    zld F_56b30 D_56b30 (sp + 24) C1.
    zld F_56b34 D_56b34 (sp + 16) C2.
    zld F_56b38 D_56b38 (sp + 8) C3.
    zld F_56b3c D_56b3c sp C4.
    zstep F_56b40 D_56b40.
    stepret F_56b44 D_56b44 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; reflexivity|]). post_kept.
Qed.
End FPX.
