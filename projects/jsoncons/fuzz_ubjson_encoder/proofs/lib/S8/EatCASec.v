(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac EatCachePop EatCombAlloc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_ca_sec_pre_fn : forall regs (M rom : word -> option byte) (sp ia s : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 s -> getr regs 13 = Z_to_bv 64 8 ->
  48 <= sp -> sp < 2 ^ 64 -> 65536 < s < 2 ^ 40 -> 0 <= ia -> ia + 4096 < 2 ^ 64 ->
  wrA M (sp - 48) 48 ->
  msteps ASEGS (mkst regs (0x57524 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x575cc : bv 64)%bv) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 8)) 10 (Z_to_bv 64 (ia + 64)))
             11 (Z_to_bv 64 (ia + 688))) 12 (Z_to_bv 64 s)) 14 (Z_to_bv 64 (ia + 64))) 15 (Z_to_bv 64 65536))
          (0x577fc : word)
          (art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) rom).
Proof.
  intros regs M rom sp ia s H2 H10 H12 H13 Hsp Hsp' Hs Hia Hia' W.
  zstep F_574d4 D_574d4.
  zsd F_574d8 D_574d8 (sp - 8) (U (getr regs 1)) ltac:(rewok W).
  zsd F_574dc D_574dc (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_574e0 D_574e0 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_574e4 D_574e4 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_574e8 D_574e8 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_574ec D_574ec (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_574f0 D_574f0.
  zstep F_574f4 D_574f4.
  zstep F_574f8 D_574f8.
  zbtk F_574fc D_574fc.
  zstep F_57520 D_57520.
  zstep F_57524 D_57524.
  zbtk F_57528 D_57528.
  zstep F_57548 D_57548.
  zbft F_5754c D_5754c.
  zbtk F_57550 D_57550.
  zstep F_57568 D_57568. zstep F_5756c D_5756c. zstep F_57570 D_57570. zstep F_57574 D_57574.
  stepn F_57578 D_57578.
  zret.
Qed.

#[local] Ltac post_kept :=
  intros r Hr; unfold art_pop_kept in Hr; destruct Hr as (?&?&?&?&?&?&?&?&?); gres; try reflexivity;
  repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.

#[using="Type"] Lemma art_ca_sec_post : forall regs (M rom : word -> option byte) (sp : Z) (raw : word) (s0v s1v s2v s3v s4v : Z),
  getr regs 8 = Z_to_bv 64 8 -> getr regs 2 = Z_to_bv 64 sp -> 0 <= sp -> sp + 48 < 2 ^ 64 ->
  cellA M (sp + 40) 8 (bv_unsigned raw) -> ret_ok raw ->
  cellA M (sp + 32) 8 s0v -> cellA M (sp + 24) 8 s1v -> cellA M (sp + 16) 8 s2v -> cellA M (sp + 8) 8 s3v -> cellA M sp 8 s4v ->
  exists regs',
    msteps ASEGS (mkst regs (0x575cc : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp + 48) /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v
    /\ getr regs' 19 = Z_to_bv 64 s3v /\ getr regs' 20 = Z_to_bv 64 s4v
    /\ (forall r : reg, art_pop_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw s0v s1v s2v s3v s4v H8 H2 Hsp Hsp' Cra Hret C0 C1 C2 C3 C4.
  eexists. split.
  - zstep F_5757c D_5757c.
    zstep F_57580 D_57580.
    zbft F_57584 D_57584.
    stepn F_57588 D_57588.
    zld F_576d8 D_576d8 (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_576dc D_576dc (sp + 32) C0.
    zld F_576e0 D_576e0 (sp + 24) C1.
    zld F_576e4 D_576e4 (sp + 16) C2.
    zld F_576e8 D_576e8 (sp + 8) C3.
    zld F_576ec D_576ec sp C4.
    zstep F_576f0 D_576f0.
    stepret F_576f4 D_576f4 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; reflexivity|]). post_kept.
Qed.
End FPX.
