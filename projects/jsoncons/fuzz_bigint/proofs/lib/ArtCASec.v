(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac ArtCachePop ArtCombAlloc.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_415bc_42aa8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_ca_sec_pre_fn : forall regs (M rom : word -> option byte) (sp ia s : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 s -> getr regs 13 = Z_to_bv 64 8 ->
  48 <= sp -> sp < 2 ^ 64 -> 65536 < s < 2 ^ 40 -> 0 <= ia -> ia + 4096 < 2 ^ 64 ->
  wrA M (sp - 48) 48 ->
  msteps ASEGS (mkst regs (0x41ac8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x41b70 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 8)) 10 (Z_to_bv 64 (ia + 64)))
             11 (Z_to_bv 64 (ia + 688))) 12 (Z_to_bv 64 s)) 14 (Z_to_bv 64 (ia + 64))) 15 (Z_to_bv 64 65536))
          (0x41da0 : word)
          (art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) rom).
Proof.
  intros regs M rom sp ia s H2 H10 H12 H13 Hsp Hsp' Hs Hia Hia' W.
  zstep F_41ac8 D_41ac8.
  zsd F_41acc D_41acc (sp - 8) (U (getr regs 1)) ltac:(rewok W).
  zsd F_41ad0 D_41ad0 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_41ad4 D_41ad4 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_41ad8 D_41ad8 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_41adc D_41adc (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_41ae0 D_41ae0 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_41ae4 D_41ae4.
  zstep F_41ae8 D_41ae8.
  zstep F_41aec D_41aec.
  zbtk F_41af0 D_41af0.
  zstep F_41b14 D_41b14.
  zstep F_41b18 D_41b18.
  zbtk F_41b1c D_41b1c.
  zstep F_41b3c D_41b3c.
  zbft F_41b40 D_41b40.
  zbtk F_41b44 D_41b44.
  zstep F_41b5c D_41b5c. zstep F_41b60 D_41b60. zstep F_41b64 D_41b64. zstep F_41b68 D_41b68.
  stepn F_41b6c D_41b6c.
  zret.
Qed.

(* [comment removed for export] *)
#[local] Ltac post_kept :=
  intros r Hr; unfold art_pop_kept in Hr; destruct Hr as (?&?&?&?&?&?&?&?&?); gres; try reflexivity;
  repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.

Lemma art_ca_sec_post : forall regs (M rom : word -> option byte) (sp : Z) (raw : word) (s0v s1v s2v s3v s4v : Z),
  getr regs 8 = Z_to_bv 64 8 -> getr regs 2 = Z_to_bv 64 sp -> 0 <= sp -> sp + 48 < 2 ^ 64 ->
  cellA M (sp + 40) 8 (bv_unsigned raw) -> ret_ok raw ->
  cellA M (sp + 32) 8 s0v -> cellA M (sp + 24) 8 s1v -> cellA M (sp + 16) 8 s2v -> cellA M (sp + 8) 8 s3v -> cellA M sp 8 s4v ->
  exists regs',
    msteps ASEGS (mkst regs (0x41b70 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp + 48) /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v
    /\ getr regs' 19 = Z_to_bv 64 s3v /\ getr regs' 20 = Z_to_bv 64 s4v
    /\ (forall r : reg, art_pop_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw s0v s1v s2v s3v s4v H8 H2 Hsp Hsp' Cra Hret C0 C1 C2 C3 C4.
  eexists. split.
  - zstep F_41b70 D_41b70.
    zstep F_41b74 D_41b74.
    zbft F_41b78 D_41b78.
    stepn F_41b7c D_41b7c.
    zld F_41ccc D_41ccc (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_41cd0 D_41cd0 (sp + 32) C0.
    zld F_41cd4 D_41cd4 (sp + 24) C1.
    zld F_41cd8 D_41cd8 (sp + 16) C2.
    zld F_41cdc D_41cdc (sp + 8) C3.
    zld F_41ce0 D_41ce0 sp C4.
    zstep F_41ce4 D_41ce4.
    stepret F_41ce8 D_41ce8 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; reflexivity|]). post_kept.
Qed.
End FPX.
