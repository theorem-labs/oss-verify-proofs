(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac EbtCachePop EbtCombAlloc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r41498_42984.
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
  msteps ASEGS (mkst regs (0x57d4c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x57df4 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 8)) 10 (Z_to_bv 64 (ia + 64)))
             11 (Z_to_bv 64 (ia + 688))) 12 (Z_to_bv 64 s)) 14 (Z_to_bv 64 (ia + 64))) 15 (Z_to_bv 64 65536))
          (0x58024 : word)
          (art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) rom).
Proof.
  intros regs M rom sp ia s H2 H10 H12 H13 Hsp Hsp' Hs Hia Hia' W.
  zstep F_57cfc D_57cfc.
  zsd F_57d00 D_57d00 (sp - 8) (U (getr regs 1)) ltac:(rewok W).
  zsd F_57d04 D_57d04 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_57d08 D_57d08 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_57d0c D_57d0c (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_57d10 D_57d10 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_57d14 D_57d14 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_57d18 D_57d18.
  zstep F_57d1c D_57d1c.
  zstep F_57d20 D_57d20.
  zbtk F_57d24 D_57d24.
  zstep F_57d48 D_57d48.
  zstep F_57d4c D_57d4c.
  zbtk F_57d50 D_57d50.
  zstep F_57d70 D_57d70.
  zbft F_57d74 D_57d74.
  zbtk F_57d78 D_57d78.
  zstep F_57d90 D_57d90. zstep F_57d94 D_57d94. zstep F_57d98 D_57d98. zstep F_57d9c D_57d9c.
  stepn F_57da0 D_57da0.
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
    msteps ASEGS (mkst regs (0x57df4 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp + 48) /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v
    /\ getr regs' 19 = Z_to_bv 64 s3v /\ getr regs' 20 = Z_to_bv 64 s4v
    /\ (forall r : reg, art_pop_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw s0v s1v s2v s3v s4v H8 H2 Hsp Hsp' Cra Hret C0 C1 C2 C3 C4.
  eexists. split.
  - zstep F_57da4 D_57da4.
    zstep F_57da8 D_57da8.
    zbft F_57dac D_57dac.
    stepn F_57db0 D_57db0.
    zld F_57f00 D_57f00 (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_57f04 D_57f04 (sp + 32) C0.
    zld F_57f08 D_57f08 (sp + 24) C1.
    zld F_57f0c D_57f0c (sp + 16) C2.
    zld F_57f10 D_57f10 (sp + 8) C3.
    zld F_57f14 D_57f14 sp C4.
    zstep F_57f18 D_57f18.
    stepret F_57f1c D_57f1c raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; reflexivity|]). post_kept.
Qed.
End FPX.
