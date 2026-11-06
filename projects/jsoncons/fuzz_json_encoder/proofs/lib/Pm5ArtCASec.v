(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac Pm5ArtCachePop Pm5ArtCombAlloc.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5_code_5f000_60000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_ca_sec_pre_fn : forall regs (M rom : word -> option byte) (sp ia s : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 s -> getr regs 13 = Z_to_bv 64 8 ->
  48 <= sp -> sp < 2 ^ 64 -> 65536 < s < 2 ^ 40 -> 0 <= ia -> ia + 4096 < 2 ^ 64 ->
  wrA M (sp - 48) 48 ->
  msteps ASEGS (mkst regs (0x5f850 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5f8f8 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 8)) 10 (Z_to_bv 64 (ia + 64)))
             11 (Z_to_bv 64 (ia + 688))) 12 (Z_to_bv 64 s)) 14 (Z_to_bv 64 (ia + 64))) 15 (Z_to_bv 64 65536))
          (0x5fb28 : word)
          (art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) rom).
Proof.
  intros regs M rom sp ia s H2 H10 H12 H13 Hsp Hsp' Hs Hia Hia' W.
  zstep F_5f808 D_5f808.
  zsd F_5f80c D_5f80c (sp - 8) (U (getr regs 1)) ltac:(rewok W).
  zsd F_5f810 D_5f810 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_5f814 D_5f814 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_5f818 D_5f818 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_5f81c D_5f81c (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_5f820 D_5f820 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_5f824 D_5f824.
  zstep F_5f828 D_5f828.
  zstep F_5f82c D_5f82c.
  zbtk F_5f830 D_5f830.
  zstep F_5f854 D_5f854.
  zstep F_5f858 D_5f858.
  zbtk F_5f85c D_5f85c.
  zstep F_5f87c D_5f87c.
  zbft F_5f880 D_5f880.
  zbtk F_5f884 D_5f884.
  zstep F_5f89c D_5f89c. zstep F_5f8a0 D_5f8a0. zstep F_5f8a4 D_5f8a4. zstep F_5f8a8 D_5f8a8.
  stepn F_5f8ac D_5f8ac.
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
    msteps ASEGS (mkst regs (0x5f8f8 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp + 48) /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v
    /\ getr regs' 19 = Z_to_bv 64 s3v /\ getr regs' 20 = Z_to_bv 64 s4v
    /\ (forall r : reg, art_pop_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw s0v s1v s2v s3v s4v H8 H2 Hsp Hsp' Cra Hret C0 C1 C2 C3 C4.
  eexists. split.
  - zstep F_5f8b0 D_5f8b0.
    zstep F_5f8b4 D_5f8b4.
    zbft F_5f8b8 D_5f8b8.
    stepn F_5f8bc D_5f8bc.
    zld F_5fa0c D_5fa0c (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_5fa10 D_5fa10 (sp + 32) C0.
    zld F_5fa14 D_5fa14 (sp + 24) C1.
    zld F_5fa18 D_5fa18 (sp + 16) C2.
    zld F_5fa1c D_5fa1c (sp + 8) C3.
    zld F_5fa20 D_5fa20 sp C4.
    zstep F_5fa24 D_5fa24.
    stepret F_5fa28 D_5fa28 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; reflexivity|]). post_kept.
Qed.
End FPX.
