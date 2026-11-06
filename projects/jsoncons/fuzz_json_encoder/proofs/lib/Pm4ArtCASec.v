(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac Pm4ArtCachePop Pm4ArtCombAlloc.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4_code_5e000_5f000 Pm4_code_5f000_60000.
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
  msteps ASEGS (mkst regs (0x5ef80 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5f028 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 8)) 10 (Z_to_bv 64 (ia + 64)))
             11 (Z_to_bv 64 (ia + 688))) 12 (Z_to_bv 64 s)) 14 (Z_to_bv 64 (ia + 64))) 15 (Z_to_bv 64 65536))
          (0x5f258 : word)
          (art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) rom).
Proof.
  intros regs M rom sp ia s H2 H10 H12 H13 Hsp Hsp' Hs Hia Hia' W.
  zstep F_5ef30 D_5ef30.
  zsd F_5ef34 D_5ef34 (sp - 8) (U (getr regs 1)) ltac:(rewok W).
  zsd F_5ef38 D_5ef38 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_5ef3c D_5ef3c (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_5ef40 D_5ef40 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_5ef44 D_5ef44 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_5ef48 D_5ef48 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_5ef4c D_5ef4c.
  zstep F_5ef50 D_5ef50.
  zstep F_5ef54 D_5ef54.
  zbtk F_5ef58 D_5ef58.
  zstep F_5ef7c D_5ef7c.
  zstep F_5ef80 D_5ef80.
  zbtk F_5ef84 D_5ef84.
  zstep F_5efa4 D_5efa4.
  zbft F_5efa8 D_5efa8.
  zbtk F_5efac D_5efac.
  zstep F_5efc4 D_5efc4. zstep F_5efc8 D_5efc8. zstep F_5efcc D_5efcc. zstep F_5efd0 D_5efd0.
  stepn F_5efd4 D_5efd4.
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
    msteps ASEGS (mkst regs (0x5f028 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp + 48) /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v
    /\ getr regs' 19 = Z_to_bv 64 s3v /\ getr regs' 20 = Z_to_bv 64 s4v
    /\ (forall r : reg, art_pop_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw s0v s1v s2v s3v s4v H8 H2 Hsp Hsp' Cra Hret C0 C1 C2 C3 C4.
  eexists. split.
  - zstep F_5efd8 D_5efd8.
    zstep F_5efdc D_5efdc.
    zbft F_5efe0 D_5efe0.
    stepn F_5efe4 D_5efe4.
    zld F_5f134 D_5f134 (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_5f138 D_5f138 (sp + 32) C0.
    zld F_5f13c D_5f13c (sp + 24) C1.
    zld F_5f140 D_5f140 (sp + 16) C2.
    zld F_5f144 D_5f144 (sp + 8) C3.
    zld F_5f148 D_5f148 sp C4.
    zstep F_5f14c D_5f14c.
    stepret F_5f150 D_5f150 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; reflexivity|]). post_kept.
Qed.
End FPX.
