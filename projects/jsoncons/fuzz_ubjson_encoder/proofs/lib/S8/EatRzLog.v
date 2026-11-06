(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_rz_rodata (M : word -> option byte) : Prop :=
  cellA M 0x10448 8 0x218a392cd3d5dbf /\ cellA M 0x105c8 1 4 /\ cellA M 0x105f1 1 11.

Definition art_rz_kept (r : reg) : Prop := r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Section FPX. Context {fx : PropExec.FPState}.

#[local] Ltac post_kept := intros r Hr; unfold art_rz_kept in Hr; destruct Hr as (?&?&?&?&?); kept_solve.

Ltac zlbu F D a HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | zaddr a; exact HYP ] | step_simpl; vnorm].

#[using="Type"] Lemma art_rz2log_16_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x583ec : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 0))
                      12 (Z_to_bv 64 4)) 13 (Z_to_bv 64 16)) 14 (Z_to_bv 64 16)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_5839c D_5839c.
  zsd F_583a0 D_583a0 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10448 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105c8 1 4) by (unfold apart in *; recell R2).
  zstep F_583a4 D_583a4. zstep F_583a8 D_583a8. zstep F_583ac D_583ac.
  zbft F_583b0 D_583b0.
  zstep F_583b4 D_583b4. zstep F_583b8 D_583b8.
  zbft F_583bc D_583bc.
  zstep F_583c0 D_583c0. zstep F_583c4 D_583c4.
  zbft F_583c8 D_583c8.
  zstep F_583cc D_583cc. zstep F_583d0 D_583d0.
  zld F_583d4 D_583d4 0x10448 C1.
  zstep F_583d8 D_583d8. zstep F_583dc D_583dc. zstep F_583e0 D_583e0. zstep F_583e4 D_583e4. zstep F_583e8 D_583e8. zstep F_583ec D_583ec.
  zlbu F_583f0 D_583f0 0x105c8 C2.
  zstep F_583f4 D_583f4. zstep F_583f8 D_583f8.
  zbft F_583fc D_583fc.
  zstep F_58400 D_58400. zstep F_58404 D_58404.
  zbft F_58408 D_58408.
  zstep F_5840c D_5840c.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_58410 D_58410 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_58414 D_58414.
  stepret F_58418 D_58418 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_rz2log_2048_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x583ec : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7))
                      12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_5839c D_5839c.
  zsd F_583a0 D_583a0 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10448 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105f1 1 11) by (unfold apart in *; recell R3).
  zstep F_583a4 D_583a4. zstep F_583a8 D_583a8. zstep F_583ac D_583ac.
  zbft F_583b0 D_583b0.
  zstep F_583b4 D_583b4. zstep F_583b8 D_583b8.
  zbft F_583bc D_583bc.
  zstep F_583c0 D_583c0. zstep F_583c4 D_583c4.
  zbft F_583c8 D_583c8.
  zstep F_583cc D_583cc. zstep F_583d0 D_583d0.
  zld F_583d4 D_583d4 0x10448 C1.
  zstep F_583d8 D_583d8. zstep F_583dc D_583dc. zstep F_583e0 D_583e0. zstep F_583e4 D_583e4. zstep F_583e8 D_583e8. zstep F_583ec D_583ec.
  zlbu F_583f0 D_583f0 0x105f1 C2.
  zstep F_583f4 D_583f4. zstep F_583f8 D_583f8.
  zbft F_583fc D_583fc.
  zstep F_58400 D_58400. zstep F_58404 D_58404.
  zbft F_58408 D_58408.
  zstep F_5840c D_5840c.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_58410 D_58410 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_58414 D_58414.
  stepret F_58418 D_58418 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
