(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_rz_rodata (M : word -> option byte) : Prop :=
  cellA M 0x10450 8 0x218a392cd3d5dbf /\ cellA M 0x105d0 1 4 /\ cellA M 0x105f9 1 11.

Definition art_rz_kept (r : reg) : Prop := r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Section FPX. Context {fx : PropExec.FPState}.

#[local] Ltac post_kept := intros r Hr; unfold art_rz_kept in Hr; destruct Hr as (?&?&?&?&?); kept_solve.

Ltac zlbu F D a HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | zaddr a; exact HYP ] | step_simpl; vnorm].

#[using="Type"] Lemma art_rz2log_16_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x58c14 : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 0))
                      12 (Z_to_bv 64 4)) 13 (Z_to_bv 64 16)) 14 (Z_to_bv 64 16)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_58bc4 D_58bc4.
  zsd F_58bc8 D_58bc8 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10450 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105d0 1 4) by (unfold apart in *; recell R2).
  zstep F_58bcc D_58bcc. zstep F_58bd0 D_58bd0. zstep F_58bd4 D_58bd4.
  zbft F_58bd8 D_58bd8.
  zstep F_58bdc D_58bdc. zstep F_58be0 D_58be0.
  zbft F_58be4 D_58be4.
  zstep F_58be8 D_58be8. zstep F_58bec D_58bec.
  zbft F_58bf0 D_58bf0.
  zstep F_58bf4 D_58bf4. zstep F_58bf8 D_58bf8.
  zld F_58bfc D_58bfc 0x10450 C1.
  zstep F_58c00 D_58c00. zstep F_58c04 D_58c04. zstep F_58c08 D_58c08. zstep F_58c0c D_58c0c. zstep F_58c10 D_58c10. zstep F_58c14 D_58c14.
  zlbu F_58c18 D_58c18 0x105d0 C2.
  zstep F_58c1c D_58c1c. zstep F_58c20 D_58c20.
  zbft F_58c24 D_58c24.
  zstep F_58c28 D_58c28. zstep F_58c2c D_58c2c.
  zbft F_58c30 D_58c30.
  zstep F_58c34 D_58c34.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_58c38 D_58c38 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_58c3c D_58c3c.
  stepret F_58c40 D_58c40 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_rz2log_2048_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x58c14 : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7))
                      12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_58bc4 D_58bc4.
  zsd F_58bc8 D_58bc8 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10450 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105f9 1 11) by (unfold apart in *; recell R3).
  zstep F_58bcc D_58bcc. zstep F_58bd0 D_58bd0. zstep F_58bd4 D_58bd4.
  zbft F_58bd8 D_58bd8.
  zstep F_58bdc D_58bdc. zstep F_58be0 D_58be0.
  zbft F_58be4 D_58be4.
  zstep F_58be8 D_58be8. zstep F_58bec D_58bec.
  zbft F_58bf0 D_58bf0.
  zstep F_58bf4 D_58bf4. zstep F_58bf8 D_58bf8.
  zld F_58bfc D_58bfc 0x10450 C1.
  zstep F_58c00 D_58c00. zstep F_58c04 D_58c04. zstep F_58c08 D_58c08. zstep F_58c0c D_58c0c. zstep F_58c10 D_58c10. zstep F_58c14 D_58c14.
  zlbu F_58c18 D_58c18 0x105f9 C2.
  zstep F_58c1c D_58c1c. zstep F_58c20 D_58c20.
  zbft F_58c24 D_58c24.
  zstep F_58c28 D_58c28. zstep F_58c2c D_58c2c.
  zbft F_58c30 D_58c30.
  zstep F_58c34 D_58c34.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_58c38 D_58c38 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_58c3c D_58c3c.
  stepret F_58c40 D_58c40 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
