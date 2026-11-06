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
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4_code_5f000_60000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_rz_rodata (M : word -> option byte) : Prop :=
  cellA M 0x10460 8 0x218a392cd3d5dbf /\ cellA M 0x105e0 1 4 /\ cellA M 0x10609 1 11.

Definition art_rz_kept (r : reg) : Prop := r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Section FPX. Context {fx : PropExec.FPState}.

#[local] Ltac post_kept := intros r Hr; unfold art_rz_kept in Hr; destruct Hr as (?&?&?&?&?); kept_solve.

Ltac zlbu F D a HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | zaddr a; exact HYP ] | step_simpl; vnorm].

Lemma art_rz2log_16 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2aff0 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5fe48 : word) M rom) (mkst regs' raw (Wn 8 M (sp - 8) (U raw)) rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, art_rz_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  eexists. split.
  - zstep F_5fdf8 D_5fdf8.
    zsd F_5fdfc D_5fdfc (sp - 8) (U raw) ltac:(rewok W).
    assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10460 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
    assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105e0 1 4) by (unfold apart in *; recell R2).
    zstep F_5fe00 D_5fe00. zstep F_5fe04 D_5fe04. zstep F_5fe08 D_5fe08.
    zbft F_5fe0c D_5fe0c.
    zstep F_5fe10 D_5fe10. zstep F_5fe14 D_5fe14.
    zbft F_5fe18 D_5fe18.
    zstep F_5fe1c D_5fe1c. zstep F_5fe20 D_5fe20.
    zbft F_5fe24 D_5fe24.
    zstep F_5fe28 D_5fe28. zstep F_5fe2c D_5fe2c.
    zld F_5fe30 D_5fe30 0x10460 C1.
    zstep F_5fe34 D_5fe34. zstep F_5fe38 D_5fe38. zstep F_5fe3c D_5fe3c. zstep F_5fe40 D_5fe40. zstep F_5fe44 D_5fe44. zstep F_5fe48 D_5fe48.
    zlbu F_5fe4c D_5fe4c 0x105e0 C2.
    zstep F_5fe50 D_5fe50. zstep F_5fe54 D_5fe54.
    zbft F_5fe58 D_5fe58.
    zstep F_5fe5c D_5fe5c. zstep F_5fe60 D_5fe60.
    zbft F_5fe64 D_5fe64.
    zstep F_5fe68 D_5fe68.
    assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
    zld F_5fe6c D_5fe6c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zstep F_5fe70 D_5fe70.
    stepret F_5fe74 D_5fe74 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]). post_kept.
Qed.
Lemma art_rz2log_2048 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2aff0 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5fe48 : word) M rom) (mkst regs' raw (Wn 8 M (sp - 8) (U raw)) rom)
    /\ getr regs' 10 = Z_to_bv 64 7 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, art_rz_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  eexists. split.
  - zstep F_5fdf8 D_5fdf8.
    zsd F_5fdfc D_5fdfc (sp - 8) (U raw) ltac:(rewok W).
    assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10460 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
    assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10609 1 11) by (unfold apart in *; recell R3).
    zstep F_5fe00 D_5fe00. zstep F_5fe04 D_5fe04. zstep F_5fe08 D_5fe08.
    zbft F_5fe0c D_5fe0c.
    zstep F_5fe10 D_5fe10. zstep F_5fe14 D_5fe14.
    zbft F_5fe18 D_5fe18.
    zstep F_5fe1c D_5fe1c. zstep F_5fe20 D_5fe20.
    zbft F_5fe24 D_5fe24.
    zstep F_5fe28 D_5fe28. zstep F_5fe2c D_5fe2c.
    zld F_5fe30 D_5fe30 0x10460 C1.
    zstep F_5fe34 D_5fe34. zstep F_5fe38 D_5fe38. zstep F_5fe3c D_5fe3c. zstep F_5fe40 D_5fe40. zstep F_5fe44 D_5fe44. zstep F_5fe48 D_5fe48.
    zlbu F_5fe4c D_5fe4c 0x10609 C2.
    zstep F_5fe50 D_5fe50. zstep F_5fe54 D_5fe54.
    zbft F_5fe58 D_5fe58.
    zstep F_5fe5c D_5fe5c. zstep F_5fe60 D_5fe60.
    zbft F_5fe64 D_5fe64.
    zstep F_5fe68 D_5fe68.
    assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
    zld F_5fe6c D_5fe6c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zstep F_5fe70 D_5fe70.
    stepret F_5fe74 D_5fe74 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]). post_kept.
Qed.

(* [comment removed for export] *)
Lemma art_rz2log_16_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2aff0 ->
  msteps ASEGS (mkst regs (0x5fe48 : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 0))
                      12 (Z_to_bv 64 4)) 13 (Z_to_bv 64 16)) 14 (Z_to_bv 64 16)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_5fdf8 D_5fdf8.
  zsd F_5fdfc D_5fdfc (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10460 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105e0 1 4) by (unfold apart in *; recell R2).
  zstep F_5fe00 D_5fe00. zstep F_5fe04 D_5fe04. zstep F_5fe08 D_5fe08.
  zbft F_5fe0c D_5fe0c.
  zstep F_5fe10 D_5fe10. zstep F_5fe14 D_5fe14.
  zbft F_5fe18 D_5fe18.
  zstep F_5fe1c D_5fe1c. zstep F_5fe20 D_5fe20.
  zbft F_5fe24 D_5fe24.
  zstep F_5fe28 D_5fe28. zstep F_5fe2c D_5fe2c.
  zld F_5fe30 D_5fe30 0x10460 C1.
  zstep F_5fe34 D_5fe34. zstep F_5fe38 D_5fe38. zstep F_5fe3c D_5fe3c. zstep F_5fe40 D_5fe40. zstep F_5fe44 D_5fe44. zstep F_5fe48 D_5fe48.
  zlbu F_5fe4c D_5fe4c 0x105e0 C2.
  zstep F_5fe50 D_5fe50. zstep F_5fe54 D_5fe54.
  zbft F_5fe58 D_5fe58.
  zstep F_5fe5c D_5fe5c. zstep F_5fe60 D_5fe60.
  zbft F_5fe64 D_5fe64.
  zstep F_5fe68 D_5fe68.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_5fe6c D_5fe6c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_5fe70 D_5fe70.
  stepret F_5fe74 D_5fe74 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_rz2log_2048_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2aff0 ->
  msteps ASEGS (mkst regs (0x5fe48 : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7))
                      12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_5fdf8 D_5fdf8.
  zsd F_5fdfc D_5fdfc (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10460 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10609 1 11) by (unfold apart in *; recell R3).
  zstep F_5fe00 D_5fe00. zstep F_5fe04 D_5fe04. zstep F_5fe08 D_5fe08.
  zbft F_5fe0c D_5fe0c.
  zstep F_5fe10 D_5fe10. zstep F_5fe14 D_5fe14.
  zbft F_5fe18 D_5fe18.
  zstep F_5fe1c D_5fe1c. zstep F_5fe20 D_5fe20.
  zbft F_5fe24 D_5fe24.
  zstep F_5fe28 D_5fe28. zstep F_5fe2c D_5fe2c.
  zld F_5fe30 D_5fe30 0x10460 C1.
  zstep F_5fe34 D_5fe34. zstep F_5fe38 D_5fe38. zstep F_5fe3c D_5fe3c. zstep F_5fe40 D_5fe40. zstep F_5fe44 D_5fe44. zstep F_5fe48 D_5fe48.
  zlbu F_5fe4c D_5fe4c 0x10609 C2.
  zstep F_5fe50 D_5fe50. zstep F_5fe54 D_5fe54.
  zbft F_5fe58 D_5fe58.
  zstep F_5fe5c D_5fe5c. zstep F_5fe60 D_5fe60.
  zbft F_5fe64 D_5fe64.
  zstep F_5fe68 D_5fe68.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_5fe6c D_5fe6c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_5fe70 D_5fe70.
  stepret F_5fe74 D_5fe74 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
