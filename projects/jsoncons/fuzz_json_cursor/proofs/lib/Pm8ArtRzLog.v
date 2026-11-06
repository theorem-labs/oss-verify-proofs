(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_5e000_5f000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_rz_rodata (M : word -> option byte) : Prop :=
  cellA M 0x10460 8 0x218a392cd3d5dbf /\ cellA M 0x105e0 1 4 /\ cellA M 0x10609 1 11.

Definition art_rz_kept (r : reg) : Prop := r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Section FPX. Context {fx : PropExec.FPState}.

#[local] Ltac post_kept := intros r Hr; unfold art_rz_kept in Hr; destruct Hr as (?&?&?&?&?); kept_solve.

Ltac zlbu F D a HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | zaddr a; exact HYP ] | step_simpl; vnorm].

Lemma art_rz2log_16 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5ea7c : word) M rom) (mkst regs' raw (Wn 8 M (sp - 8) (U raw)) rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, art_rz_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  eexists. split.
  - zstep F_5ea2c D_5ea2c.
    zsd F_5ea30 D_5ea30 (sp - 8) (U raw) ltac:(rewok W).
    assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10460 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
    assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105e0 1 4) by (unfold apart in *; recell R2).
    zstep F_5ea34 D_5ea34. zstep F_5ea38 D_5ea38. zstep F_5ea3c D_5ea3c.
    zbft F_5ea40 D_5ea40.
    zstep F_5ea44 D_5ea44. zstep F_5ea48 D_5ea48.
    zbft F_5ea4c D_5ea4c.
    zstep F_5ea50 D_5ea50. zstep F_5ea54 D_5ea54.
    zbft F_5ea58 D_5ea58.
    zstep F_5ea5c D_5ea5c. zstep F_5ea60 D_5ea60.
    zld F_5ea64 D_5ea64 0x10460 C1.
    zstep F_5ea68 D_5ea68. zstep F_5ea6c D_5ea6c. zstep F_5ea70 D_5ea70. zstep F_5ea74 D_5ea74. zstep F_5ea78 D_5ea78. zstep F_5ea7c D_5ea7c.
    zlbu F_5ea80 D_5ea80 0x105e0 C2.
    zstep F_5ea84 D_5ea84. zstep F_5ea88 D_5ea88.
    zbft F_5ea8c D_5ea8c.
    zstep F_5ea90 D_5ea90. zstep F_5ea94 D_5ea94.
    zbft F_5ea98 D_5ea98.
    zstep F_5ea9c D_5ea9c.
    assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
    zld F_5eaa0 D_5eaa0 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zstep F_5eaa4 D_5eaa4.
    stepret F_5eaa8 D_5eaa8 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]). post_kept.
Qed.
Lemma art_rz2log_2048 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5ea7c : word) M rom) (mkst regs' raw (Wn 8 M (sp - 8) (U raw)) rom)
    /\ getr regs' 10 = Z_to_bv 64 7 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, art_rz_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  eexists. split.
  - zstep F_5ea2c D_5ea2c.
    zsd F_5ea30 D_5ea30 (sp - 8) (U raw) ltac:(rewok W).
    assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10460 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
    assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10609 1 11) by (unfold apart in *; recell R3).
    zstep F_5ea34 D_5ea34. zstep F_5ea38 D_5ea38. zstep F_5ea3c D_5ea3c.
    zbft F_5ea40 D_5ea40.
    zstep F_5ea44 D_5ea44. zstep F_5ea48 D_5ea48.
    zbft F_5ea4c D_5ea4c.
    zstep F_5ea50 D_5ea50. zstep F_5ea54 D_5ea54.
    zbft F_5ea58 D_5ea58.
    zstep F_5ea5c D_5ea5c. zstep F_5ea60 D_5ea60.
    zld F_5ea64 D_5ea64 0x10460 C1.
    zstep F_5ea68 D_5ea68. zstep F_5ea6c D_5ea6c. zstep F_5ea70 D_5ea70. zstep F_5ea74 D_5ea74. zstep F_5ea78 D_5ea78. zstep F_5ea7c D_5ea7c.
    zlbu F_5ea80 D_5ea80 0x10609 C2.
    zstep F_5ea84 D_5ea84. zstep F_5ea88 D_5ea88.
    zbft F_5ea8c D_5ea8c.
    zstep F_5ea90 D_5ea90. zstep F_5ea94 D_5ea94.
    zbft F_5ea98 D_5ea98.
    zstep F_5ea9c D_5ea9c.
    assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
    zld F_5eaa0 D_5eaa0 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zstep F_5eaa4 D_5eaa4.
    stepret F_5eaa8 D_5eaa8 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]). post_kept.
Qed.

Lemma art_rz2log_16_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x5ea7c : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 0))
                      12 (Z_to_bv 64 4)) 13 (Z_to_bv 64 16)) 14 (Z_to_bv 64 16)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_5ea2c D_5ea2c.
  zsd F_5ea30 D_5ea30 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10460 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105e0 1 4) by (unfold apart in *; recell R2).
  zstep F_5ea34 D_5ea34. zstep F_5ea38 D_5ea38. zstep F_5ea3c D_5ea3c.
  zbft F_5ea40 D_5ea40.
  zstep F_5ea44 D_5ea44. zstep F_5ea48 D_5ea48.
  zbft F_5ea4c D_5ea4c.
  zstep F_5ea50 D_5ea50. zstep F_5ea54 D_5ea54.
  zbft F_5ea58 D_5ea58.
  zstep F_5ea5c D_5ea5c. zstep F_5ea60 D_5ea60.
  zld F_5ea64 D_5ea64 0x10460 C1.
  zstep F_5ea68 D_5ea68. zstep F_5ea6c D_5ea6c. zstep F_5ea70 D_5ea70. zstep F_5ea74 D_5ea74. zstep F_5ea78 D_5ea78. zstep F_5ea7c D_5ea7c.
  zlbu F_5ea80 D_5ea80 0x105e0 C2.
  zstep F_5ea84 D_5ea84. zstep F_5ea88 D_5ea88.
  zbft F_5ea8c D_5ea8c.
  zstep F_5ea90 D_5ea90. zstep F_5ea94 D_5ea94.
  zbft F_5ea98 D_5ea98.
  zstep F_5ea9c D_5ea9c.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_5eaa0 D_5eaa0 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_5eaa4 D_5eaa4.
  stepret F_5eaa8 D_5eaa8 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_rz2log_2048_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x5ea7c : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7))
                      12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_5ea2c D_5ea2c.
  zsd F_5ea30 D_5ea30 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10460 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10609 1 11) by (unfold apart in *; recell R3).
  zstep F_5ea34 D_5ea34. zstep F_5ea38 D_5ea38. zstep F_5ea3c D_5ea3c.
  zbft F_5ea40 D_5ea40.
  zstep F_5ea44 D_5ea44. zstep F_5ea48 D_5ea48.
  zbft F_5ea4c D_5ea4c.
  zstep F_5ea50 D_5ea50. zstep F_5ea54 D_5ea54.
  zbft F_5ea58 D_5ea58.
  zstep F_5ea5c D_5ea5c. zstep F_5ea60 D_5ea60.
  zld F_5ea64 D_5ea64 0x10460 C1.
  zstep F_5ea68 D_5ea68. zstep F_5ea6c D_5ea6c. zstep F_5ea70 D_5ea70. zstep F_5ea74 D_5ea74. zstep F_5ea78 D_5ea78. zstep F_5ea7c D_5ea7c.
  zlbu F_5ea80 D_5ea80 0x10609 C2.
  zstep F_5ea84 D_5ea84. zstep F_5ea88 D_5ea88.
  zbft F_5ea8c D_5ea8c.
  zstep F_5ea90 D_5ea90. zstep F_5ea94 D_5ea94.
  zbft F_5ea98 D_5ea98.
  zstep F_5ea9c D_5ea9c.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_5eaa0 D_5eaa0 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_5eaa4 D_5eaa4.
  stepret F_5eaa8 D_5eaa8 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
