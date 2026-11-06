(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_415bc_42aa8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_rz_rodata (M : word -> option byte) : Prop :=
  cellA M 0x103e8 8 0x218a392cd3d5dbf /\ cellA M 0x10560 1 4 /\ cellA M 0x10589 1 11.

Definition art_rz_kept (r : reg) : Prop := r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Section FPX. Context {fx : PropExec.FPState}.

#[local] Ltac post_kept := intros r Hr; unfold art_rz_kept in Hr; destruct Hr as (?&?&?&?&?); kept_solve.

Ltac zlbu F D a HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | zaddr a; exact HYP ] | step_simpl; vnorm].

Lemma art_rz2log_16 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  exists regs',
    msteps ASEGS (mkst regs (0x42990 : word) M rom) (mkst regs' raw (Wn 8 M (sp - 8) (U raw)) rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, art_rz_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  eexists. split.
  - zstep F_42990 D_42990.
    zsd F_42994 D_42994 (sp - 8) (U raw) ltac:(rewok W).
    assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x103e8 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
    assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10560 1 4) by (unfold apart in *; recell R2).
    zstep F_42998 D_42998. zstep F_4299c D_4299c. zstep F_429a0 D_429a0.
    zbft F_429a4 D_429a4.
    zstep F_429a8 D_429a8. zstep F_429ac D_429ac.
    zbft F_429b0 D_429b0.
    zstep F_429b4 D_429b4. zstep F_429b8 D_429b8.
    zbft F_429bc D_429bc.
    zstep F_429c0 D_429c0. zstep F_429c4 D_429c4.
    zld F_429c8 D_429c8 0x103e8 C1.
    zstep F_429cc D_429cc. zstep F_429d0 D_429d0. zstep F_429d4 D_429d4. zstep F_429d8 D_429d8. zstep F_429dc D_429dc. zstep F_429e0 D_429e0.
    zlbu F_429e4 D_429e4 0x10560 C2.
    zstep F_429e8 D_429e8. zstep F_429ec D_429ec.
    zbft F_429f0 D_429f0.
    zstep F_429f4 D_429f4. zstep F_429f8 D_429f8.
    zbft F_429fc D_429fc.
    zstep F_42a00 D_42a00.
    assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
    zld F_42a04 D_42a04 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zstep F_42a08 D_42a08.
    stepret F_42a0c D_42a0c raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]). post_kept.
Qed.
Lemma art_rz2log_2048 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  exists regs',
    msteps ASEGS (mkst regs (0x42990 : word) M rom) (mkst regs' raw (Wn 8 M (sp - 8) (U raw)) rom)
    /\ getr regs' 10 = Z_to_bv 64 7 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, art_rz_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  eexists. split.
  - zstep F_42990 D_42990.
    zsd F_42994 D_42994 (sp - 8) (U raw) ltac:(rewok W).
    assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x103e8 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
    assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10589 1 11) by (unfold apart in *; recell R3).
    zstep F_42998 D_42998. zstep F_4299c D_4299c. zstep F_429a0 D_429a0.
    zbft F_429a4 D_429a4.
    zstep F_429a8 D_429a8. zstep F_429ac D_429ac.
    zbft F_429b0 D_429b0.
    zstep F_429b4 D_429b4. zstep F_429b8 D_429b8.
    zbft F_429bc D_429bc.
    zstep F_429c0 D_429c0. zstep F_429c4 D_429c4.
    zld F_429c8 D_429c8 0x103e8 C1.
    zstep F_429cc D_429cc. zstep F_429d0 D_429d0. zstep F_429d4 D_429d4. zstep F_429d8 D_429d8. zstep F_429dc D_429dc. zstep F_429e0 D_429e0.
    zlbu F_429e4 D_429e4 0x10589 C2.
    zstep F_429e8 D_429e8. zstep F_429ec D_429ec.
    zbft F_429f0 D_429f0.
    zstep F_429f4 D_429f4. zstep F_429f8 D_429f8.
    zbft F_429fc D_429fc.
    zstep F_42a00 D_42a00.
    assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
    zld F_42a04 D_42a04 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zstep F_42a08 D_42a08.
    stepret F_42a0c D_42a0c raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]). post_kept.
Qed.

(* [comment removed for export] *)
Lemma art_rz2log_16_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x42990 : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 0))
                      12 (Z_to_bv 64 4)) 13 (Z_to_bv 64 16)) 14 (Z_to_bv 64 16)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_42990 D_42990.
  zsd F_42994 D_42994 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x103e8 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10560 1 4) by (unfold apart in *; recell R2).
  zstep F_42998 D_42998. zstep F_4299c D_4299c. zstep F_429a0 D_429a0.
  zbft F_429a4 D_429a4.
  zstep F_429a8 D_429a8. zstep F_429ac D_429ac.
  zbft F_429b0 D_429b0.
  zstep F_429b4 D_429b4. zstep F_429b8 D_429b8.
  zbft F_429bc D_429bc.
  zstep F_429c0 D_429c0. zstep F_429c4 D_429c4.
  zld F_429c8 D_429c8 0x103e8 C1.
  zstep F_429cc D_429cc. zstep F_429d0 D_429d0. zstep F_429d4 D_429d4. zstep F_429d8 D_429d8. zstep F_429dc D_429dc. zstep F_429e0 D_429e0.
  zlbu F_429e4 D_429e4 0x10560 C2.
  zstep F_429e8 D_429e8. zstep F_429ec D_429ec.
  zbft F_429f0 D_429f0.
  zstep F_429f4 D_429f4. zstep F_429f8 D_429f8.
  zbft F_429fc D_429fc.
  zstep F_42a00 D_42a00.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_42a04 D_42a04 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_42a08 D_42a08.
  stepret F_42a0c D_42a0c raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_rz2log_2048_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x42990 : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7))
                      12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_42990 D_42990.
  zsd F_42994 D_42994 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x103e8 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10589 1 11) by (unfold apart in *; recell R3).
  zstep F_42998 D_42998. zstep F_4299c D_4299c. zstep F_429a0 D_429a0.
  zbft F_429a4 D_429a4.
  zstep F_429a8 D_429a8. zstep F_429ac D_429ac.
  zbft F_429b0 D_429b0.
  zstep F_429b4 D_429b4. zstep F_429b8 D_429b8.
  zbft F_429bc D_429bc.
  zstep F_429c0 D_429c0. zstep F_429c4 D_429c4.
  zld F_429c8 D_429c8 0x103e8 C1.
  zstep F_429cc D_429cc. zstep F_429d0 D_429d0. zstep F_429d4 D_429d4. zstep F_429d8 D_429d8. zstep F_429dc D_429dc. zstep F_429e0 D_429e0.
  zlbu F_429e4 D_429e4 0x10589 C2.
  zstep F_429e8 D_429e8. zstep F_429ec D_429ec.
  zbft F_429f0 D_429f0.
  zstep F_429f4 D_429f4. zstep F_429f8 D_429f8.
  zbft F_429fc D_429fc.
  zstep F_42a00 D_42a00.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_42a04 D_42a04 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_42a08 D_42a08.
  stepret F_42a0c D_42a0c raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
