(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_5e000_5f000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_rz_rodata (M : word -> option byte) : Prop :=
  cellA M 0x10478 8 0x218a392cd3d5dbf /\ cellA M 0x105f8 1 4 /\ cellA M 0x10621 1 11.

Definition art_rz_kept (r : reg) : Prop := r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Section FPX. Context {fx : PropExec.FPState}.

#[local] Ltac post_kept := intros r Hr; unfold art_rz_kept in Hr; destruct Hr as (?&?&?&?&?); kept_solve.

Ltac zlbu F D a HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | zaddr a; exact HYP ] | step_simpl; vnorm].

Lemma art_rz2log_16 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5ee3c : word) M rom) (mkst regs' raw (Wn 8 M (sp - 8) (U raw)) rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, art_rz_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  eexists. split.
  - zstep F_5edf4 D_5edf4.
    zsd F_5edf8 D_5edf8 (sp - 8) (U raw) ltac:(rewok W).
    assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10478 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
    assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105f8 1 4) by (unfold apart in *; recell R2).
    zstep F_5edfc D_5edfc. zstep F_5ee00 D_5ee00. zstep F_5ee04 D_5ee04.
    zbft F_5ee08 D_5ee08.
    zstep F_5ee0c D_5ee0c. zstep F_5ee10 D_5ee10.
    zbft F_5ee14 D_5ee14.
    zstep F_5ee18 D_5ee18. zstep F_5ee1c D_5ee1c.
    zbft F_5ee20 D_5ee20.
    zstep F_5ee24 D_5ee24. zstep F_5ee28 D_5ee28.
    zld F_5ee2c D_5ee2c 0x10478 C1.
    zstep F_5ee30 D_5ee30. zstep F_5ee34 D_5ee34. zstep F_5ee38 D_5ee38. zstep F_5ee3c D_5ee3c. zstep F_5ee40 D_5ee40. zstep F_5ee44 D_5ee44.
    zlbu F_5ee48 D_5ee48 0x105f8 C2.
    zstep F_5ee4c D_5ee4c. zstep F_5ee50 D_5ee50.
    zbft F_5ee54 D_5ee54.
    zstep F_5ee58 D_5ee58. zstep F_5ee5c D_5ee5c.
    zbft F_5ee60 D_5ee60.
    zstep F_5ee64 D_5ee64.
    assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
    zld F_5ee68 D_5ee68 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zstep F_5ee6c D_5ee6c.
    stepret F_5ee70 D_5ee70 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]). post_kept.
Qed.
Lemma art_rz2log_2048 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5ee3c : word) M rom) (mkst regs' raw (Wn 8 M (sp - 8) (U raw)) rom)
    /\ getr regs' 10 = Z_to_bv 64 7 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, art_rz_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  eexists. split.
  - zstep F_5edf4 D_5edf4.
    zsd F_5edf8 D_5edf8 (sp - 8) (U raw) ltac:(rewok W).
    assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10478 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
    assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10621 1 11) by (unfold apart in *; recell R3).
    zstep F_5edfc D_5edfc. zstep F_5ee00 D_5ee00. zstep F_5ee04 D_5ee04.
    zbft F_5ee08 D_5ee08.
    zstep F_5ee0c D_5ee0c. zstep F_5ee10 D_5ee10.
    zbft F_5ee14 D_5ee14.
    zstep F_5ee18 D_5ee18. zstep F_5ee1c D_5ee1c.
    zbft F_5ee20 D_5ee20.
    zstep F_5ee24 D_5ee24. zstep F_5ee28 D_5ee28.
    zld F_5ee2c D_5ee2c 0x10478 C1.
    zstep F_5ee30 D_5ee30. zstep F_5ee34 D_5ee34. zstep F_5ee38 D_5ee38. zstep F_5ee3c D_5ee3c. zstep F_5ee40 D_5ee40. zstep F_5ee44 D_5ee44.
    zlbu F_5ee48 D_5ee48 0x10621 C2.
    zstep F_5ee4c D_5ee4c. zstep F_5ee50 D_5ee50.
    zbft F_5ee54 D_5ee54.
    zstep F_5ee58 D_5ee58. zstep F_5ee5c D_5ee5c.
    zbft F_5ee60 D_5ee60.
    zstep F_5ee64 D_5ee64.
    assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
    zld F_5ee68 D_5ee68 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zstep F_5ee6c D_5ee6c.
    stepret F_5ee70 D_5ee70 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]). post_kept.
Qed.

Lemma art_rz2log_16_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x5ee3c : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 0))
                      12 (Z_to_bv 64 4)) 13 (Z_to_bv 64 16)) 14 (Z_to_bv 64 16)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_5edf4 D_5edf4.
  zsd F_5edf8 D_5edf8 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10478 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105f8 1 4) by (unfold apart in *; recell R2).
  zstep F_5edfc D_5edfc. zstep F_5ee00 D_5ee00. zstep F_5ee04 D_5ee04.
  zbft F_5ee08 D_5ee08.
  zstep F_5ee0c D_5ee0c. zstep F_5ee10 D_5ee10.
  zbft F_5ee14 D_5ee14.
  zstep F_5ee18 D_5ee18. zstep F_5ee1c D_5ee1c.
  zbft F_5ee20 D_5ee20.
  zstep F_5ee24 D_5ee24. zstep F_5ee28 D_5ee28.
  zld F_5ee2c D_5ee2c 0x10478 C1.
  zstep F_5ee30 D_5ee30. zstep F_5ee34 D_5ee34. zstep F_5ee38 D_5ee38. zstep F_5ee3c D_5ee3c. zstep F_5ee40 D_5ee40. zstep F_5ee44 D_5ee44.
  zlbu F_5ee48 D_5ee48 0x105f8 C2.
  zstep F_5ee4c D_5ee4c. zstep F_5ee50 D_5ee50.
  zbft F_5ee54 D_5ee54.
  zstep F_5ee58 D_5ee58. zstep F_5ee5c D_5ee5c.
  zbft F_5ee60 D_5ee60.
  zstep F_5ee64 D_5ee64.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_5ee68 D_5ee68 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_5ee6c D_5ee6c.
  stepret F_5ee70 D_5ee70 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_rz2log_2048_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x5ee3c : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7))
                      12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_5edf4 D_5edf4.
  zsd F_5edf8 D_5edf8 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10478 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10621 1 11) by (unfold apart in *; recell R3).
  zstep F_5edfc D_5edfc. zstep F_5ee00 D_5ee00. zstep F_5ee04 D_5ee04.
  zbft F_5ee08 D_5ee08.
  zstep F_5ee0c D_5ee0c. zstep F_5ee10 D_5ee10.
  zbft F_5ee14 D_5ee14.
  zstep F_5ee18 D_5ee18. zstep F_5ee1c D_5ee1c.
  zbft F_5ee20 D_5ee20.
  zstep F_5ee24 D_5ee24. zstep F_5ee28 D_5ee28.
  zld F_5ee2c D_5ee2c 0x10478 C1.
  zstep F_5ee30 D_5ee30. zstep F_5ee34 D_5ee34. zstep F_5ee38 D_5ee38. zstep F_5ee3c D_5ee3c. zstep F_5ee40 D_5ee40. zstep F_5ee44 D_5ee44.
  zlbu F_5ee48 D_5ee48 0x10621 C2.
  zstep F_5ee4c D_5ee4c. zstep F_5ee50 D_5ee50.
  zbft F_5ee54 D_5ee54.
  zstep F_5ee58 D_5ee58. zstep F_5ee5c D_5ee5c.
  zbft F_5ee60 D_5ee60.
  zstep F_5ee64 D_5ee64.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_5ee68 D_5ee68 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_5ee6c D_5ee6c.
  stepret F_5ee70 D_5ee70 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
