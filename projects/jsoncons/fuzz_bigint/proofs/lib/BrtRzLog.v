(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_4183c_42d28.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
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
    msteps ASEGS (mkst regs (0x42c10 : word) M rom) (mkst regs' raw (Wn 8 M (sp - 8) (U raw)) rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, art_rz_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  eexists. split.
  - zstep F_42c10 D_42c10.
    zsd F_42c14 D_42c14 (sp - 8) (U raw) ltac:(rewok W).
    assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x103e8 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
    assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10560 1 4) by (unfold apart in *; recell R2).
    zstep F_42c18 D_42c18. zstep F_42c1c D_42c1c. zstep F_42c20 D_42c20.
    zbft F_42c24 D_42c24.
    zstep F_42c28 D_42c28. zstep F_42c2c D_42c2c.
    zbft F_42c30 D_42c30.
    zstep F_42c34 D_42c34. zstep F_42c38 D_42c38.
    zbft F_42c3c D_42c3c.
    zstep F_42c40 D_42c40. zstep F_42c44 D_42c44.
    zld F_42c48 D_42c48 0x103e8 C1.
    zstep F_42c4c D_42c4c. zstep F_42c50 D_42c50. zstep F_42c54 D_42c54. zstep F_42c58 D_42c58. zstep F_42c5c D_42c5c. zstep F_42c60 D_42c60.
    zlbu F_42c64 D_42c64 0x10560 C2.
    zstep F_42c68 D_42c68. zstep F_42c6c D_42c6c.
    zbft F_42c70 D_42c70.
    zstep F_42c74 D_42c74. zstep F_42c78 D_42c78.
    zbft F_42c7c D_42c7c.
    zstep F_42c80 D_42c80.
    assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
    zld F_42c84 D_42c84 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zstep F_42c88 D_42c88.
    stepret F_42c8c D_42c8c raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]). post_kept.
Qed.
Lemma art_rz2log_2048 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  exists regs',
    msteps ASEGS (mkst regs (0x42c10 : word) M rom) (mkst regs' raw (Wn 8 M (sp - 8) (U raw)) rom)
    /\ getr regs' 10 = Z_to_bv 64 7 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, art_rz_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  eexists. split.
  - zstep F_42c10 D_42c10.
    zsd F_42c14 D_42c14 (sp - 8) (U raw) ltac:(rewok W).
    assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x103e8 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
    assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10589 1 11) by (unfold apart in *; recell R3).
    zstep F_42c18 D_42c18. zstep F_42c1c D_42c1c. zstep F_42c20 D_42c20.
    zbft F_42c24 D_42c24.
    zstep F_42c28 D_42c28. zstep F_42c2c D_42c2c.
    zbft F_42c30 D_42c30.
    zstep F_42c34 D_42c34. zstep F_42c38 D_42c38.
    zbft F_42c3c D_42c3c.
    zstep F_42c40 D_42c40. zstep F_42c44 D_42c44.
    zld F_42c48 D_42c48 0x103e8 C1.
    zstep F_42c4c D_42c4c. zstep F_42c50 D_42c50. zstep F_42c54 D_42c54. zstep F_42c58 D_42c58. zstep F_42c5c D_42c5c. zstep F_42c60 D_42c60.
    zlbu F_42c64 D_42c64 0x10589 C2.
    zstep F_42c68 D_42c68. zstep F_42c6c D_42c6c.
    zbft F_42c70 D_42c70.
    zstep F_42c74 D_42c74. zstep F_42c78 D_42c78.
    zbft F_42c7c D_42c7c.
    zstep F_42c80 D_42c80.
    assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
    zld F_42c84 D_42c84 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zstep F_42c88 D_42c88.
    stepret F_42c8c D_42c8c raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]). post_kept.
Qed.

(* [comment removed for export] *)
Lemma art_rz2log_16_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x42c10 : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 0))
                      12 (Z_to_bv 64 4)) 13 (Z_to_bv 64 16)) 14 (Z_to_bv 64 16)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_42c10 D_42c10.
  zsd F_42c14 D_42c14 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x103e8 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10560 1 4) by (unfold apart in *; recell R2).
  zstep F_42c18 D_42c18. zstep F_42c1c D_42c1c. zstep F_42c20 D_42c20.
  zbft F_42c24 D_42c24.
  zstep F_42c28 D_42c28. zstep F_42c2c D_42c2c.
  zbft F_42c30 D_42c30.
  zstep F_42c34 D_42c34. zstep F_42c38 D_42c38.
  zbft F_42c3c D_42c3c.
  zstep F_42c40 D_42c40. zstep F_42c44 D_42c44.
  zld F_42c48 D_42c48 0x103e8 C1.
  zstep F_42c4c D_42c4c. zstep F_42c50 D_42c50. zstep F_42c54 D_42c54. zstep F_42c58 D_42c58. zstep F_42c5c D_42c5c. zstep F_42c60 D_42c60.
  zlbu F_42c64 D_42c64 0x10560 C2.
  zstep F_42c68 D_42c68. zstep F_42c6c D_42c6c.
  zbft F_42c70 D_42c70.
  zstep F_42c74 D_42c74. zstep F_42c78 D_42c78.
  zbft F_42c7c D_42c7c.
  zstep F_42c80 D_42c80.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_42c84 D_42c84 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_42c88 D_42c88.
  stepret F_42c8c D_42c8c raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_rz2log_2048_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2b000 ->
  msteps ASEGS (mkst regs (0x42c10 : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7))
                      12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_42c10 D_42c10.
  zsd F_42c14 D_42c14 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x103e8 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10589 1 11) by (unfold apart in *; recell R3).
  zstep F_42c18 D_42c18. zstep F_42c1c D_42c1c. zstep F_42c20 D_42c20.
  zbft F_42c24 D_42c24.
  zstep F_42c28 D_42c28. zstep F_42c2c D_42c2c.
  zbft F_42c30 D_42c30.
  zstep F_42c34 D_42c34. zstep F_42c38 D_42c38.
  zbft F_42c3c D_42c3c.
  zstep F_42c40 D_42c40. zstep F_42c44 D_42c44.
  zld F_42c48 D_42c48 0x103e8 C1.
  zstep F_42c4c D_42c4c. zstep F_42c50 D_42c50. zstep F_42c54 D_42c54. zstep F_42c58 D_42c58. zstep F_42c5c D_42c5c. zstep F_42c60 D_42c60.
  zlbu F_42c64 D_42c64 0x10589 C2.
  zstep F_42c68 D_42c68. zstep F_42c6c D_42c6c.
  zbft F_42c70 D_42c70.
  zstep F_42c74 D_42c74. zstep F_42c78 D_42c78.
  zbft F_42c7c D_42c7c.
  zstep F_42c80 D_42c80.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_42c84 D_42c84 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_42c88 D_42c88.
  stepret F_42c8c D_42c8c raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
