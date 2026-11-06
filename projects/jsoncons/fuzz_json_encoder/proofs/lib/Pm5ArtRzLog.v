(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5_code_60000_61000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_rz_rodata (M : word -> option byte) : Prop :=
  cellA M 0x10478 8 0x218a392cd3d5dbf /\ cellA M 0x105f8 1 4 /\ cellA M 0x10621 1 11.

Definition art_rz_kept (r : reg) : Prop := r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Section FPX. Context {fx : PropExec.FPState}.

#[local] Ltac post_kept := intros r Hr; unfold art_rz_kept in Hr; destruct Hr as (?&?&?&?&?); kept_solve.

Ltac zlbu F D a HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | zaddr a; exact HYP ] | step_simpl; vnorm].

Lemma art_rz2log_16 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2afe8 ->
  exists regs',
    msteps ASEGS (mkst regs (0x60718 : word) M rom) (mkst regs' raw (Wn 8 M (sp - 8) (U raw)) rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, art_rz_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  eexists. split.
  - zstep F_606d0 D_606d0.
    zsd F_606d4 D_606d4 (sp - 8) (U raw) ltac:(rewok W).
    assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10478 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
    assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105f8 1 4) by (unfold apart in *; recell R2).
    zstep F_606d8 D_606d8. zstep F_606dc D_606dc. zstep F_606e0 D_606e0.
    zbft F_606e4 D_606e4.
    zstep F_606e8 D_606e8. zstep F_606ec D_606ec.
    zbft F_606f0 D_606f0.
    zstep F_606f4 D_606f4. zstep F_606f8 D_606f8.
    zbft F_606fc D_606fc.
    zstep F_60700 D_60700. zstep F_60704 D_60704.
    zld F_60708 D_60708 0x10478 C1.
    zstep F_6070c D_6070c. zstep F_60710 D_60710. zstep F_60714 D_60714. zstep F_60718 D_60718. zstep F_6071c D_6071c. zstep F_60720 D_60720.
    zlbu F_60724 D_60724 0x105f8 C2.
    zstep F_60728 D_60728. zstep F_6072c D_6072c.
    zbft F_60730 D_60730.
    zstep F_60734 D_60734. zstep F_60738 D_60738.
    zbft F_6073c D_6073c.
    zstep F_60740 D_60740.
    assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
    zld F_60744 D_60744 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zstep F_60748 D_60748.
    stepret F_6074c D_6074c raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]). post_kept.
Qed.
Lemma art_rz2log_2048 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2afe8 ->
  exists regs',
    msteps ASEGS (mkst regs (0x60718 : word) M rom) (mkst regs' raw (Wn 8 M (sp - 8) (U raw)) rom)
    /\ getr regs' 10 = Z_to_bv 64 7 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, art_rz_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  eexists. split.
  - zstep F_606d0 D_606d0.
    zsd F_606d4 D_606d4 (sp - 8) (U raw) ltac:(rewok W).
    assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10478 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
    assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10621 1 11) by (unfold apart in *; recell R3).
    zstep F_606d8 D_606d8. zstep F_606dc D_606dc. zstep F_606e0 D_606e0.
    zbft F_606e4 D_606e4.
    zstep F_606e8 D_606e8. zstep F_606ec D_606ec.
    zbft F_606f0 D_606f0.
    zstep F_606f4 D_606f4. zstep F_606f8 D_606f8.
    zbft F_606fc D_606fc.
    zstep F_60700 D_60700. zstep F_60704 D_60704.
    zld F_60708 D_60708 0x10478 C1.
    zstep F_6070c D_6070c. zstep F_60710 D_60710. zstep F_60714 D_60714. zstep F_60718 D_60718. zstep F_6071c D_6071c. zstep F_60720 D_60720.
    zlbu F_60724 D_60724 0x10621 C2.
    zstep F_60728 D_60728. zstep F_6072c D_6072c.
    zbft F_60730 D_60730.
    zstep F_60734 D_60734. zstep F_60738 D_60738.
    zbft F_6073c D_6073c.
    zstep F_60740 D_60740.
    assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
    zld F_60744 D_60744 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zstep F_60748 D_60748.
    stepret F_6074c D_6074c raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]). post_kept.
Qed.

(* [comment removed for export] *)
Lemma art_rz2log_16_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2afe8 ->
  msteps ASEGS (mkst regs (0x60718 : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 0))
                      12 (Z_to_bv 64 4)) 13 (Z_to_bv 64 16)) 14 (Z_to_bv 64 16)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_606d0 D_606d0.
  zsd F_606d4 D_606d4 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10478 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x105f8 1 4) by (unfold apart in *; recell R2).
  zstep F_606d8 D_606d8. zstep F_606dc D_606dc. zstep F_606e0 D_606e0.
  zbft F_606e4 D_606e4.
  zstep F_606e8 D_606e8. zstep F_606ec D_606ec.
  zbft F_606f0 D_606f0.
  zstep F_606f4 D_606f4. zstep F_606f8 D_606f8.
  zbft F_606fc D_606fc.
  zstep F_60700 D_60700. zstep F_60704 D_60704.
  zld F_60708 D_60708 0x10478 C1.
  zstep F_6070c D_6070c. zstep F_60710 D_60710. zstep F_60714 D_60714. zstep F_60718 D_60718. zstep F_6071c D_6071c. zstep F_60720 D_60720.
  zlbu F_60724 D_60724 0x105f8 C2.
  zstep F_60728 D_60728. zstep F_6072c D_6072c.
  zbft F_60730 D_60730.
  zstep F_60734 D_60734. zstep F_60738 D_60738.
  zbft F_6073c D_6073c.
  zstep F_60740 D_60740.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_60744 D_60744 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_60748 D_60748.
  stepret F_6074c D_6074c raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_rz2log_2048_fn : forall regs (M rom : word -> option byte) (sp : Z) (raw : word),
  getr regs 10 = Z_to_bv 64 2048 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = raw -> ret_ok raw ->
  16 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 16) 16 -> art_rz_rodata M -> apart (sp - 16) 16 0x10000 0x2afe8 ->
  msteps ASEGS (mkst regs (0x60718 : word) M rom)
             (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7))
                      12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom sp raw H10 H2 H1 Hret Hsp Hsp' W (R1 & R2 & R3) Ap.
  zstep F_606d0 D_606d0.
  zsd F_606d4 D_606d4 (sp - 8) (U raw) ltac:(rewok W).
  assert (C1 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10478 8 0x218a392cd3d5dbf) by (unfold apart in *; recell R1).
  assert (C2 : cellA (Wn 8 M (sp - 8) (U raw)) 0x10621 1 11) by (unfold apart in *; recell R3).
  zstep F_606d8 D_606d8. zstep F_606dc D_606dc. zstep F_606e0 D_606e0.
  zbft F_606e4 D_606e4.
  zstep F_606e8 D_606e8. zstep F_606ec D_606ec.
  zbft F_606f0 D_606f0.
  zstep F_606f4 D_606f4. zstep F_606f8 D_606f8.
  zbft F_606fc D_606fc.
  zstep F_60700 D_60700. zstep F_60704 D_60704.
  zld F_60708 D_60708 0x10478 C1.
  zstep F_6070c D_6070c. zstep F_60710 D_60710. zstep F_60714 D_60714. zstep F_60718 D_60718. zstep F_6071c D_6071c. zstep F_60720 D_60720.
  zlbu F_60724 D_60724 0x10621 C2.
  zstep F_60728 D_60728. zstep F_6072c D_6072c.
  zbft F_60730 D_60730.
  zstep F_60734 D_60734. zstep F_60738 D_60738.
  zbft F_6073c D_6073c.
  zstep F_60740 D_60740.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_60744 D_60744 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_60748 D_60748.
  stepret F_6074c D_6074c raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
