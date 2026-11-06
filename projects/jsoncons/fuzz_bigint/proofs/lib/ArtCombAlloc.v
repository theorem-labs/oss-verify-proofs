(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_415bc_42aa8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).

(* [comment removed for export] *)
Definition art_ca_frame (M : word -> option byte) (sp ra s0 s1 s2 s3 s4 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) ra) (sp - 16) s0) (sp - 24) s1) (sp - 32) s2) (sp - 40) s3) (sp - 48) s4.

Section FPX. Context {fx : PropExec.FPState}.

#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_ca_entry_kept (r : reg) : Prop := r <> 2%bv /\ r <> 12%bv /\ r <> 14%bv /\ r <> 15%bv.

Lemma art_ca_entry8 : forall regs (M rom : word -> option byte) (sp s : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 12 = Z_to_bv 64 s -> getr regs 13 = Z_to_bv 64 8 ->
  48 <= sp -> sp < 2 ^ 64 -> 1 <= s <= 65536 ->
  wrA M (sp - 48) 48 ->
  exists regs',
    msteps ASEGS (mkst regs (0x41ac8 : word) M rom)
                 (mkst regs' (0x41b4c : word)
                       (art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 14 = Z_to_bv 64 s /\ getr regs' 12 = Z_to_bv 64 512 /\ getr regs' 15 = Z_to_bv 64 65536
    /\ (forall r : reg, art_ca_entry_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp s H2 H12 H13 Hsp Hsp' Hs W.
  eexists. split.
  - zstep F_41ac8 D_41ac8.
    zsd F_41acc D_41acc (sp - 8) (U (getr regs 1)) ltac:(rewok W).
    zsd F_41ad0 D_41ad0 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_41ad4 D_41ad4 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
    zsd F_41ad8 D_41ad8 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_41adc D_41adc (sp - 40) (U (getr regs 19)) ltac:(rewok W).
    zsd F_41ae0 D_41ae0 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zstep F_41ae4 D_41ae4.
    zstep F_41ae8 D_41ae8.
    zstep F_41aec D_41aec.
    zbtk F_41af0 D_41af0.
    zstep F_41b14 D_41b14.
    zstep F_41b18 D_41b18.
    zbtk F_41b1c D_41b1c.
    zstep F_41b3c D_41b3c.
    zbft F_41b40 D_41b40.
    zbft F_41b44 D_41b44.
    zstep F_41b48 D_41b48.
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]).
    intros r Hr; unfold art_ca_entry_kept in Hr; destruct Hr as (?&?&?&?); gres; try reflexivity;
    repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.

Lemma art_ca_small : forall regs (M rom : word -> option byte) (s : Z),
  getr regs 14 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 512 -> 1 <= s <= 512 ->
  exists regs',
    msteps ASEGS (mkst regs (0x41b4c : word) M rom) (mkst regs' (0x41c5c : word) M rom)
    /\ getr regs' 8 = Z_to_bv 64 ((s + 31) / 32) /\ getr regs' 14 = Z_to_bv 64 (s + 31)
    /\ (forall r : reg, r <> 8%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom s H14 H12 Hs.
  eexists. split.
  - zbft F_41b4c D_41b4c.
    zstep F_41b50 D_41b50.
    stepn F_41b54 D_41b54. rwH. rewrite art_zb_srli by lia. change (2 ^ 5) with 32.
    stepn F_41b58 D_41b58.
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]).
    intros r H1 H2; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.

Lemma art_ca_big : forall regs (M rom : word -> option byte) (s : Z),
  getr regs 14 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 512 -> 513 <= s <= 65536 ->
  msteps ASEGS (mkst regs (0x41b4c : word) M rom) (mkst regs (0x41b80 : word) M rom).
Proof.
  intros regs M rom s H14 H12 Hs.
  zbtk F_41b4c D_41b4c.
  apply mst_refl.
Qed.
End FPX.
