(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).

Definition art_ca_frame (M : word -> option byte) (sp ra s0 s1 s2 s3 s4 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) ra) (sp - 16) s0) (sp - 24) s1) (sp - 32) s2) (sp - 40) s3) (sp - 48) s4.

Section FPX. Context {fx : PropExec.FPState}.

#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_ca_entry_kept (r : reg) : Prop := r <> 2%bv /\ r <> 12%bv /\ r <> 14%bv /\ r <> 15%bv.

#[using="Type"] Lemma art_ca_entry8 : forall regs (M rom : word -> option byte) (sp s : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 12 = Z_to_bv 64 s -> getr regs 13 = Z_to_bv 64 8 ->
  48 <= sp -> sp < 2 ^ 64 -> 1 <= s <= 65536 ->
  wrA M (sp - 48) 48 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57524 : word) M rom)
                 (mkst regs' (0x575a8 : word)
                       (art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 14 = Z_to_bv 64 s /\ getr regs' 12 = Z_to_bv 64 512 /\ getr regs' 15 = Z_to_bv 64 65536
    /\ (forall r : reg, art_ca_entry_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp s H2 H12 H13 Hsp Hsp' Hs W.
  eexists. split.
  - zstep F_574d4 D_574d4.
    zsd F_574d8 D_574d8 (sp - 8) (U (getr regs 1)) ltac:(rewok W).
    zsd F_574dc D_574dc (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_574e0 D_574e0 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
    zsd F_574e4 D_574e4 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_574e8 D_574e8 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
    zsd F_574ec D_574ec (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zstep F_574f0 D_574f0.
    zstep F_574f4 D_574f4.
    zstep F_574f8 D_574f8.
    zbtk F_574fc D_574fc.
    zstep F_57520 D_57520.
    zstep F_57524 D_57524.
    zbtk F_57528 D_57528.
    zstep F_57548 D_57548.
    zbft F_5754c D_5754c.
    zbft F_57550 D_57550.
    zstep F_57554 D_57554.
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]).
    intros r Hr; unfold art_ca_entry_kept in Hr; destruct Hr as (?&?&?&?); gres; try reflexivity;
    repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.

#[using="Type"] Lemma art_ca_small : forall regs (M rom : word -> option byte) (s : Z),
  getr regs 14 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 512 -> 1 <= s <= 512 ->
  exists regs',
    msteps ASEGS (mkst regs (0x575a8 : word) M rom) (mkst regs' (0x576b8 : word) M rom)
    /\ getr regs' 8 = Z_to_bv 64 ((s + 31) / 32) /\ getr regs' 14 = Z_to_bv 64 (s + 31)
    /\ (forall r : reg, r <> 8%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom s H14 H12 Hs.
  eexists. split.
  - zbft F_57558 D_57558.
    zstep F_5755c D_5755c.
    stepn F_57560 D_57560. rwH. rewrite art_zb_srli by lia. change (2 ^ 5) with 32.
    stepn F_57564 D_57564.
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]).
    intros r H1 H2; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.

#[using="Type"] Lemma art_ca_big : forall regs (M rom : word -> option byte) (s : Z),
  getr regs 14 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 512 -> 513 <= s <= 65536 ->
  msteps ASEGS (mkst regs (0x575a8 : word) M rom) (mkst regs (0x575dc : word) M rom).
Proof.
  intros regs M rom s H14 H12 Hs.
  zbtk F_57558 D_57558.
  apply mst_refl.
Qed.
End FPX.
