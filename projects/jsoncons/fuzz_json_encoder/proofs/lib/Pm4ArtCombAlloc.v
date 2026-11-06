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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4_code_5e000_5f000.
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
    msteps ASEGS (mkst regs (0x5ef80 : word) M rom)
                 (mkst regs' (0x5f004 : word)
                       (art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 14 = Z_to_bv 64 s /\ getr regs' 12 = Z_to_bv 64 512 /\ getr regs' 15 = Z_to_bv 64 65536
    /\ (forall r : reg, art_ca_entry_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp s H2 H12 H13 Hsp Hsp' Hs W.
  eexists. split.
  - zstep F_5ef30 D_5ef30.
    zsd F_5ef34 D_5ef34 (sp - 8) (U (getr regs 1)) ltac:(rewok W).
    zsd F_5ef38 D_5ef38 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_5ef3c D_5ef3c (sp - 24) (U (getr regs 9)) ltac:(rewok W).
    zsd F_5ef40 D_5ef40 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_5ef44 D_5ef44 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
    zsd F_5ef48 D_5ef48 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zstep F_5ef4c D_5ef4c.
    zstep F_5ef50 D_5ef50.
    zstep F_5ef54 D_5ef54.
    zbtk F_5ef58 D_5ef58.
    zstep F_5ef7c D_5ef7c.
    zstep F_5ef80 D_5ef80.
    zbtk F_5ef84 D_5ef84.
    zstep F_5efa4 D_5efa4.
    zbft F_5efa8 D_5efa8.
    zbft F_5efac D_5efac.
    zstep F_5efb0 D_5efb0.
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]).
    intros r Hr; unfold art_ca_entry_kept in Hr; destruct Hr as (?&?&?&?); gres; try reflexivity;
    repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.

Lemma art_ca_small : forall regs (M rom : word -> option byte) (s : Z),
  getr regs 14 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 512 -> 1 <= s <= 512 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5f004 : word) M rom) (mkst regs' (0x5f114 : word) M rom)
    /\ getr regs' 8 = Z_to_bv 64 ((s + 31) / 32) /\ getr regs' 14 = Z_to_bv 64 (s + 31)
    /\ (forall r : reg, r <> 8%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom s H14 H12 Hs.
  eexists. split.
  - zbft F_5efb4 D_5efb4.
    zstep F_5efb8 D_5efb8.
    stepn F_5efbc D_5efbc. rwH. rewrite art_zb_srli by lia. change (2 ^ 5) with 32.
    stepn F_5efc0 D_5efc0.
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]).
    intros r H1 H2; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.

Lemma art_ca_big : forall regs (M rom : word -> option byte) (s : Z),
  getr regs 14 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 512 -> 513 <= s <= 65536 ->
  msteps ASEGS (mkst regs (0x5f004 : word) M rom) (mkst regs (0x5f038 : word) M rom).
Proof.
  intros regs M rom s H14 H12 Hs.
  zbtk F_5efb4 D_5efb4.
  apply mst_refl.
Qed.
End FPX.
