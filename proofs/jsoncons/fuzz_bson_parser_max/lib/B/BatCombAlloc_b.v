(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtAtomics ArtTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r41498_42984_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).

(* [comment removed for export] *)
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
    msteps ASEGS (mkst regs (0x56d3c : word) M rom)
                 (mkst regs' (0x56dc0 : word)
                       (art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 14 = Z_to_bv 64 s /\ getr regs' 12 = Z_to_bv 64 512 /\ getr regs' 15 = Z_to_bv 64 65536
    /\ (forall r : reg, art_ca_entry_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp s H2 H12 H13 Hsp Hsp' Hs W.
  eexists. split.
  - zstep F_56924 D_56924.
    zsd F_56928 D_56928 (sp - 8) (U (getr regs 1)) ltac:(rewok W).
    zsd F_5692c D_5692c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_56930 D_56930 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
    zsd F_56934 D_56934 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_56938 D_56938 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
    zsd F_5693c D_5693c (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zstep F_56940 D_56940.
    zstep F_56944 D_56944.
    zstep F_56948 D_56948.
    zbtk F_5694c D_5694c.
    zstep F_56970 D_56970.
    zstep F_56974 D_56974.
    zbtk F_56978 D_56978.
    zstep F_56998 D_56998.
    zbft F_5699c D_5699c.
    zbft F_569a0 D_569a0.
    zstep F_569a4 D_569a4.
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]).
    intros r Hr; unfold art_ca_entry_kept in Hr; destruct Hr as (?&?&?&?); gres; try reflexivity;
    repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.

#[using="Type"] Lemma art_ca_small : forall regs (M rom : word -> option byte) (s : Z),
  getr regs 14 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 512 -> 1 <= s <= 512 ->
  exists regs',
    msteps ASEGS (mkst regs (0x56dc0 : word) M rom) (mkst regs' (0x56ed0 : word) M rom)
    /\ getr regs' 8 = Z_to_bv 64 ((s + 31) / 32) /\ getr regs' 14 = Z_to_bv 64 (s + 31)
    /\ (forall r : reg, r <> 8%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom s H14 H12 Hs.
  eexists. split.
  - zbft F_569a8 D_569a8.
    zstep F_569ac D_569ac.
    stepn F_569b0 D_569b0. rwH. rewrite art_zb_srli by lia. change (2 ^ 5) with 32.
    stepn F_569b4 D_569b4.
    apply mst_refl.
  - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia] |]).
    intros r H1 H2; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.

#[using="Type"] Lemma art_ca_big : forall regs (M rom : word -> option byte) (s : Z),
  getr regs 14 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 512 -> 513 <= s <= 65536 ->
  msteps ASEGS (mkst regs (0x56dc0 : word) M rom) (mkst regs (0x56df4 : word) M rom).
Proof.
  intros regs M rom s H14 H12 Hs.
  zbtk F_569a8 D_569a8.
  apply mst_refl.
Qed.
End FPX.
