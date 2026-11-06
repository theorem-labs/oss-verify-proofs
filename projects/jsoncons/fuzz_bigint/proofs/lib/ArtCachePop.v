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

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_cache_pop_core : forall regs (M rom : word -> option byte) (c ca ia cnt csz ch st spb : Z),
  getr regs 8 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 ca -> getr regs 10 = Z_to_bv 64 ia ->
  1 <= c <= 31 -> 0 <= ca -> ca + 4096 < 2 ^ 64 -> ca mod 8 = 0 -> 0 <= ia -> ia + 4096 < 2 ^ 64 ->
  1 <= cnt <= 16 -> 0 <= csz < 2 ^ 64 -> 0 <= ch < 2 ^ 32 -> 0 <= st < 2 ^ 64 -> 0 <= spb < 2 ^ 64 ->
  cellA M (ca + 80 * c) 4 cnt -> cellA M (ca + 80 * c + 8) 8 csz -> cellA M (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch ->
  cellA M (ca + 2576) 8 st -> cellA M (ia + 32) 8 spb ->
  wokA M (ca + 80 * c) 4 -> wokA M (ca + 2576) 8 ->
  apart (ca + 80 * c) 4 (ia + 32) 8 -> apart (ca + 2576) 8 (ia + 32) 8 ->
  exists regs',
    msteps ASEGS (mkst regs (0x41c5c : word) M rom)
                 (mkst regs' (0x41cb8 : word) (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) rom)
    /\ getr regs' 10 = Z_to_bv 64 (spb + c * 2 ^ 32 + ch * 16)
    /\ (forall r : reg, r <> 8%bv -> r <> 9%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom c ca ia cnt csz ch st spb H8 H11 H10 Hc Hca Hca' Hca8 Hia Hia' Hcnt Hcsz Hch Hst Hspb
         Ccnt Ccsz Cch Cst Cspb Wcnt Wst Ap1 Ap2.
  eexists. split.
  - zbft F_41c5c D_41c5c.
    zstep F_41c60 D_41c60.
    zbft F_41c64 D_41c64.
    zstep F_41c68 D_41c68.
    zstep F_41c6c D_41c6c.
    zstep F_41c70 D_41c70.
    zlw F_41c74 D_41c74 (ca + 80 * c) Ccnt.
    zbft F_41c78 D_41c78.
    zstep F_41c7c D_41c7c.
    zstep F_41c80 D_41c80.
    zstep F_41c84 D_41c84.
    zsw F_41c88 D_41c88 (ca + 80 * c) (cnt - 1) ltac:(exact Wcnt).
    zstep F_41c8c D_41c8c.
    assert (Ccsz1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 8) 8 csz) by recell Ccsz.
    assert (Cch1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch) by recell Cch.
    assert (Cst1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8 st) by recell Cst.
    assert (Wst1 : wokA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8) by rewok Wst.
    zld F_41c90 D_41c90 (ca + 80 * c + 8) Ccsz1.
    stepn F_41c94 D_41c94. rewrite (art_zb_srli_exact _ 30 (4 * (cnt - 1))) by lia.
    zstep F_41c98 D_41c98.
    zlwu F_41c9c D_41c9c (ca + 80 * c + 16 + 4 * (cnt - 1)) Cch1.
    zamoadd_d F_41ca0 D_41ca0 (ca + 2576) st csz Cst1 ltac:(exact Wst1).
    assert (Cspb2 : cellA (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) (ia + 32) 8 spb) by recell Cspb.
    zld F_41ca4 D_41ca4 (ia + 32) Cspb2.
    zstep F_41ca8 D_41ca8.
    zstep F_41cac D_41cac.
    zstep F_41cb0 D_41cb0.
    zstep F_41cb4 D_41cb4.
    apply mst_refl.
  - split; [gres; f_equal; lia|].
    intros r N8 N9 N10 N11 N12 N14; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.

(* [comment removed for export] *)
Definition art_pop_kept (r : reg) : Prop :=
  r <> 1%bv /\ r <> 2%bv /\ r <> 8%bv /\ r <> 9%bv /\ r <> 18%bv /\ r <> 19%bv /\ r <> 20%bv /\ r <> 11%bv /\ r <> 13%bv.

#[local] Ltac post_kept :=
  intros r Hr; unfold art_pop_kept in Hr; destruct Hr as (?&?&?&?&?&?&?&?&?); gres; try reflexivity;
  repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.

Lemma art_cache_pop_tail8 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word) (s0v s1v s2v s3v s4v : Z),
  getr regs 13 = Z_to_bv 64 8 -> getr regs 2 = Z_to_bv 64 sp -> 0 <= sp -> sp + 48 < 2 ^ 64 ->
  cellA M (sp + 40) 8 (bv_unsigned raw) -> ret_ok raw ->
  cellA M (sp + 32) 8 s0v -> cellA M (sp + 24) 8 s1v -> cellA M (sp + 16) 8 s2v -> cellA M (sp + 8) 8 s3v -> cellA M sp 8 s4v ->
  exists regs',
    msteps ASEGS (mkst regs (0x41cb8 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp + 48) /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v
    /\ getr regs' 19 = Z_to_bv 64 s3v /\ getr regs' 20 = Z_to_bv 64 s4v
    /\ (forall r : reg, art_pop_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw s0v s1v s2v s3v s4v H13 H2 Hsp Hsp' Cra Hret C0 C1 C2 C3 C4.
  eexists. split.
  - zstep F_41cb8 D_41cb8.
    zbtk F_41cbc D_41cbc.
    zld F_41ccc D_41ccc (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_41cd0 D_41cd0 (sp + 32) C0.
    zld F_41cd4 D_41cd4 (sp + 24) C1.
    zld F_41cd8 D_41cd8 (sp + 16) C2.
    zld F_41cdc D_41cdc (sp + 8) C3.
    zld F_41ce0 D_41ce0 sp C4.
    zstep F_41ce4 D_41ce4.
    stepret F_41ce8 D_41ce8 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; reflexivity|]). post_kept.
Qed.

Lemma art_land15_of_mod16 : forall x, 0 <= x -> x mod 16 = 0 -> Z.land 15 x = 0.
Proof.
  intros x Hx Hm. rewrite Z.land_comm. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. exact Hm.
Qed.

Lemma art_cache_pop_tail16 : forall regs (M rom : word -> option byte) (sp res : Z) (raw : word) (s0v s1v s2v s3v s4v : Z),
  getr regs 13 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 res ->
  0 <= sp -> sp + 48 < 2 ^ 64 -> 0 <= res < 2 ^ 64 -> res mod 16 = 0 ->
  cellA M (sp + 40) 8 (bv_unsigned raw) -> ret_ok raw ->
  cellA M (sp + 32) 8 s0v -> cellA M (sp + 24) 8 s1v -> cellA M (sp + 16) 8 s2v -> cellA M (sp + 8) 8 s3v -> cellA M sp 8 s4v ->
  exists regs',
    msteps ASEGS (mkst regs (0x41cb8 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp + 48) /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v
    /\ getr regs' 19 = Z_to_bv 64 s3v /\ getr regs' 20 = Z_to_bv 64 s4v
    /\ (forall r : reg, art_pop_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp res raw s0v s1v s2v s3v s4v H13 H2 H10 Hsp Hsp' Hres Hres16 Cra Hret C0 C1 C2 C3 C4.
  eexists. split.
  - zstep F_41cb8 D_41cb8.
    zbft F_41cbc D_41cbc.
    zstep F_41cc0 D_41cc0.
    stepn F_41cc4 D_41cc4. rwH. rewrite art_zb_and by lia. rewrite (art_land15_of_mod16 res) by lia.
    zbft F_41cc8 D_41cc8.
    zld F_41ccc D_41ccc (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_41cd0 D_41cd0 (sp + 32) C0.
    zld F_41cd4 D_41cd4 (sp + 24) C1.
    zld F_41cd8 D_41cd8 (sp + 16) C2.
    zld F_41cdc D_41cdc (sp + 8) C3.
    zld F_41ce0 D_41ce0 sp C4.
    zstep F_41ce4 D_41ce4.
    stepret F_41ce8 D_41ce8 raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; reflexivity|]). post_kept.
Qed.
End FPX.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
