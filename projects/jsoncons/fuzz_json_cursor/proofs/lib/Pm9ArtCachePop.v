(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_5e000_5f000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).

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
    msteps ASEGS (mkst regs (0x5e108 : word) M rom)
                 (mkst regs' (0x5e164 : word) (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) rom)
    /\ getr regs' 10 = Z_to_bv 64 (spb + c * 2 ^ 32 + ch * 16)
    /\ (forall r : reg, r <> 8%bv -> r <> 9%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom c ca ia cnt csz ch st spb H8 H11 H10 Hc Hca Hca' Hca8 Hia Hia' Hcnt Hcsz Hch Hst Hspb
         Ccnt Ccsz Cch Cst Cspb Wcnt Wst Ap1 Ap2.
  eexists. split.
  - zbft F_5e0c0 D_5e0c0.
    zstep F_5e0c4 D_5e0c4.
    zbft F_5e0c8 D_5e0c8.
    zstep F_5e0cc D_5e0cc.
    zstep F_5e0d0 D_5e0d0.
    zstep F_5e0d4 D_5e0d4.
    zlw F_5e0d8 D_5e0d8 (ca + 80 * c) Ccnt.
    zbft F_5e0dc D_5e0dc.
    zstep F_5e0e0 D_5e0e0.
    zstep F_5e0e4 D_5e0e4.
    zstep F_5e0e8 D_5e0e8.
    zsw F_5e0ec D_5e0ec (ca + 80 * c) (cnt - 1) ltac:(exact Wcnt).
    zstep F_5e0f0 D_5e0f0.
    assert (Ccsz1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 8) 8 csz) by recell Ccsz.
    assert (Cch1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch) by recell Cch.
    assert (Cst1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8 st) by recell Cst.
    assert (Wst1 : wokA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8) by rewok Wst.
    zld F_5e0f4 D_5e0f4 (ca + 80 * c + 8) Ccsz1.
    stepn F_5e0f8 D_5e0f8. rewrite (art_zb_srli_exact _ 30 (4 * (cnt - 1))) by lia.
    zstep F_5e0fc D_5e0fc.
    zlwu F_5e100 D_5e100 (ca + 80 * c + 16 + 4 * (cnt - 1)) Cch1.
    zamoadd_d F_5e104 D_5e104 (ca + 2576) st csz Cst1 ltac:(exact Wst1).
    assert (Cspb2 : cellA (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) (ia + 32) 8 spb) by recell Cspb.
    zld F_5e108 D_5e108 (ia + 32) Cspb2.
    zstep F_5e10c D_5e10c.
    zstep F_5e110 D_5e110.
    zstep F_5e114 D_5e114.
    zstep F_5e118 D_5e118.
    apply mst_refl.
  - split; [gres; f_equal; lia|].
    intros r N8 N9 N10 N11 N12 N14; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.

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
    msteps ASEGS (mkst regs (0x5e164 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp + 48) /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v
    /\ getr regs' 19 = Z_to_bv 64 s3v /\ getr regs' 20 = Z_to_bv 64 s4v
    /\ (forall r : reg, art_pop_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw s0v s1v s2v s3v s4v H13 H2 Hsp Hsp' Cra Hret C0 C1 C2 C3 C4.
  eexists. split.
  - zstep F_5e11c D_5e11c.
    zbtk F_5e120 D_5e120.
    zld F_5e130 D_5e130 (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_5e134 D_5e134 (sp + 32) C0.
    zld F_5e138 D_5e138 (sp + 24) C1.
    zld F_5e13c D_5e13c (sp + 16) C2.
    zld F_5e140 D_5e140 (sp + 8) C3.
    zld F_5e144 D_5e144 sp C4.
    zstep F_5e148 D_5e148.
    stepret F_5e14c D_5e14c raw ltac:(rwH; reflexivity).
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
    msteps ASEGS (mkst regs (0x5e164 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp + 48) /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v
    /\ getr regs' 19 = Z_to_bv 64 s3v /\ getr regs' 20 = Z_to_bv 64 s4v
    /\ (forall r : reg, art_pop_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp res raw s0v s1v s2v s3v s4v H13 H2 H10 Hsp Hsp' Hres Hres16 Cra Hret C0 C1 C2 C3 C4.
  eexists. split.
  - zstep F_5e11c D_5e11c.
    zbft F_5e120 D_5e120.
    zstep F_5e124 D_5e124.
    stepn F_5e128 D_5e128. rwH. rewrite art_zb_and by lia. rewrite (art_land15_of_mod16 res) by lia.
    zbft F_5e12c D_5e12c.
    zld F_5e130 D_5e130 (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_5e134 D_5e134 (sp + 32) C0.
    zld F_5e138 D_5e138 (sp + 24) C1.
    zld F_5e13c D_5e13c (sp + 16) C2.
    zld F_5e140 D_5e140 (sp + 8) C3.
    zld F_5e144 D_5e144 sp C4.
    zstep F_5e148 D_5e148.
    stepret F_5e14c D_5e14c raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; reflexivity|]). post_kept.
Qed.
End FPX.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
