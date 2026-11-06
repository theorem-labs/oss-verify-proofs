(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib ArtMem ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_cache_pop_core : forall regs (M rom : word -> option byte) (c ca ia cnt csz ch st spb : Z),
  getr regs 8 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 ca -> getr regs 10 = Z_to_bv 64 ia ->
  1 <= c <= 31 -> 0 <= ca -> ca + 4096 < 2 ^ 64 -> ca mod 8 = 0 -> 0 <= ia -> ia + 4096 < 2 ^ 64 ->
  1 <= cnt <= 16 -> 0 <= csz < 2 ^ 64 -> 0 <= ch < 2 ^ 32 -> 0 <= st < 2 ^ 64 -> 0 <= spb < 2 ^ 64 ->
  cellA M (ca + 80 * c) 4 cnt -> cellA M (ca + 80 * c + 8) 8 csz -> cellA M (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch ->
  cellA M (ca + 2576) 8 st -> cellA M (ia + 32) 8 spb ->
  wokA M (ca + 80 * c) 4 -> wokA M (ca + 2576) 8 ->
  apart (ca + 80 * c) 4 (ia + 32) 8 -> apart (ca + 2576) 8 (ia + 32) 8 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57ee0 : word) M rom)
                 (mkst regs' (0x57f3c : word) (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) rom)
    /\ getr regs' 10 = Z_to_bv 64 (spb + c * 2 ^ 32 + ch * 16)
    /\ (forall r : reg, r <> 8%bv -> r <> 9%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom c ca ia cnt csz ch st spb H8 H11 H10 Hc Hca Hca' Hca8 Hia Hia' Hcnt Hcsz Hch Hst Hspb
         Ccnt Ccsz Cch Cst Cspb Wcnt Wst Ap1 Ap2.
  eexists. split.
  - zbft F_57e90 D_57e90.
    zstep F_57e94 D_57e94.
    zbft F_57e98 D_57e98.
    zstep F_57e9c D_57e9c.
    zstep F_57ea0 D_57ea0.
    zstep F_57ea4 D_57ea4.
    zlw F_57ea8 D_57ea8 (ca + 80 * c) Ccnt.
    zbft F_57eac D_57eac.
    zstep F_57eb0 D_57eb0.
    zstep F_57eb4 D_57eb4.
    zstep F_57eb8 D_57eb8.
    zsw F_57ebc D_57ebc (ca + 80 * c) (cnt - 1) ltac:(exact Wcnt).
    zstep F_57ec0 D_57ec0.
    assert (Ccsz1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 8) 8 csz) by recell Ccsz.
    assert (Cch1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch) by recell Cch.
    assert (Cst1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8 st) by recell Cst.
    assert (Wst1 : wokA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8) by rewok Wst.
    zld F_57ec4 D_57ec4 (ca + 80 * c + 8) Ccsz1.
    stepn F_57ec8 D_57ec8. rewrite (art_zb_srli_exact _ 30 (4 * (cnt - 1))) by lia.
    zstep F_57ecc D_57ecc.
    zlwu F_57ed0 D_57ed0 (ca + 80 * c + 16 + 4 * (cnt - 1)) Cch1.
    zamoadd_d F_57ed4 D_57ed4 (ca + 2576) st csz Cst1 ltac:(exact Wst1).
    assert (Cspb2 : cellA (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) (ia + 32) 8 spb) by recell Cspb.
    zld F_57ed8 D_57ed8 (ia + 32) Cspb2.
    zstep F_57edc D_57edc.
    zstep F_57ee0 D_57ee0.
    zstep F_57ee4 D_57ee4.
    zstep F_57ee8 D_57ee8.
    apply mst_refl.
  - split; [gres; f_equal; lia|].
    intros r N8 N9 N10 N11 N12 N14; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.

Definition art_pop_kept (r : reg) : Prop :=
  r <> 1%bv /\ r <> 2%bv /\ r <> 8%bv /\ r <> 9%bv /\ r <> 18%bv /\ r <> 19%bv /\ r <> 20%bv /\ r <> 11%bv /\ r <> 13%bv.

#[local] Ltac post_kept :=
  intros r Hr; unfold art_pop_kept in Hr; destruct Hr as (?&?&?&?&?&?&?&?&?); gres; try reflexivity;
  repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.

#[using="Type"] Lemma art_cache_pop_tail8 : forall regs (M rom : word -> option byte) (sp : Z) (raw : word) (s0v s1v s2v s3v s4v : Z),
  getr regs 13 = Z_to_bv 64 8 -> getr regs 2 = Z_to_bv 64 sp -> 0 <= sp -> sp + 48 < 2 ^ 64 ->
  cellA M (sp + 40) 8 (bv_unsigned raw) -> ret_ok raw ->
  cellA M (sp + 32) 8 s0v -> cellA M (sp + 24) 8 s1v -> cellA M (sp + 16) 8 s2v -> cellA M (sp + 8) 8 s3v -> cellA M sp 8 s4v ->
  exists regs',
    msteps ASEGS (mkst regs (0x57f3c : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp + 48) /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v
    /\ getr regs' 19 = Z_to_bv 64 s3v /\ getr regs' 20 = Z_to_bv 64 s4v
    /\ (forall r : reg, art_pop_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp raw s0v s1v s2v s3v s4v H13 H2 Hsp Hsp' Cra Hret C0 C1 C2 C3 C4.
  eexists. split.
  - zstep F_57eec D_57eec.
    zbtk F_57ef0 D_57ef0.
    zld F_57f00 D_57f00 (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_57f04 D_57f04 (sp + 32) C0.
    zld F_57f08 D_57f08 (sp + 24) C1.
    zld F_57f0c D_57f0c (sp + 16) C2.
    zld F_57f10 D_57f10 (sp + 8) C3.
    zld F_57f14 D_57f14 sp C4.
    zstep F_57f18 D_57f18.
    stepret F_57f1c D_57f1c raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; reflexivity|]). post_kept.
Qed.

#[using="Type"] Lemma art_land15_of_mod16 : forall x, 0 <= x -> x mod 16 = 0 -> Z.land 15 x = 0.
Proof.
  intros x Hx Hm. rewrite Z.land_comm. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. exact Hm.
Qed.

#[using="Type"] Lemma art_cache_pop_tail16 : forall regs (M rom : word -> option byte) (sp res : Z) (raw : word) (s0v s1v s2v s3v s4v : Z),
  getr regs 13 = Z_to_bv 64 16 -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 res ->
  0 <= sp -> sp + 48 < 2 ^ 64 -> 0 <= res < 2 ^ 64 -> res mod 16 = 0 ->
  cellA M (sp + 40) 8 (bv_unsigned raw) -> ret_ok raw ->
  cellA M (sp + 32) 8 s0v -> cellA M (sp + 24) 8 s1v -> cellA M (sp + 16) 8 s2v -> cellA M (sp + 8) 8 s3v -> cellA M sp 8 s4v ->
  exists regs',
    msteps ASEGS (mkst regs (0x57f3c : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp + 48) /\ getr regs' 1 = raw
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v
    /\ getr regs' 19 = Z_to_bv 64 s3v /\ getr regs' 20 = Z_to_bv 64 s4v
    /\ (forall r : reg, art_pop_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp res raw s0v s1v s2v s3v s4v H13 H2 H10 Hsp Hsp' Hres Hres16 Cra Hret C0 C1 C2 C3 C4.
  eexists. split.
  - zstep F_57eec D_57eec.
    zbft F_57ef0 D_57ef0.
    zstep F_57ef4 D_57ef4.
    stepn F_57ef8 D_57ef8. rwH. rewrite art_zb_and by lia. rewrite (art_land15_of_mod16 res) by lia.
    zbft F_57efc D_57efc.
    zld F_57f00 D_57f00 (sp + 40) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_57f04 D_57f04 (sp + 32) C0.
    zld F_57f08 D_57f08 (sp + 24) C1.
    zld F_57f0c D_57f0c (sp + 16) C2.
    zld F_57f10 D_57f10 (sp + 8) C3.
    zld F_57f14 D_57f14 sp C4.
    zstep F_57f18 D_57f18.
    stepret F_57f1c D_57f1c raw ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat (split; [gres; rwH; reflexivity|]). post_kept.
Qed.
End FPX.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
