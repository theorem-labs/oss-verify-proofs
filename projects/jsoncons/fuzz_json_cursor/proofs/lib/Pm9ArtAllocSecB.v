(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_59000_5a000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9ArtAllocB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_b_sec_fn : forall regs (M rom : word -> option byte) (sp ab n rs rz stk t ctx ob trp szt : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ab -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 (rs + rz + rz) ->
  getr regs 20 = Z_to_bv 64 rz -> getr regs 21 = Z_to_bv 64 n -> getr regs 23 = Z_to_bv 64 stk -> getr regs 25 = Z_to_bv 64 7 ->
  getr regs 26 = Z_to_bv 64 t -> getr regs 27 = Z_to_bv 64 1 ->
  0 <= sp -> sp + 128 < 2 ^ 64 -> 4096 <= ab -> ab + rs + rz + rz < 2 ^ 47 -> ab mod 16 = 0 ->
  1 <= n < 2 ^ 40 -> rs = (Z.max n 8 + 7) / 8 * 8 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> rs + rz + rz < 2 ^ 40 ->
  4096 <= stk -> stk + 16 < 2 ^ 64 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 4096 <= ctx -> ctx + 4096 < 2 ^ 64 -> 0 <= ob < 256 ->
  0 <= trp < 2 ^ 64 -> 0 <= szt < 2 ^ 64 ->
  wrA M (ab + rz - 16) 16 ->
  cellA M (ab + rz - 15) 1 ob -> cellA M (sp + 16) 8 16 -> cellA M t 8 ctx -> cellA M (ctx + 8) 4 0 -> cellA M stk 8 trp -> cellA M (stk + 8) 8 szt ->
  apart (ab + rz - 16) 16 sp 128 -> apart (ab + rz - 16) 16 t 8 -> apart (ab + rz - 16) 16 (ctx + 8) 4 -> apart (ab + rz - 16) 16 stk 16 ->
  msteps ASEGS (mkst regs (0x59abc : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x59bc8 : bv 64)%bv) 10 (Z_to_bv 64 trp)) 11 (Z_to_bv 64 szt)) 12 (Z_to_bv 64 0)) 14 (Z_to_bv 64 (ab + rs + rz + rz))) 18 (Z_to_bv 64 ab)) 20 (Z_to_bv 64 (ab + rz))) 21 (Z_to_bv 64 (ab + rz - 16))) 24 (Z_to_bv 64 0)) 25 (Z_to_bv 64 (ab + rz + n))) (0xa1564 : word) (art_alloc_memB M ab rz n ob) rom).
Proof.
  intros regs M rom sp ab n rs rz stk t ctx ob trp szt H2 H10 H9 H19 H20 H21 H23 H25 H26 H27 Hsp Hsp' Hab Hab' Hab16 Hn Hrs Hrz Hrz16 Hprim
         Hstk Hstk' Ht Ht' Hctx Hctx' Hob Htrp Hszt W Cob C16 Cctx Ctid Ctrp Cszt A1 A2 A3 A4.
  assert (Hrsn : n <= rs /\ rs <= n + 15) by (subst rs; split; [|]; lia).
  pose proof (art_hdr_b1a_range ob Hob) as Rb1a. pose proof (art_hdr_b1_range ob Hob) as Rb1.
  zstep F_59a74 D_59a74.
  zbft F_59a78 D_59a78.
  zstep F_59a7c D_59a7c.
  stepn F_59a80 D_59a80. rwH. rewrite art_zb_and by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  replace ((ab + rz) mod 8) with 0 by lia.
  zstep F_59a84 D_59a84.
  zbtk F_59a88 D_59a88.
  zstep F_59a94 D_59a94.
  zbft F_59a98 D_59a98.
  zlbu F_59a9c D_59a9c (ab + rz - 15) Cob.
  stepn F_59aa0 D_59aa0. rwH. rewrite art_zb_andi by lia. change (Z.land 1 3) with 1.
  stepn F_59aa4 D_59aa4. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612.
  pose proof (land_le_l ob 18446744073709551612 ltac:(lia) ltac:(lia)) as Lb.
  stepn F_59aa8 D_59aa8. rwH. unfold v_or. rewrite !art_u_lit by lia.
  change (Z.lor (Z.land ob 18446744073709551612) 1) with (art_hdr_b1a ob).
  stepn F_59aac D_59aac. rwH. rewrite art_zb_srli by lia.
  stepn F_59ab0 D_59ab0. rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small n (2 ^ 48)) by lia.
  zsb F_59ab4 D_59ab4 (ab + rz - 15) (art_hdr_b1a ob) ltac:(rewok W).
  zsh F_59ab8 D_59ab8 (ab + rz - 14) (n / 2 ^ 32) ltac:(rewok W).
  zsw F_59abc D_59abc (ab + rz - 12) n ltac:(rewok W).
  zbft F_59ac0 D_59ac0.
  zstep F_59ac4 D_59ac4.
  stepn F_59ac8 D_59ac8. rwH. rewrite art_zb_andi by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (sp + 16) 8 16) by (unfold apart in *; recell C16) end.
  zld F_59acc D_59acc (sp + 16) C16'.
  pose proof (land_le_l (art_hdr_b1a ob) 143 ltac:(lia) ltac:(lia)) as Lb2.
  stepn F_59ad0 D_59ad0. rwH. unfold v_or. rewrite !art_u_lit by lia.
  change (Z.lor (Z.land (art_hdr_b1a ob) 143) 16) with (art_hdr_b1 ob).
  zsb F_59ad4 D_59ad4 (ab + rz - 16 + 1) (art_hdr_b1 ob) ltac:(rewok W).
  zbft F_59ad8 D_59ad8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cctx' : cellA X t 8 ctx) by (unfold apart in *; recell Cctx);
    assert (Ctid' : cellA X (ctx + 8) 4 0) by (unfold apart in *; recell Ctid);
    assert (Ctrp' : cellA X stk 8 trp) by (unfold apart in *; recell Ctrp);
    assert (Cszt' : cellA X (stk + 8) 8 szt) by (unfold apart in *; recell Cszt) end.
  zld F_59adc D_59adc t Cctx'.
  zlw F_59ae0 D_59ae0 (ctx + 8) Ctid'.
  zstep F_59ae4 D_59ae4.
  stepn F_59ae8 D_59ae8.
  zld F_59b74 D_59b74 stk Ctrp'.
  zld F_59b78 D_59b78 (stk + 8) Cszt'.
  stepn F_59b7c D_59b7c.
  unfold art_alloc_memB. zret.
Qed.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
