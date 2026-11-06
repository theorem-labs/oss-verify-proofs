(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtLeaf ArtRzLog ArtAllocA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_3d034_3dfbc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_a3_sec_fn : forall regs (M rom : word -> option byte) (sp ia n r rs rz tp key tsd ctx t : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 8 -> getr regs 10 = Z_to_bv 64 (Z.max n 8) ->
  getr regs 18 = Z_to_bv 64 8 -> getr regs 19 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 65536 -> getr regs 21 = Z_to_bv 64 n ->
  getr regs 22 = Z_to_bv 64 ia -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x633000 -> 0x633000 + 16 <= sp ->
  1 <= n < 2 ^ 39 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 7) / 8 * 8 -> rz = 16 * 2 ^ r -> 65536 < rs + rz ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x3d524 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d610 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 0)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + rz + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + rz + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 8))) 26 (Z_to_bv 64 t)) (0x41ac8 : word) (Wn 8 M (sp - 8) 0x3d5f4) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hsec W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs8 : rs mod 8 = 0) by (subst rs; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 7) 8 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. }
  assert (Hrshi : rs <= n + 7 \/ rs = 8). { subst rs. pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. }
  assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_3d524 D_3d524. zstep F_3d528 D_3d528. zstep F_3d52c D_3d52c. zstep F_3d530 D_3d530. zstep F_3d534 D_3d534.
  stepn F_3d538 D_3d538. rwH. rewrite art_zb_and by lia. rewrite art_land_m8 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 8 * 8)] => replace (e / 8 * 8) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_3d53c D_3d53c. zstep F_3d540 D_3d540.
  stepn F_3d544 D_3d544. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_3d548 D_3d548.
  zstep F_3d54c D_3d54c. zstep F_3d550 D_3d550. zstep F_3d554 D_3d554.
  stepn F_3d558 D_3d558. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_3d55c D_3d55c. zstep F_3d560 D_3d560. zstep F_3d564 D_3d564. zstep F_3d568 D_3d568. zstep F_3d56c D_3d56c. zstep F_3d570 D_3d570.
  zstep F_3d574 D_3d574.
  stepn F_3d578 D_3d578. rwH. rewrite art_zb_and by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite (Z.mod_small rz) by lia.
  zstep F_3d57c D_3d57c. zstep F_3d580 D_3d580.
  zbft F_3d584 D_3d584. zbft F_3d588 D_3d588.
  zld F_3d58c D_3d58c (ia + 3616) Cmax.
  zbtk F_3d590 D_3d590.
  stepn F_3d5f0 D_3d5f0.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_3d5f8 D_3d5f8 || (zstep F_3d5f4 D_3d5f4; zbft F_3d5f8 D_3d5f8).
  zstep F_3d5fc D_3d5fc. zstep F_3d600 D_3d600. zstep F_3d604 D_3d604. zstep F_3d608 D_3d608.
  stepn F_3d60c D_3d60c.
  zret.
Qed.
End FPX.
