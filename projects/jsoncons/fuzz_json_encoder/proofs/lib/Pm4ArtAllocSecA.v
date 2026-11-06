(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm4ArtLeaf Pm4ArtRzLog Pm4ArtAllocA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4_code_5a000_5b000 .
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
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x6c0000 -> 0x6c0000 + 16 <= sp ->
  1 <= n < 2 ^ 39 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 7) / 8 * 8 -> rz = 16 * 2 ^ r -> 65536 < rs + rz ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x5a9dc : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5aac8 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 0)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + rz + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + rz + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 8))) 26 (Z_to_bv 64 t)) (0x5ef80 : word) (Wn 8 M (sp - 8) 0x5aaac) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hsec W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs8 : rs mod 8 = 0) by (subst rs; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 7) 8 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. }
  assert (Hrshi : rs <= n + 7 \/ rs = 8). { subst rs. pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. }
  assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_5a98c D_5a98c. zstep F_5a990 D_5a990. zstep F_5a994 D_5a994. zstep F_5a998 D_5a998. zstep F_5a99c D_5a99c.
  stepn F_5a9a0 D_5a9a0. rwH. rewrite art_zb_and by lia. rewrite art_land_m8 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 8 * 8)] => replace (e / 8 * 8) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_5a9a4 D_5a9a4. zstep F_5a9a8 D_5a9a8.
  stepn F_5a9ac D_5a9ac. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_5a9b0 D_5a9b0.
  zstep F_5a9b4 D_5a9b4. zstep F_5a9b8 D_5a9b8. zstep F_5a9bc D_5a9bc.
  stepn F_5a9c0 D_5a9c0. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_5a9c4 D_5a9c4. zstep F_5a9c8 D_5a9c8. zstep F_5a9cc D_5a9cc. zstep F_5a9d0 D_5a9d0. zstep F_5a9d4 D_5a9d4. zstep F_5a9d8 D_5a9d8.
  zstep F_5a9dc D_5a9dc.
  stepn F_5a9e0 D_5a9e0. rwH. rewrite art_zb_and by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite (Z.mod_small rz) by lia.
  zstep F_5a9e4 D_5a9e4. zstep F_5a9e8 D_5a9e8.
  zbft F_5a9ec D_5a9ec. zbft F_5a9f0 D_5a9f0.
  zld F_5a9f4 D_5a9f4 (ia + 3616) Cmax.
  zbtk F_5a9f8 D_5a9f8.
  stepn F_5aa58 D_5aa58.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_5aa60 D_5aa60 || (zstep F_5aa5c D_5aa5c; zbft F_5aa60 D_5aa60).
  zstep F_5aa64 D_5aa64. zstep F_5aa68 D_5aa68. zstep F_5aa6c D_5aa6c. zstep F_5aa70 D_5aa70.
  stepn F_5aa74 D_5aa74.
  zret.
Qed.
End FPX.
