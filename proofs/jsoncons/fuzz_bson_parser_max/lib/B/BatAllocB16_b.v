(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r3cf10_3de98_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocB_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_hdr_b1_16 (ob : Z) : Z := Z.lor (Z.land (art_hdr_b1a ob) 143) 32.
Lemma art_hdr_b1_16_range : forall ob, 0 <= ob < 256 -> 0 <= art_hdr_b1_16 ob < 256.
Proof. intros ob Hob. unfold art_hdr_b1_16. pose proof (art_hdr_b1a_range ob Hob). apply lor_lt_256; [|lia]. pose proof (land_le_l (art_hdr_b1a ob) 143 ltac:(lia) ltac:(lia)). lia. Qed.
Definition art_alloc_memB_16 (M : word -> option byte) (ab rz n ob : Z) : word -> option byte :=
  Wn 1 (Wn 4 (Wn 2 (Wn 1 M (ab + rz - 15) (art_hdr_b1a ob)) (ab + rz - 14) (n / 2 ^ 32)) (ab + rz - 12) n) (ab + rz - 15) (art_hdr_b1_16 ob).

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_alloc_b_16_fn : forall regs (M rom : word -> option byte) (sp ab n rs rz stk t ctx ob trp szt : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ab -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 (rs + 16 + rz) ->
  getr regs 20 = Z_to_bv 64 rz -> getr regs 21 = Z_to_bv 64 n -> getr regs 23 = Z_to_bv 64 stk -> getr regs 25 = Z_to_bv 64 15 ->
  getr regs 26 = Z_to_bv 64 t -> getr regs 27 = Z_to_bv 64 1 ->
  0 <= sp -> sp + 128 < 2 ^ 64 -> 4096 <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 ->
  1 <= n < 2 ^ 40 -> rs = (Z.max n 8 + 15) / 16 * 16 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> rs + 16 + rz <= 65536 ->
  4096 <= stk -> stk + 16 < 2 ^ 64 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 4096 <= ctx -> ctx + 4096 < 2 ^ 64 -> 0 <= ob < 256 ->
  0 <= trp < 2 ^ 64 -> 0 <= szt < 2 ^ 64 ->
  wrA M (ab + rz - 16) 16 ->
  cellA M (ab + rz - 15) 1 ob -> cellA M (sp + 16) 8 32 -> cellA M t 8 ctx -> cellA M (ctx + 8) 4 0 -> cellA M stk 8 trp -> cellA M (stk + 8) 8 szt ->
  apart (ab + rz - 16) 16 sp 128 -> apart (ab + rz - 16) 16 t 8 -> apart (ab + rz - 16) 16 (ctx + 8) 4 -> apart (ab + rz - 16) 16 stk 16 ->
  msteps ASEGS (mkst regs (0x52884 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x52990 : bv 64)%bv) 10 (Z_to_bv 64 trp)) 11 (Z_to_bv 64 szt)) 12 (Z_to_bv 64 0)) 14 (Z_to_bv 64 (ab + rs + 16 + rz))) 18 (Z_to_bv 64 ab)) 20 (Z_to_bv 64 (ab + rz))) 21 (Z_to_bv 64 (ab + rz - 16))) 24 (Z_to_bv 64 0)) 25 (Z_to_bv 64 (ab + rz + n))) (0x99fc4 : word) (art_alloc_memB_16 M ab rz n ob) rom).
Proof.
  intros regs M rom sp ab n rs rz stk t ctx ob trp szt H2 H10 H9 H19 H20 H21 H23 H25 H26 H27 Hsp Hsp' Hab Hab' Hab16 Hn Hrs Hrz Hrz16 Hprim
         Hstk Hstk' Ht Ht' Hctx Hctx' Hob Htrp Hszt W Cob C16 Cctx Ctid Ctrp Cszt A1 A2 A3 A4.
  assert (Hrsn : n <= rs /\ rs <= n + 23) by (subst rs; split; [|]; lia).
  pose proof (art_hdr_b1a_range ob Hob) as Rb1a. pose proof (art_hdr_b1_16_range ob Hob) as Rb1.
  zstep F_5246c D_5246c.
  zbft F_52470 D_52470.
  zstep F_52474 D_52474.
  stepn F_52478 D_52478. rwH. rewrite art_zb_and by lia. change 15 with (Z.ones 4) at 1. rewrite Z.land_ones by lia. change (2 ^ 4) with 16.
  replace ((ab + rz) mod 16) with 0 by lia.
  zstep F_5247c D_5247c.
  zbtk F_52480 D_52480.
  zstep F_5248c D_5248c.
  zbft F_52490 D_52490.
  zlbu F_52494 D_52494 (ab + rz - 15) Cob.
  stepn F_52498 D_52498. rwH. rewrite art_zb_andi by lia. change (Z.land 1 3) with 1.
  stepn F_5249c D_5249c. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612.
  pose proof (land_le_l ob 18446744073709551612 ltac:(lia) ltac:(lia)) as Lb.
  stepn F_524a0 D_524a0. rwH. unfold v_or. rewrite !art_u_lit by lia.
  change (Z.lor (Z.land ob 18446744073709551612) 1) with (art_hdr_b1a ob).
  stepn F_524a4 D_524a4. rwH. rewrite art_zb_srli by lia.
  stepn F_524a8 D_524a8. rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small n (2 ^ 48)) by lia.
  zsb F_524ac D_524ac (ab + rz - 15) (art_hdr_b1a ob) ltac:(rewok W).
  zsh F_524b0 D_524b0 (ab + rz - 14) (n / 2 ^ 32) ltac:(rewok W).
  zsw F_524b4 D_524b4 (ab + rz - 12) n ltac:(rewok W).
  zbft F_524b8 D_524b8.
  zstep F_524bc D_524bc.
  stepn F_524c0 D_524c0. rwH. rewrite art_zb_andi by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (sp + 16) 8 32) by (unfold apart in *; recell C16) end.
  zld F_524c4 D_524c4 (sp + 16) C16'.
  pose proof (land_le_l (art_hdr_b1a ob) 143 ltac:(lia) ltac:(lia)) as Lb2.
  stepn F_524c8 D_524c8. rwH. unfold v_or. rewrite !art_u_lit by lia.
  change (Z.lor (Z.land (art_hdr_b1a ob) 143) 32) with (art_hdr_b1_16 ob).
  zsb F_524cc D_524cc (ab + rz - 16 + 1) (art_hdr_b1_16 ob) ltac:(rewok W).
  zbft F_524d0 D_524d0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cctx' : cellA X t 8 ctx) by (unfold apart in *; recell Cctx);
    assert (Ctid' : cellA X (ctx + 8) 4 0) by (unfold apart in *; recell Ctid);
    assert (Ctrp' : cellA X stk 8 trp) by (unfold apart in *; recell Ctrp);
    assert (Cszt' : cellA X (stk + 8) 8 szt) by (unfold apart in *; recell Cszt) end.
  zld F_524d4 D_524d4 t Cctx'.
  zlw F_524d8 D_524d8 (ctx + 8) Ctid'.
  zstep F_524dc D_524dc.
  stepn F_524e0 D_524e0.
  zld F_5256c D_5256c stk Ctrp'.
  zld F_52570 D_52570 (stk + 8) Cszt'.
  stepn F_52574 D_52574.
  unfold art_alloc_memB_16. zret.
Qed.

End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
