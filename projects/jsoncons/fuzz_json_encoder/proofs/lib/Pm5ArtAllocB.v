(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5_code_5b000_5c000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_hdr_b1a (ob : Z) : Z := Z.lor (Z.land ob 18446744073709551612) 1.
Definition art_hdr_b1 (ob : Z) : Z := Z.lor (Z.land (art_hdr_b1a ob) 143) 16.

Lemma lor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
  intros a b Ha Hb. split. apply Z.lor_nonneg; lia.
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|NZ]; [rewrite E; lia|].
  assert (Hl : Z.log2 (Z.lor a b) < 8).
  { rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
    - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
    - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  apply Z.log2_lt_pow2 in Hl; [exact Hl|]. pose proof (Z.lor_nonneg a b). lia.
Qed.
Lemma land_le_l a m : 0 <= a -> 0 <= m -> 0 <= Z.land a m <= a.
Proof.
  intros Ha Hm. split. apply Z.land_nonneg. left; exact Ha.
  rewrite Z.land_comm.
  pose proof (Z.lor_ldiff_and a m) as E1. pose proof (Z.add_lor_land (Z.ldiff a m) (Z.land m a)) as E2.
  rewrite (Z.land_comm m a) in E2.
  assert (Z0: Z.land (Z.ldiff a m) (Z.land a m) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.ldiff_spec, Z.bits_0. destruct (Z.testbit a i), (Z.testbit m i); reflexivity. }
  assert (D0: 0 <= Z.ldiff a m). { apply Z.ldiff_nonneg. left; exact Ha. }
  rewrite (Z.land_comm m a). lia.
Qed.
Lemma art_hdr_b1a_range : forall ob, 0 <= ob < 256 -> 0 <= art_hdr_b1a ob < 256.
Proof. intros ob Hob. unfold art_hdr_b1a. apply lor_lt_256; [|lia]. pose proof (land_le_l ob 18446744073709551612 ltac:(lia) ltac:(lia)). lia. Qed.
Lemma art_hdr_b1_range : forall ob, 0 <= ob < 256 -> 0 <= art_hdr_b1 ob < 256.
Proof. intros ob Hob. unfold art_hdr_b1. pose proof (art_hdr_b1a_range ob Hob). apply lor_lt_256; [|lia]. pose proof (land_le_l (art_hdr_b1a ob) 143 ltac:(lia) ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Definition art_alloc_memB (M : word -> option byte) (ab rz n ob : Z) : word -> option byte :=
  Wn 1 (Wn 4 (Wn 2 (Wn 1 M (ab + rz - 15) (art_hdr_b1a ob)) (ab + rz - 14) (n / 2 ^ 32)) (ab + rz - 12) n) (ab + rz - 15) (art_hdr_b1 ob).

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_b_fn : forall regs (M rom : word -> option byte) (sp ab n rs rz stk t ctx ob trp szt : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ab -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 (rs + rz) ->
  getr regs 20 = Z_to_bv 64 rz -> getr regs 21 = Z_to_bv 64 n -> getr regs 23 = Z_to_bv 64 stk -> getr regs 25 = Z_to_bv 64 7 ->
  getr regs 26 = Z_to_bv 64 t -> getr regs 27 = Z_to_bv 64 1 ->
  0 <= sp -> sp + 128 < 2 ^ 64 -> 4096 <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 ->
  1 <= n < 2 ^ 40 -> rs = (Z.max n 8 + 7) / 8 * 8 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> rs + rz <= 65536 ->
  4096 <= stk -> stk + 16 < 2 ^ 64 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 4096 <= ctx -> ctx + 4096 < 2 ^ 64 -> 0 <= ob < 256 ->
  0 <= trp < 2 ^ 64 -> 0 <= szt < 2 ^ 64 ->
  wrA M (ab + rz - 16) 16 ->
  cellA M (ab + rz - 15) 1 ob -> cellA M (sp + 16) 8 16 -> cellA M t 8 ctx -> cellA M (ctx + 8) 4 0 -> cellA M stk 8 trp -> cellA M (stk + 8) 8 szt ->
  apart (ab + rz - 16) 16 sp 128 -> apart (ab + rz - 16) 16 t 8 -> apart (ab + rz - 16) 16 (ctx + 8) 4 -> apart (ab + rz - 16) 16 stk 16 ->
  msteps ASEGS (mkst regs (0x5b398 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5b4a4 : bv 64)%bv) 10 (Z_to_bv 64 trp)) 11 (Z_to_bv 64 szt)) 12 (Z_to_bv 64 0)) 14 (Z_to_bv 64 (ab + rs + rz))) 18 (Z_to_bv 64 ab)) 20 (Z_to_bv 64 (ab + rz))) 21 (Z_to_bv 64 (ab + rz - 16))) 24 (Z_to_bv 64 0)) 25 (Z_to_bv 64 (ab + rz + n))) (0xa2e40 : word) (art_alloc_memB M ab rz n ob) rom).
Proof.
  intros regs M rom sp ab n rs rz stk t ctx ob trp szt H2 H10 H9 H19 H20 H21 H23 H25 H26 H27 Hsp Hsp' Hab Hab' Hab16 Hn Hrs Hrz Hrz16 Hprim
         Hstk Hstk' Ht Ht' Hctx Hctx' Hob Htrp Hszt W Cob C16 Cctx Ctid Ctrp Cszt A1 A2 A3 A4.
  assert (Hrsn : n <= rs /\ rs <= n + 15) by (subst rs; split; [|]; lia).
  pose proof (art_hdr_b1a_range ob Hob) as Rb1a. pose proof (art_hdr_b1_range ob Hob) as Rb1.
  zstep F_5b350 D_5b350.
  zbft F_5b354 D_5b354.
  zstep F_5b358 D_5b358.
  stepn F_5b35c D_5b35c. rwH. rewrite art_zb_and by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  replace ((ab + rz) mod 8) with 0 by lia.
  zstep F_5b360 D_5b360.
  zbtk F_5b364 D_5b364.
  zstep F_5b370 D_5b370.
  zbft F_5b374 D_5b374.
  zlbu F_5b378 D_5b378 (ab + rz - 15) Cob.
  stepn F_5b37c D_5b37c. rwH. rewrite art_zb_andi by lia. change (Z.land 1 3) with 1.
  stepn F_5b380 D_5b380. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612.
  pose proof (land_le_l ob 18446744073709551612 ltac:(lia) ltac:(lia)) as Lb.
  stepn F_5b384 D_5b384. rwH. unfold v_or. rewrite !art_u_lit by lia.
  change (Z.lor (Z.land ob 18446744073709551612) 1) with (art_hdr_b1a ob).
  stepn F_5b388 D_5b388. rwH. rewrite art_zb_srli by lia.
  stepn F_5b38c D_5b38c. rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small n (2 ^ 48)) by lia.
  zsb F_5b390 D_5b390 (ab + rz - 15) (art_hdr_b1a ob) ltac:(rewok W).
  zsh F_5b394 D_5b394 (ab + rz - 14) (n / 2 ^ 32) ltac:(rewok W).
  zsw F_5b398 D_5b398 (ab + rz - 12) n ltac:(rewok W).
  zbft F_5b39c D_5b39c.
  zstep F_5b3a0 D_5b3a0.
  stepn F_5b3a4 D_5b3a4. rwH. rewrite art_zb_andi by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (sp + 16) 8 16) by (unfold apart in *; recell C16) end.
  zld F_5b3a8 D_5b3a8 (sp + 16) C16'.
  pose proof (land_le_l (art_hdr_b1a ob) 143 ltac:(lia) ltac:(lia)) as Lb2.
  stepn F_5b3ac D_5b3ac. rwH. unfold v_or. rewrite !art_u_lit by lia.
  change (Z.lor (Z.land (art_hdr_b1a ob) 143) 16) with (art_hdr_b1 ob).
  zsb F_5b3b0 D_5b3b0 (ab + rz - 16 + 1) (art_hdr_b1 ob) ltac:(rewok W).
  zbft F_5b3b4 D_5b3b4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cctx' : cellA X t 8 ctx) by (unfold apart in *; recell Cctx);
    assert (Ctid' : cellA X (ctx + 8) 4 0) by (unfold apart in *; recell Ctid);
    assert (Ctrp' : cellA X stk 8 trp) by (unfold apart in *; recell Ctrp);
    assert (Cszt' : cellA X (stk + 8) 8 szt) by (unfold apart in *; recell Cszt) end.
  zld F_5b3b8 D_5b3b8 t Cctx'.
  zlw F_5b3bc D_5b3bc (ctx + 8) Ctid'.
  zstep F_5b3c0 D_5b3c0.
  stepn F_5b3c4 D_5b3c4.
  zld F_5b450 D_5b450 stk Ctrp'.
  zld F_5b454 D_5b454 (stk + 8) Cszt'.
  stepn F_5b458 D_5b458.
  unfold art_alloc_memB. zret.
Qed.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
