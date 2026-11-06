(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtLeaf ArtPoison.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_3d034_3dfbc As0_code_6dfb8_6e12c.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ArtAllocE.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_e32_sec_fn : forall regs (M rom : word -> option byte) (raw0 : word) (sp ab n rz b1 tp loff s0x s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 s0x -> 0 <= s0x < 2 ^ 64 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x633000 + 32 <= sp -> 0x633000 <= ab -> ab + rz < 2 ^ 47 -> ab mod 16 = 0 -> 1 <= n < 2 ^ 40 ->
  0 <= b1 < 256 -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= loff -> tp + loff + 4 < 2 ^ 64 -> ret_ok raw0 ->
  cellA M 0xd6510 8 loff -> cellA M (tp + loff) 4 0 -> apart (tp + loff) 4 (ab + rz - 16) 16 ->
  cellA M (ab + rz - 16 + 1) 1 b1 -> wrA M (ab + rz - 16) 16 -> wrA M (sp - 32) 32 -> art_layout M -> cellA M 0x16f600 8 0 ->
  apart (ab + rz - 16) 16 (sp - 32) 160 -> apart ab 16 (sp - 32) 160 ->
  cellA M (sp + 120) 8 (U raw0) -> cellA M (sp + 112) 8 s0v -> cellA M (sp + 104) 8 s1v -> cellA M (sp + 96) 8 s2v -> cellA M (sp + 88) 8 s3v -> cellA M (sp + 80) 8 s4v -> cellA M (sp + 72) 8 s5v -> cellA M (sp + 64) 8 s6v -> cellA M (sp + 56) 8 s7v -> cellA M (sp + 48) 8 s8v -> cellA M (sp + 40) 8 s9v -> cellA M (sp + 32) 8 s10v -> cellA M (sp + 24) 8 s11v ->
  32 <= rz <= 2048 -> rz mod 16 = 0 -> wrA M ab 16 -> cellA M 0x10340 8 0xcc6e96b9cc6e96b9 ->
  msteps ASEGS (mkst regs (0x3da50 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 (sp + 128))) 8 (Z_to_bv 64 s0v)) 9 (Z_to_bv 64 s1v)) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (ab + 16))) 18 (Z_to_bv 64 s2v)) 19 (Z_to_bv 64 s3v)) 20 (Z_to_bv 64 s4v)) 21 (Z_to_bv 64 s5v)) 22 (Z_to_bv 64 s6v)) 23 (Z_to_bv 64 s7v)) 24 (Z_to_bv 64 s8v)) 25 (Z_to_bv 64 s9v)) 26 (Z_to_bv 64 s10v)) 27 (Z_to_bv 64 s11v)) raw0 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 1 M (ab + rz - 15) (Z.land b1 243)) (ab + rz - 16) 2) (ab + 8) (ab + rz - 16)) ab 0xcc6e96b9cc6e96b9) (sp - 8) 0x3daa4) (sp - 16) s0x) (sp - 24) n) (sp - 32) ab) rom).
Proof.
  intros regs M rom raw0 sp ab n rz b1 tp loff s0x s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v H2 H4 H8 Hs0x H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
  intros Hrz Hrz16 Wab Cmag. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  pose proof (land_le_l' b1 243 ltac:(lia) ltac:(lia)) as Lb.
  stepn F_3da50 D_3da50.
  zcall (art_lsan_off_fn _ _ _ _ tp loff).
  zlbu F_3da54 D_3da54 (ab + rz - 16 + 1) Cb1.
  zstep F_3da58 D_3da58. zstep F_3da5c D_3da5c.
  stepn F_3da60 D_3da60. rwH. rewrite art_zb_andi by lia.
  stepn F_3da64 D_3da64. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_r.
  zstep F_3da68 D_3da68.
  zsb F_3da6c D_3da6c (ab + rz - 16 + 1) (Z.land b1 243) ltac:(rewok Wh).
  stepfence F_3da70 D_3da70.
  zsb F_3da74 D_3da74 (ab + rz - 16) 2 ltac:(rewok Wh).
  zbft F_3da78 D_3da78.
  zstep F_3da7c D_3da7c.
  zbft F_3da80 D_3da80.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmag' : cellA X 0x10340 8 0xcc6e96b9cc6e96b9) by (recell Cmag) end.
  zstep F_3da84 D_3da84. zld F_3da88 D_3da88 0x10340 Cmag'.
  zsd F_3da8c D_3da8c (ab + 8) (ab + rz - 16) ltac:(rewok Wab).
  stepfence F_3da90 D_3da90.
  zsd F_3da94 D_3da94 ab 0xcc6e96b9cc6e96b9 ltac:(rewok Wab).
  zstep F_3da98 D_3da98. zstep F_3da9c D_3da9c.
  stepn F_3daa0 D_3daa0.
  zcall (art_run_malloc_hooks_fn _ _ _ _ sp).
  zstep F_3daa4 D_3daa4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (C120 : cellA X (sp + 120) 8 (U raw0)) by (recell F120);
    assert (C112 : cellA X (sp + 112) 8 s0v) by (recell F112);
    assert (C104 : cellA X (sp + 104) 8 s1v) by (recell F104);
    assert (C96 : cellA X (sp + 96) 8 s2v) by (recell F96);
    assert (C88 : cellA X (sp + 88) 8 s3v) by (recell F88);
    assert (C80 : cellA X (sp + 80) 8 s4v) by (recell F80);
    assert (C72 : cellA X (sp + 72) 8 s5v) by (recell F72);
    assert (C64 : cellA X (sp + 64) 8 s6v) by (recell F64);
    assert (C56 : cellA X (sp + 56) 8 s7v) by (recell F56);
    assert (C48 : cellA X (sp + 48) 8 s8v) by (recell F48);
    assert (C40 : cellA X (sp + 40) 8 s9v) by (recell F40);
    assert (C32 : cellA X (sp + 32) 8 s10v) by (recell F32);
    assert (C24 : cellA X (sp + 24) 8 s11v) by (recell F24); idtac end.
  zld F_3daa8 D_3daa8 (sp + 120) C120. rewrite Z_to_bv_bv_unsigned.
  zld F_3daac D_3daac (sp + 112) C112.
  zld F_3dab0 D_3dab0 (sp + 104) C104.
  zld F_3dab4 D_3dab4 (sp + 96) C96.
  zld F_3dab8 D_3dab8 (sp + 88) C88.
  zld F_3dabc D_3dabc (sp + 80) C80.
  zld F_3dac0 D_3dac0 (sp + 72) C72.
  zld F_3dac4 D_3dac4 (sp + 64) C64.
  zld F_3dac8 D_3dac8 (sp + 56) C56.
  zld F_3dacc D_3dacc (sp + 48) C48.
  zld F_3dad0 D_3dad0 (sp + 40) C40.
  zld F_3dad4 D_3dad4 (sp + 32) C32.
  zld F_3dad8 D_3dad8 (sp + 24) C24.
  zstep F_3dadc D_3dadc.
  stepret F_3dae0 D_3dae0 raw0 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
