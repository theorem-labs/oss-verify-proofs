(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm9ArtLeaf Pm9ArtPoison.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_59000_5a000 .
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9ArtAllocE.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_e32_sec_fn : forall regs (M rom : word -> option byte) (raw0 : word) (sp ab n rz b1 tp loff s0x s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 s0x -> 0 <= s0x < 2 ^ 64 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x6b4000 + 32 <= sp -> 0x6b4000 <= ab -> ab + rz < 2 ^ 47 -> ab mod 16 = 0 -> 1 <= n < 2 ^ 40 ->
  0 <= b1 < 256 -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= loff -> tp + loff + 4 < 2 ^ 64 -> ret_ok raw0 ->
  cellA M 0x155160 8 loff -> cellA M (tp + loff) 4 0 -> apart (tp + loff) 4 (ab + rz - 16) 16 ->
  cellA M (ab + rz - 16 + 1) 1 b1 -> wrA M (ab + rz - 16) 16 -> wrA M (sp - 32) 32 -> art_layout M -> cellA M 0x1ef7c0 8 0 ->
  apart (ab + rz - 16) 16 (sp - 32) 160 -> apart ab 16 (sp - 32) 160 ->
  cellA M (sp + 120) 8 (U raw0) -> cellA M (sp + 112) 8 s0v -> cellA M (sp + 104) 8 s1v -> cellA M (sp + 96) 8 s2v -> cellA M (sp + 88) 8 s3v -> cellA M (sp + 80) 8 s4v -> cellA M (sp + 72) 8 s5v -> cellA M (sp + 64) 8 s6v -> cellA M (sp + 56) 8 s7v -> cellA M (sp + 48) 8 s8v -> cellA M (sp + 40) 8 s9v -> cellA M (sp + 32) 8 s10v -> cellA M (sp + 24) 8 s11v ->
  32 <= rz <= 2048 -> rz mod 16 = 0 -> wrA M ab 16 -> cellA M 0x10388 8 0xcc6e96b9cc6e96b9 ->
  msteps ASEGS (mkst regs (0x59efc : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 (sp + 128))) 8 (Z_to_bv 64 s0v)) 9 (Z_to_bv 64 s1v)) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (ab + 16))) 18 (Z_to_bv 64 s2v)) 19 (Z_to_bv 64 s3v)) 20 (Z_to_bv 64 s4v)) 21 (Z_to_bv 64 s5v)) 22 (Z_to_bv 64 s6v)) 23 (Z_to_bv 64 s7v)) 24 (Z_to_bv 64 s8v)) 25 (Z_to_bv 64 s9v)) 26 (Z_to_bv 64 s10v)) 27 (Z_to_bv 64 s11v)) raw0 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 1 M (ab + rz - 15) (Z.land b1 243)) (ab + rz - 16) 2) (ab + 8) (ab + rz - 16)) ab 0xcc6e96b9cc6e96b9) (sp - 8) 0x59f50) (sp - 16) s0x) (sp - 24) n) (sp - 32) ab) rom).
Proof.
  intros regs M rom raw0 sp ab n rz b1 tp loff s0x s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v H2 H4 H8 Hs0x H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
  intros Hrz Hrz16 Wab Cmag. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  pose proof (land_le_l' b1 243 ltac:(lia) ltac:(lia)) as Lb.
  stepn F_59eb4 D_59eb4.
  zcall (art_lsan_off_fn _ _ _ _ tp loff).
  zlbu F_59eb8 D_59eb8 (ab + rz - 16 + 1) Cb1.
  zstep F_59ebc D_59ebc. zstep F_59ec0 D_59ec0.
  stepn F_59ec4 D_59ec4. rwH. rewrite art_zb_andi by lia.
  stepn F_59ec8 D_59ec8. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_r.
  zstep F_59ecc D_59ecc.
  zsb F_59ed0 D_59ed0 (ab + rz - 16 + 1) (Z.land b1 243) ltac:(rewok Wh).
  stepfence F_59ed4 D_59ed4.
  zsb F_59ed8 D_59ed8 (ab + rz - 16) 2 ltac:(rewok Wh).
  zbft F_59edc D_59edc.
  zstep F_59ee0 D_59ee0.
  zbft F_59ee4 D_59ee4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmag' : cellA X 0x10388 8 0xcc6e96b9cc6e96b9) by (recell Cmag) end.
  zstep F_59ee8 D_59ee8. zld F_59eec D_59eec 0x10388 Cmag'.
  zsd F_59ef0 D_59ef0 (ab + 8) (ab + rz - 16) ltac:(rewok Wab).
  stepfence F_59ef4 D_59ef4.
  zsd F_59ef8 D_59ef8 ab 0xcc6e96b9cc6e96b9 ltac:(rewok Wab).
  zstep F_59efc D_59efc. zstep F_59f00 D_59f00.
  stepn F_59f04 D_59f04.
  zcall (art_run_malloc_hooks_fn _ _ _ _ sp).
  zstep F_59f08 D_59f08.
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
  zld F_59f0c D_59f0c (sp + 120) C120. rewrite Z_to_bv_bv_unsigned.
  zld F_59f10 D_59f10 (sp + 112) C112.
  zld F_59f14 D_59f14 (sp + 104) C104.
  zld F_59f18 D_59f18 (sp + 96) C96.
  zld F_59f1c D_59f1c (sp + 88) C88.
  zld F_59f20 D_59f20 (sp + 80) C80.
  zld F_59f24 D_59f24 (sp + 72) C72.
  zld F_59f28 D_59f28 (sp + 64) C64.
  zld F_59f2c D_59f2c (sp + 56) C56.
  zld F_59f30 D_59f30 (sp + 48) C48.
  zld F_59f34 D_59f34 (sp + 40) C40.
  zld F_59f38 D_59f38 (sp + 32) C32.
  zld F_59f3c D_59f3c (sp + 24) C24.
  zstep F_59f40 D_59f40.
  stepret F_59f44 D_59f44 raw0 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
