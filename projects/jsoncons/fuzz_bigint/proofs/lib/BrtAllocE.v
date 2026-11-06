(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac BrtLeaf BrtPoison.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_3d2b4_3e23c Bo0_code_6e238_6e3ac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma land_le_l' a m : 0 <= a -> 0 <= m -> 0 <= Z.land a m <= a.
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

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_run_malloc_hooks_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 32 <= sp -> sp < 2 ^ 64 -> 0x634000 + 32 <= sp ->
  wrA M (sp - 32) 32 -> cellA M 0x170200 8 0 ->
  msteps ASEGS (mkst regs (0x6e238 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 0x170258)) 12 (Z_to_bv 64 0)) 18 (getr regs 18)) raw (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Ch.
  zstep F_6e238 D_6e238.
  zsd F_6e23c D_6e23c (sp - 8) (U raw) ltac:(rewok W).
  zsd F_6e240 D_6e240 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_6e244 D_6e244 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_6e248 D_6e248 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_6e24c D_6e24c. zstep F_6e250 D_6e250.
  stepn F_6e254 D_6e254.
  stepjr F_6e2f0 D_6e2f0 (0x6e258 : bv 64)%bv ltac:(gres; bveq).
  zstep F_6e258 D_6e258. zstep F_6e25c D_6e25c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ch' : cellA X 0x170200 8 0) by (recell Ch);
    assert (Cra : cellA X (sp - 8) 8 (U raw)) by (do 3 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
    assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by (do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
    assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by (do 1 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
    assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by (apply cell_Wn_hit; lia) end.
  zld F_6e260 D_6e260 0x170200 Ch'.
  zbtk F_6e264 D_6e264.
  zld F_6e2d8 D_6e2d8 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_6e2dc D_6e2dc (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_6e2e0 D_6e2e0 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_6e2e4 D_6e2e4 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zstep F_6e2e8 D_6e2e8.
  stepret F_6e2ec D_6e2ec raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_alloc_e16_fn : forall regs (M rom : word -> option byte) (raw0 : word) (sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x634000 + 32 <= sp -> kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 1 <= n < 2 ^ 40 ->
  0 <= b1 < 256 -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= loff -> tp + loff + 4 < 2 ^ 64 -> ret_ok raw0 ->
  cellA M 0xd7120 8 loff -> cellA M (tp + loff) 4 0 -> apart (tp + loff) 4 (ab + rz - 16) 16 ->
  cellA M (ab + rz - 16 + 1) 1 b1 -> wrA M (ab + rz - 16) 16 -> wrA M (sp - 32) 32 -> art_layout M -> cellA M 0x170200 8 0 ->
  apart (ab + rz - 16) 16 (sp - 32) 160 -> apart ab 16 (sp - 32) 160 ->
  cellA M (sp + 120) 8 (U raw0) -> cellA M (sp + 112) 8 s0v -> cellA M (sp + 104) 8 s1v -> cellA M (sp + 96) 8 s2v -> cellA M (sp + 88) 8 s3v -> cellA M (sp + 80) 8 s4v -> cellA M (sp + 72) 8 s5v -> cellA M (sp + 64) 8 s6v -> cellA M (sp + 56) 8 s7v -> cellA M (sp + 48) 8 s8v -> cellA M (sp + 40) 8 s9v -> cellA M (sp + 32) 8 s10v -> cellA M (sp + 24) 8 s11v ->
  rz = 16 ->
  msteps ASEGS (mkst regs (0x3dcd0 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 (sp + 128))) 8 (Z_to_bv 64 s0v)) 9 (Z_to_bv 64 s1v)) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 0)) 18 (Z_to_bv 64 s2v)) 19 (Z_to_bv 64 s3v)) 20 (Z_to_bv 64 s4v)) 21 (Z_to_bv 64 s5v)) 22 (Z_to_bv 64 s6v)) 23 (Z_to_bv 64 s7v)) 24 (Z_to_bv 64 s8v)) 25 (Z_to_bv 64 s9v)) 26 (Z_to_bv 64 s10v)) 27 (Z_to_bv 64 s11v)) raw0 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 1 M (ab + rz - 15) (Z.land b1 243)) (ab + rz - 16) 2) (sp - 8) 0x3dd24) (sp - 16) 1) (sp - 24) n) (sp - 32) ab) rom).
Proof.
  intros regs M rom raw0 sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v H2 H4 H8 H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
  intros Hrz. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  pose proof (land_le_l' b1 243 ltac:(lia) ltac:(lia)) as Lb.
  stepn F_3dcd0 D_3dcd0.
  zcall (art_lsan_off_fn _ _ _ _ tp loff).
  zlbu F_3dcd4 D_3dcd4 (ab + rz - 16 + 1) Cb1.
  zstep F_3dcd8 D_3dcd8. zstep F_3dcdc D_3dcdc.
  stepn F_3dce0 D_3dce0. rwH. rewrite art_zb_andi by lia.
  stepn F_3dce4 D_3dce4. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_r.
  zstep F_3dce8 D_3dce8.
  zsb F_3dcec D_3dcec (ab + rz - 16 + 1) (Z.land b1 243) ltac:(rewok Wh).
  stepfence F_3dcf0 D_3dcf0.
  zsb F_3dcf4 D_3dcf4 (ab + rz - 16) 2 ltac:(rewok Wh).
  zbtk F_3dcf8 D_3dcf8.
  zstep F_3dd18 D_3dd18. zstep F_3dd1c D_3dd1c.
  stepn F_3dd20 D_3dd20.
  zcall (art_run_malloc_hooks_fn _ _ _ _ sp).
  zstep F_3dd24 D_3dd24.
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
  zld F_3dd28 D_3dd28 (sp + 120) C120. rewrite Z_to_bv_bv_unsigned.
  zld F_3dd2c D_3dd2c (sp + 112) C112.
  zld F_3dd30 D_3dd30 (sp + 104) C104.
  zld F_3dd34 D_3dd34 (sp + 96) C96.
  zld F_3dd38 D_3dd38 (sp + 88) C88.
  zld F_3dd3c D_3dd3c (sp + 80) C80.
  zld F_3dd40 D_3dd40 (sp + 72) C72.
  zld F_3dd44 D_3dd44 (sp + 64) C64.
  zld F_3dd48 D_3dd48 (sp + 56) C56.
  zld F_3dd4c D_3dd4c (sp + 48) C48.
  zld F_3dd50 D_3dd50 (sp + 40) C40.
  zld F_3dd54 D_3dd54 (sp + 32) C32.
  zld F_3dd58 D_3dd58 (sp + 24) C24.
  zstep F_3dd5c D_3dd5c.
  stepret F_3dd60 D_3dd60 raw0 ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_alloc_e32_fn : forall regs (M rom : word -> option byte) (raw0 : word) (sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x634000 + 32 <= sp -> kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 1 <= n < 2 ^ 40 ->
  0 <= b1 < 256 -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= loff -> tp + loff + 4 < 2 ^ 64 -> ret_ok raw0 ->
  cellA M 0xd7120 8 loff -> cellA M (tp + loff) 4 0 -> apart (tp + loff) 4 (ab + rz - 16) 16 ->
  cellA M (ab + rz - 16 + 1) 1 b1 -> wrA M (ab + rz - 16) 16 -> wrA M (sp - 32) 32 -> art_layout M -> cellA M 0x170200 8 0 ->
  apart (ab + rz - 16) 16 (sp - 32) 160 -> apart ab 16 (sp - 32) 160 ->
  cellA M (sp + 120) 8 (U raw0) -> cellA M (sp + 112) 8 s0v -> cellA M (sp + 104) 8 s1v -> cellA M (sp + 96) 8 s2v -> cellA M (sp + 88) 8 s3v -> cellA M (sp + 80) 8 s4v -> cellA M (sp + 72) 8 s5v -> cellA M (sp + 64) 8 s6v -> cellA M (sp + 56) 8 s7v -> cellA M (sp + 48) 8 s8v -> cellA M (sp + 40) 8 s9v -> cellA M (sp + 32) 8 s10v -> cellA M (sp + 24) 8 s11v ->
  32 <= rz <= 2048 -> rz mod 16 = 0 -> wrA M ab 16 -> cellA M 0x10340 8 0xcc6e96b9cc6e96b9 ->
  msteps ASEGS (mkst regs (0x3dcd0 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 (sp + 128))) 8 (Z_to_bv 64 s0v)) 9 (Z_to_bv 64 s1v)) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (ab + 16))) 18 (Z_to_bv 64 s2v)) 19 (Z_to_bv 64 s3v)) 20 (Z_to_bv 64 s4v)) 21 (Z_to_bv 64 s5v)) 22 (Z_to_bv 64 s6v)) 23 (Z_to_bv 64 s7v)) 24 (Z_to_bv 64 s8v)) 25 (Z_to_bv 64 s9v)) 26 (Z_to_bv 64 s10v)) 27 (Z_to_bv 64 s11v)) raw0 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 1 M (ab + rz - 15) (Z.land b1 243)) (ab + rz - 16) 2) (ab + 8) (ab + rz - 16)) ab 0xcc6e96b9cc6e96b9) (sp - 8) 0x3dd24) (sp - 16) 1) (sp - 24) n) (sp - 32) ab) rom).
Proof.
  intros regs M rom raw0 sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v H2 H4 H8 H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
  intros Hrz Hrz16 Wab Cmag. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  pose proof (land_le_l' b1 243 ltac:(lia) ltac:(lia)) as Lb.
  stepn F_3dcd0 D_3dcd0.
  zcall (art_lsan_off_fn _ _ _ _ tp loff).
  zlbu F_3dcd4 D_3dcd4 (ab + rz - 16 + 1) Cb1.
  zstep F_3dcd8 D_3dcd8. zstep F_3dcdc D_3dcdc.
  stepn F_3dce0 D_3dce0. rwH. rewrite art_zb_andi by lia.
  stepn F_3dce4 D_3dce4. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_r.
  zstep F_3dce8 D_3dce8.
  zsb F_3dcec D_3dcec (ab + rz - 16 + 1) (Z.land b1 243) ltac:(rewok Wh).
  stepfence F_3dcf0 D_3dcf0.
  zsb F_3dcf4 D_3dcf4 (ab + rz - 16) 2 ltac:(rewok Wh).
  zbft F_3dcf8 D_3dcf8.
  zstep F_3dcfc D_3dcfc.
  zbft F_3dd00 D_3dd00.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmag' : cellA X 0x10340 8 0xcc6e96b9cc6e96b9) by (recell Cmag) end.
  zstep F_3dd04 D_3dd04. zld F_3dd08 D_3dd08 0x10340 Cmag'.
  zsd F_3dd0c D_3dd0c (ab + 8) (ab + rz - 16) ltac:(rewok Wab).
  stepfence F_3dd10 D_3dd10.
  zsd F_3dd14 D_3dd14 ab 0xcc6e96b9cc6e96b9 ltac:(rewok Wab).
  zstep F_3dd18 D_3dd18. zstep F_3dd1c D_3dd1c.
  stepn F_3dd20 D_3dd20.
  zcall (art_run_malloc_hooks_fn _ _ _ _ sp).
  zstep F_3dd24 D_3dd24.
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
  zld F_3dd28 D_3dd28 (sp + 120) C120. rewrite Z_to_bv_bv_unsigned.
  zld F_3dd2c D_3dd2c (sp + 112) C112.
  zld F_3dd30 D_3dd30 (sp + 104) C104.
  zld F_3dd34 D_3dd34 (sp + 96) C96.
  zld F_3dd38 D_3dd38 (sp + 88) C88.
  zld F_3dd3c D_3dd3c (sp + 80) C80.
  zld F_3dd40 D_3dd40 (sp + 72) C72.
  zld F_3dd44 D_3dd44 (sp + 64) C64.
  zld F_3dd48 D_3dd48 (sp + 56) C56.
  zld F_3dd4c D_3dd4c (sp + 48) C48.
  zld F_3dd50 D_3dd50 (sp + 40) C40.
  zld F_3dd54 D_3dd54 (sp + 32) C32.
  zld F_3dd58 D_3dd58 (sp + 24) C24.
  zstep F_3dd5c D_3dd5c.
  stepret F_3dd60 D_3dd60 raw0 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
