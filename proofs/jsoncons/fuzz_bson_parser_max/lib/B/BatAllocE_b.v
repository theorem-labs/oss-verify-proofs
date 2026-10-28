(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r3cf10_3de98_b Ba0_code_r6de28_6df9c_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
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

#[using="Type"] Lemma art_run_malloc_hooks_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 32 <= sp -> sp < 2 ^ 64 -> 0x696000 + 32 <= sp ->
  wrA M (sp - 32) 32 -> cellA M 0x1d1700 8 0 ->
  msteps ASEGS (mkst regs (0x880b8 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 0x1d10d8)) 12 (Z_to_bv 64 0)) 18 (getr regs 18)) raw (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Ch.
  zstep F_87ca0 D_87ca0.
  zsd F_87ca4 D_87ca4 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_87ca8 D_87ca8 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_87cac D_87cac (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_87cb0 D_87cb0 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_87cb4 D_87cb4. zstep F_87cb8 D_87cb8.
  stepn F_87cbc D_87cbc.
  stepjr F_87d58 D_87d58 (0x880d8 : bv 64)%bv ltac:(gres; bveq).
  zstep F_87cc0 D_87cc0. zstep F_87cc4 D_87cc4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ch' : cellA X 0x1d1700 8 0) by (recell Ch);
    assert (Cra : cellA X (sp - 8) 8 (U raw)) by (do 3 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
    assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by (do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
    assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by (do 1 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
    assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by (apply cell_Wn_hit; lia) end.
  zld F_87cc8 D_87cc8 0x1d1700 Ch'.
  zbtk F_87ccc D_87ccc.
  zld F_87d40 D_87d40 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_87d44 D_87d44 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_87d48 D_87d48 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_87d4c D_87d4c (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zstep F_87d50 D_87d50.
  stepret F_87d54 D_87d54 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_alloc_e16_fn : forall regs (M rom : word -> option byte) (raw0 : word) (sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x696000 + 32 <= sp -> kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 1 <= n < 2 ^ 40 ->
  0 <= b1 < 256 -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= loff -> tp + loff + 4 < 2 ^ 64 -> ret_ok raw0 ->
  cellA M 0x138120 8 loff -> cellA M (tp + loff) 4 0 -> apart (tp + loff) 4 (ab + rz - 16) 16 ->
  cellA M (ab + rz - 16 + 1) 1 b1 -> wrA M (ab + rz - 16) 16 -> wrA M (sp - 32) 32 -> art_layout M -> cellA M 0x1d1700 8 0 ->
  apart (ab + rz - 16) 16 (sp - 32) 160 -> apart ab 16 (sp - 32) 160 ->
  cellA M (sp + 120) 8 (U raw0) -> cellA M (sp + 112) 8 s0v -> cellA M (sp + 104) 8 s1v -> cellA M (sp + 96) 8 s2v -> cellA M (sp + 88) 8 s3v -> cellA M (sp + 80) 8 s4v -> cellA M (sp + 72) 8 s5v -> cellA M (sp + 64) 8 s6v -> cellA M (sp + 56) 8 s7v -> cellA M (sp + 48) 8 s8v -> cellA M (sp + 40) 8 s9v -> cellA M (sp + 32) 8 s10v -> cellA M (sp + 24) 8 s11v ->
  rz = 16 ->
  msteps ASEGS (mkst regs (0x52cc4 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 (sp + 128))) 8 (Z_to_bv 64 s0v)) 9 (Z_to_bv 64 s1v)) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 0)) 18 (Z_to_bv 64 s2v)) 19 (Z_to_bv 64 s3v)) 20 (Z_to_bv 64 s4v)) 21 (Z_to_bv 64 s5v)) 22 (Z_to_bv 64 s6v)) 23 (Z_to_bv 64 s7v)) 24 (Z_to_bv 64 s8v)) 25 (Z_to_bv 64 s9v)) 26 (Z_to_bv 64 s10v)) 27 (Z_to_bv 64 s11v)) raw0 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 1 M (ab + rz - 15) (Z.land b1 243)) (ab + rz - 16) 2) (sp - 8) 0x52d18) (sp - 16) 1) (sp - 24) n) (sp - 32) ab) rom).
Proof.
  intros regs M rom raw0 sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v H2 H4 H8 H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
  intros Hrz. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  pose proof (land_le_l' b1 243 ltac:(lia) ltac:(lia)) as Lb.
  stepn F_528ac D_528ac.
  zcall (art_lsan_off_fn _ _ _ _ tp loff).
  zlbu F_528b0 D_528b0 (ab + rz - 16 + 1) Cb1.
  zstep F_528b4 D_528b4. zstep F_528b8 D_528b8.
  stepn F_528bc D_528bc. rwH. rewrite art_zb_andi by lia.
  stepn F_528c0 D_528c0. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_r.
  zstep F_528c4 D_528c4.
  zsb F_528c8 D_528c8 (ab + rz - 16 + 1) (Z.land b1 243) ltac:(rewok Wh).
  stepfence F_528cc D_528cc.
  zsb F_528d0 D_528d0 (ab + rz - 16) 2 ltac:(rewok Wh).
  zbtk F_528d4 D_528d4.
  zstep F_528f4 D_528f4. zstep F_528f8 D_528f8.
  stepn F_528fc D_528fc.
  zcall (art_run_malloc_hooks_fn _ _ _ _ sp).
  zstep F_52900 D_52900.
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
  zld F_52904 D_52904 (sp + 120) C120. rewrite Z_to_bv_bv_unsigned.
  zld F_52908 D_52908 (sp + 112) C112.
  zld F_5290c D_5290c (sp + 104) C104.
  zld F_52910 D_52910 (sp + 96) C96.
  zld F_52914 D_52914 (sp + 88) C88.
  zld F_52918 D_52918 (sp + 80) C80.
  zld F_5291c D_5291c (sp + 72) C72.
  zld F_52920 D_52920 (sp + 64) C64.
  zld F_52924 D_52924 (sp + 56) C56.
  zld F_52928 D_52928 (sp + 48) C48.
  zld F_5292c D_5292c (sp + 40) C40.
  zld F_52930 D_52930 (sp + 32) C32.
  zld F_52934 D_52934 (sp + 24) C24.
  zstep F_52938 D_52938.
  stepret F_5293c D_5293c raw0 ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_alloc_e32_fn : forall regs (M rom : word -> option byte) (raw0 : word) (sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x696000 + 32 <= sp -> kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 1 <= n < 2 ^ 40 ->
  0 <= b1 < 256 -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= loff -> tp + loff + 4 < 2 ^ 64 -> ret_ok raw0 ->
  cellA M 0x138120 8 loff -> cellA M (tp + loff) 4 0 -> apart (tp + loff) 4 (ab + rz - 16) 16 ->
  cellA M (ab + rz - 16 + 1) 1 b1 -> wrA M (ab + rz - 16) 16 -> wrA M (sp - 32) 32 -> art_layout M -> cellA M 0x1d1700 8 0 ->
  apart (ab + rz - 16) 16 (sp - 32) 160 -> apart ab 16 (sp - 32) 160 ->
  cellA M (sp + 120) 8 (U raw0) -> cellA M (sp + 112) 8 s0v -> cellA M (sp + 104) 8 s1v -> cellA M (sp + 96) 8 s2v -> cellA M (sp + 88) 8 s3v -> cellA M (sp + 80) 8 s4v -> cellA M (sp + 72) 8 s5v -> cellA M (sp + 64) 8 s6v -> cellA M (sp + 56) 8 s7v -> cellA M (sp + 48) 8 s8v -> cellA M (sp + 40) 8 s9v -> cellA M (sp + 32) 8 s10v -> cellA M (sp + 24) 8 s11v ->
  32 <= rz <= 2048 -> rz mod 16 = 0 -> wrA M ab 16 -> cellA M 0x10360 8 0xcc6e96b9cc6e96b9 ->
  msteps ASEGS (mkst regs (0x52cc4 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 (sp + 128))) 8 (Z_to_bv 64 s0v)) 9 (Z_to_bv 64 s1v)) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (ab + 16))) 18 (Z_to_bv 64 s2v)) 19 (Z_to_bv 64 s3v)) 20 (Z_to_bv 64 s4v)) 21 (Z_to_bv 64 s5v)) 22 (Z_to_bv 64 s6v)) 23 (Z_to_bv 64 s7v)) 24 (Z_to_bv 64 s8v)) 25 (Z_to_bv 64 s9v)) 26 (Z_to_bv 64 s10v)) 27 (Z_to_bv 64 s11v)) raw0 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 1 M (ab + rz - 15) (Z.land b1 243)) (ab + rz - 16) 2) (ab + 8) (ab + rz - 16)) ab 0xcc6e96b9cc6e96b9) (sp - 8) 0x52d18) (sp - 16) 1) (sp - 24) n) (sp - 32) ab) rom).
Proof.
  intros regs M rom raw0 sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v H2 H4 H8 H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
  intros Hrz Hrz16 Wab Cmag. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  pose proof (land_le_l' b1 243 ltac:(lia) ltac:(lia)) as Lb.
  stepn F_528ac D_528ac.
  zcall (art_lsan_off_fn _ _ _ _ tp loff).
  zlbu F_528b0 D_528b0 (ab + rz - 16 + 1) Cb1.
  zstep F_528b4 D_528b4. zstep F_528b8 D_528b8.
  stepn F_528bc D_528bc. rwH. rewrite art_zb_andi by lia.
  stepn F_528c0 D_528c0. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_r.
  zstep F_528c4 D_528c4.
  zsb F_528c8 D_528c8 (ab + rz - 16 + 1) (Z.land b1 243) ltac:(rewok Wh).
  stepfence F_528cc D_528cc.
  zsb F_528d0 D_528d0 (ab + rz - 16) 2 ltac:(rewok Wh).
  zbft F_528d4 D_528d4.
  zstep F_528d8 D_528d8.
  zbft F_528dc D_528dc.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmag' : cellA X 0x10360 8 0xcc6e96b9cc6e96b9) by (recell Cmag) end.
  zstep F_528e0 D_528e0. zld F_528e4 D_528e4 0x10360 Cmag'.
  zsd F_528e8 D_528e8 (ab + 8) (ab + rz - 16) ltac:(rewok Wab).
  stepfence F_528ec D_528ec.
  zsd F_528f0 D_528f0 ab 0xcc6e96b9cc6e96b9 ltac:(rewok Wab).
  zstep F_528f4 D_528f4. zstep F_528f8 D_528f8.
  stepn F_528fc D_528fc.
  zcall (art_run_malloc_hooks_fn _ _ _ _ sp).
  zstep F_52900 D_52900.
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
  zld F_52904 D_52904 (sp + 120) C120. rewrite Z_to_bv_bv_unsigned.
  zld F_52908 D_52908 (sp + 112) C112.
  zld F_5290c D_5290c (sp + 104) C104.
  zld F_52910 D_52910 (sp + 96) C96.
  zld F_52914 D_52914 (sp + 88) C88.
  zld F_52918 D_52918 (sp + 80) C80.
  zld F_5291c D_5291c (sp + 72) C72.
  zld F_52920 D_52920 (sp + 64) C64.
  zld F_52924 D_52924 (sp + 56) C56.
  zld F_52928 D_52928 (sp + 48) C48.
  zld F_5292c D_5292c (sp + 40) C40.
  zld F_52930 D_52930 (sp + 32) C32.
  zld F_52934 D_52934 (sp + 24) C24.
  zstep F_52938 D_52938.
  stepret F_5293c D_5293c raw0 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
