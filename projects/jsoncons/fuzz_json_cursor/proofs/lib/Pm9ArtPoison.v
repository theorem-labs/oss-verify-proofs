(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import muslA.Pm9SumsMemset_code muslA.Pm9SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_82000_83000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition SB : Z := 0x7fff8000.
Definition kHighMemEnd : Z := 0x7fffffffffff.
Definition kHighMemBeg : Z := 0x10007fff8000.

Definition art_layout (M : word -> option byte) : Prop :=
  cellA M 0x154500 8 0x15dcf8 /\ cellA M 0x15dcf8 8 SB
  /\ cellA M 0x154508 8 0x15e9e8 /\ cellA M 0x15e9e8 8 0
  /\ cellA M 0x154510 8 0x15e9f0 /\ cellA M 0x15e9f0 8 0
  /\ cellA M 0x154518 8 0x15e9e0 /\ cellA M 0x15e9e0 8 kHighMemEnd
  /\ cellA M 0x1544f8 8 0x15b4f8 /\ cellA M (0x15b4f8 + 78) 1 1
  /\ cellA M 0x154520 8 0x156528 /\ cellA M 0x156528 8 0x1468c4
  /\ cellA M 0x1544f0 8 0x1ef828 /\ cellA M (0x1ef828 + 120) 8 18446744073709551615
  /\ cellA M 0x15d55c 1 1.

Lemma art_layout_Wn : forall n M a v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  apart a (Z.of_nat n) 0x154040 0xe000 -> apart a (Z.of_nat n) 0x1ef828 256 ->
  art_layout M -> art_layout (Wn n M a v).
Proof.
  intros n M a v Ha Hn A1 A2 L. unfold art_layout in *. unfold apart in *.
  repeat match goal with |- _ /\ _ => split end;
  match goal with |- cell _ _ ?b ?m _ => apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; cbn; lia| tauto] end.
Qed.

Definition art_poison_frame (M : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) ra) (sp - 16) s0) (sp - 24) s1) (sp - 32) s2) (sp - 40) s3) (sp - 48) s4) (sp - 56) s5.

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_poison_hi_fn : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x154040 0xe000 -> apart (sp - 64) 64 0x1ef828 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 8 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  msteps ASEGS (mkst regs (0x820d8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 (SB + kHighMemEnd / 8))) 6 (Z_to_bv 64 0x1468c4)) 7 (Z_to_bv 64 kHighMemEnd)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (SB + p / 8))) 11 (Z_to_bv 64 v)) 12 (Z_to_bv 64 (n / 8))) 13 (Z_to_bv 64 (p / 8))) 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 (kHighMemEnd / 8))) 16 (Z_to_bv 64 (2 ^ 64 - 1))) 17 (Z_to_bv 64 0)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21)) 28 (Z_to_bv 64 kHighMemEnd))
       (0x1468c4 : word)
       (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom).
Proof.
  intros regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn Hv Hthr.
  unfold kHighMemBeg, kHighMemEnd in *.
  zstep F_82090 D_82090.
  zsd F_82094 D_82094 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_82098 D_82098 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_8209c D_8209c (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_820a0 D_820a0 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_820a4 D_820a4 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_820a8 D_820a8 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_820ac D_820ac (sp - 56) (U (getr regs 21)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (L1 : art_layout Mf) by (unfold Mf; repeat (apply art_layout_Wn; [lia|lia|unfold apart in *; cbn; lia|unfold apart in *; cbn; lia|]); exact L).
  assert (Cra : cellA Mf (sp - 8) 8 (U raw)) by (unfold Mf; do 6 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs0 : cellA Mf (sp - 16) 8 (U (getr regs 8))) by (unfold Mf; do 5 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs1 : cellA Mf (sp - 24) 8 (U (getr regs 9))) by (unfold Mf; do 4 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs2 : cellA Mf (sp - 32) 8 (U (getr regs 18))) by (unfold Mf; do 3 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs3 : cellA Mf (sp - 40) 8 (U (getr regs 19))) by (unfold Mf; do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs4 : cellA Mf (sp - 48) 8 (U (getr regs 20))) by (unfold Mf; do 1 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
  assert (Cs5 : cellA Mf (sp - 56) 8 (U (getr regs 21))) by (unfold Mf; apply cell_Wn_hit; lia).
  destruct L1 as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  assert (Hp8' : p / 8 * 8 = p) by lia. assert (Hn8' : n / 8 * 8 = n) by lia.
  destruct (Z.eq_dec v 0) as [V0|V1].

  - zbtk F_820b0 D_820b0.
    stepn F_820c4 D_820c4. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_820c8 D_820c8.
  zstep F_820cc D_820cc.
  zld F_820d0 D_820d0 0x154500 G48.
  zld F_820d4 D_820d4 0x15dcf8 Csb. unfold SB in *.
  zstep F_820d8 D_820d8. zstep F_820dc D_820dc. zstep F_820e0 D_820e0.
  zstep F_820e4 D_820e4.
  zbft F_820e8 D_820e8.
  zstep F_820ec D_820ec. zld F_820f0 D_820f0 0x154508 G50.
  zstep F_820f4 D_820f4. zld F_820f8 D_820f8 0x154510 G58.
  zld F_820fc D_820fc 0x15e9e8 Cmb. zld F_82100 D_82100 0x15e9f0 Cme.
  zstep F_82104 D_82104.
  zbtk F_82108 D_82108.
  zstep F_82110 D_82110. zld F_82114 D_82114 0x154518 G60. zld F_82118 D_82118 0x15e9e0 Che.
  zstep F_8211c D_8211c.
  zstep F_82120 D_82120.
  zbft F_82124 D_82124.
  zbtk F_82128 D_82128.
  zld F_821f0 D_821f0 0x15e9e0 Che.
  zstep F_821f4 D_821f4.
  zstep F_821f8 D_821f8.
  zbft F_821fc D_821fc.
  zbtk F_82200 D_82200.
  stepn F_822c0 D_822c0. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_822c4 D_822c4.
  zstep F_822c8 D_822c8. zstep F_822cc D_822cc.
  zbft F_822d0 D_822d0.
  zstep F_822d4 D_822d4. zld F_822d8 D_822d8 0x154508 G50.
  zstep F_822dc D_822dc. zld F_822e0 D_822e0 0x154510 G58.
  zld F_822e4 D_822e4 0x15e9e8 Cmb. zld F_822e8 D_822e8 0x15e9f0 Cme.
  zstep F_822ec D_822ec.
  zbtk F_822f0 D_822f0.
  zstep F_822f8 D_822f8. zld F_822fc D_822fc 0x154518 G60. zld F_82300 D_82300 0x15e9e0 Che.
  zstep F_82304 D_82304.
  zstep F_82308 D_82308.
  zbft F_8230c D_8230c.
  zbft F_82310 D_82310.
  zstep F_82314 D_82314. zld F_82318 D_82318 0x154520 G68. zld F_8231c D_8231c 0x156528 Crm.
  zbft F_82320 D_82320.
  stepn F_82324 D_82324. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_82328 D_82328. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_8232c D_8232c. zstep F_82330 D_82330. zstep F_82334 D_82334.
    zbft F_82338 D_82338.
    zstep F_8233c D_8233c. zld F_82340 D_82340 0x1544f0 G38. zld F_82344 D_82344 (0x1ef828 + 120) Cth.
    zbtk F_82348 D_82348.
    zstep F_823f8 D_823f8. stepn F_823fc D_823fc.
  zstep F_82408 D_82408.
  zld F_8240c D_8240c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_82410 D_82410 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_82414 D_82414 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_82418 D_82418 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_8241c D_8241c (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_82420 D_82420 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_82424 D_82424 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_82428 D_82428.
  stepjr F_8242c D_8242c (0x1468c4 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. subst v. zret.

  - zbft F_820b0 D_820b0.
    zstep F_820b4 D_820b4.
    zlb F_820b8 D_820b8 0x15d55c Ccp.
    stepfence F_820bc D_820bc.
    zbft F_820c0 D_820c0.
    stepn F_820c4 D_820c4. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_820c8 D_820c8.
  zstep F_820cc D_820cc.
  zld F_820d0 D_820d0 0x154500 G48.
  zld F_820d4 D_820d4 0x15dcf8 Csb. unfold SB in *.
  zstep F_820d8 D_820d8. zstep F_820dc D_820dc. zstep F_820e0 D_820e0.
  zstep F_820e4 D_820e4.
  zbft F_820e8 D_820e8.
  zstep F_820ec D_820ec. zld F_820f0 D_820f0 0x154508 G50.
  zstep F_820f4 D_820f4. zld F_820f8 D_820f8 0x154510 G58.
  zld F_820fc D_820fc 0x15e9e8 Cmb. zld F_82100 D_82100 0x15e9f0 Cme.
  zstep F_82104 D_82104.
  zbtk F_82108 D_82108.
  zstep F_82110 D_82110. zld F_82114 D_82114 0x154518 G60. zld F_82118 D_82118 0x15e9e0 Che.
  zstep F_8211c D_8211c.
  zstep F_82120 D_82120.
  zbft F_82124 D_82124.
  zbtk F_82128 D_82128.
  zld F_821f0 D_821f0 0x15e9e0 Che.
  zstep F_821f4 D_821f4.
  zstep F_821f8 D_821f8.
  zbft F_821fc D_821fc.
  zbtk F_82200 D_82200.
  stepn F_822c0 D_822c0. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_822c4 D_822c4.
  zstep F_822c8 D_822c8. zstep F_822cc D_822cc.
  zbft F_822d0 D_822d0.
  zstep F_822d4 D_822d4. zld F_822d8 D_822d8 0x154508 G50.
  zstep F_822dc D_822dc. zld F_822e0 D_822e0 0x154510 G58.
  zld F_822e4 D_822e4 0x15e9e8 Cmb. zld F_822e8 D_822e8 0x15e9f0 Cme.
  zstep F_822ec D_822ec.
  zbtk F_822f0 D_822f0.
  zstep F_822f8 D_822f8. zld F_822fc D_822fc 0x154518 G60. zld F_82300 D_82300 0x15e9e0 Che.
  zstep F_82304 D_82304.
  zstep F_82308 D_82308.
  zbft F_8230c D_8230c.
  zbft F_82310 D_82310.
  zstep F_82314 D_82314. zld F_82318 D_82318 0x154520 G68. zld F_8231c D_8231c 0x156528 Crm.
  zbft F_82320 D_82320.
  stepn F_82324 D_82324. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_82328 D_82328. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_8232c D_8232c. zstep F_82330 D_82330. zstep F_82334 D_82334.
    zbtk F_82338 D_82338.
    zstep F_823f8 D_823f8. stepn F_823fc D_823fc.
  zstep F_82408 D_82408.
  zld F_8240c D_8240c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_82410 D_82410 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_82414 D_82414 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_82418 D_82418 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_8241c D_8241c (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_82420 D_82420 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_82424 D_82424 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_82428 D_82428.
  stepjr F_8242c D_8242c (0x1468c4 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. zret.
Qed.

End FPX.
