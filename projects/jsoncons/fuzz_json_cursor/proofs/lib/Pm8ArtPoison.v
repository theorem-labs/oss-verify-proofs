(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import muslA.Pm8SumsMemset_code muslA.Pm8SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_81000_82000 Pm8_code_82000_83000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition SB : Z := 0x7fff8000.
Definition kHighMemEnd : Z := 0x7fffffffffff.
Definition kHighMemBeg : Z := 0x10007fff8000.

Definition art_layout (M : word -> option byte) : Prop :=
  cellA M 0x153138 8 0x15c9b8 /\ cellA M 0x15c9b8 8 SB
  /\ cellA M 0x153140 8 0x15d6a8 /\ cellA M 0x15d6a8 8 0
  /\ cellA M 0x153148 8 0x15d6b0 /\ cellA M 0x15d6b0 8 0
  /\ cellA M 0x153150 8 0x15d6a0 /\ cellA M 0x15d6a0 8 kHighMemEnd
  /\ cellA M 0x153130 8 0x15a1b8 /\ cellA M (0x15a1b8 + 78) 1 1
  /\ cellA M 0x153158 8 0x155160 /\ cellA M 0x155160 8 0x145308
  /\ cellA M 0x153128 8 0x1ee4e8 /\ cellA M (0x1ee4e8 + 120) 8 18446744073709551615
  /\ cellA M 0x15c21c 1 1.

Lemma art_layout_Wn : forall n M a v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  apart a (Z.of_nat n) 0x153040 0xe000 -> apart a (Z.of_nat n) 0x1ee4e8 256 ->
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
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x153040 0xe000 -> apart (sp - 64) 64 0x1ee4e8 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 8 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 65536) ->
  msteps ASEGS (mkst regs (0x81d18 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 (SB + kHighMemEnd / 8))) 6 (Z_to_bv 64 0x145308)) 7 (Z_to_bv 64 kHighMemEnd)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (SB + p / 8))) 11 (Z_to_bv 64 v)) 12 (Z_to_bv 64 (n / 8))) 13 (Z_to_bv 64 (p / 8))) 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 (kHighMemEnd / 8))) 16 (Z_to_bv 64 (2 ^ 64 - 1))) 17 (Z_to_bv 64 0)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21)) 28 (Z_to_bv 64 kHighMemEnd))
       (0x145308 : word)
       (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom).
Proof.
  intros regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn Hv Hthr.
  unfold kHighMemBeg, kHighMemEnd in *.
  zstep F_81cc8 D_81cc8.
  zsd F_81ccc D_81ccc (sp - 8) (U raw) ltac:(rewok W).
  zsd F_81cd0 D_81cd0 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_81cd4 D_81cd4 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_81cd8 D_81cd8 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_81cdc D_81cdc (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_81ce0 D_81ce0 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_81ce4 D_81ce4 (sp - 56) (U (getr regs 21)) ltac:(rewok W).
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

  - zbtk F_81ce8 D_81ce8.
    stepn F_81cfc D_81cfc. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_81d00 D_81d00.
  zstep F_81d04 D_81d04.
  zld F_81d08 D_81d08 0x153138 G48.
  zld F_81d0c D_81d0c 0x15c9b8 Csb. unfold SB in *.
  zstep F_81d10 D_81d10. zstep F_81d14 D_81d14. zstep F_81d18 D_81d18.
  zstep F_81d1c D_81d1c.
  zbft F_81d20 D_81d20.
  zstep F_81d24 D_81d24. zld F_81d28 D_81d28 0x153140 G50.
  zstep F_81d2c D_81d2c. zld F_81d30 D_81d30 0x153148 G58.
  zld F_81d34 D_81d34 0x15d6a8 Cmb. zld F_81d38 D_81d38 0x15d6b0 Cme.
  zstep F_81d3c D_81d3c.
  zbtk F_81d40 D_81d40.
  zstep F_81d48 D_81d48. zld F_81d4c D_81d4c 0x153150 G60. zld F_81d50 D_81d50 0x15d6a0 Che.
  zstep F_81d54 D_81d54.
  zstep F_81d58 D_81d58.
  zbft F_81d5c D_81d5c.
  zbtk F_81d60 D_81d60.
  zld F_81e28 D_81e28 0x15d6a0 Che.
  zstep F_81e2c D_81e2c.
  zstep F_81e30 D_81e30.
  zbft F_81e34 D_81e34.
  zbtk F_81e38 D_81e38.
  stepn F_81ef8 D_81ef8. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_81efc D_81efc.
  zstep F_81f00 D_81f00. zstep F_81f04 D_81f04.
  zbft F_81f08 D_81f08.
  zstep F_81f0c D_81f0c. zld F_81f10 D_81f10 0x153140 G50.
  zstep F_81f14 D_81f14. zld F_81f18 D_81f18 0x153148 G58.
  zld F_81f1c D_81f1c 0x15d6a8 Cmb. zld F_81f20 D_81f20 0x15d6b0 Cme.
  zstep F_81f24 D_81f24.
  zbtk F_81f28 D_81f28.
  zstep F_81f30 D_81f30. zld F_81f34 D_81f34 0x153150 G60. zld F_81f38 D_81f38 0x15d6a0 Che.
  zstep F_81f3c D_81f3c.
  zstep F_81f40 D_81f40.
  zbft F_81f44 D_81f44.
  zbft F_81f48 D_81f48.
  zstep F_81f4c D_81f4c. zld F_81f50 D_81f50 0x153158 G68. zld F_81f54 D_81f54 0x155160 Crm.
  zbft F_81f58 D_81f58.
  stepn F_81f5c D_81f5c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_81f60 D_81f60. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_81f64 D_81f64. zstep F_81f68 D_81f68. zstep F_81f6c D_81f6c.
    zbft F_81f70 D_81f70.
    zstep F_81f74 D_81f74. zld F_81f78 D_81f78 0x153128 G38. zld F_81f7c D_81f7c (0x1ee4e8 + 120) Cth.
    zbtk F_81f80 D_81f80.
    zstep F_82030 D_82030. stepn F_82034 D_82034.
  zstep F_82040 D_82040.
  zld F_82044 D_82044 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_82048 D_82048 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_8204c D_8204c (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_82050 D_82050 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_82054 D_82054 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_82058 D_82058 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_8205c D_8205c (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_82060 D_82060.
  stepjr F_82064 D_82064 (0x145308 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. subst v. zret.

  - zbft F_81ce8 D_81ce8.
    zstep F_81cec D_81cec.
    zlb F_81cf0 D_81cf0 0x15c21c Ccp.
    stepfence F_81cf4 D_81cf4.
    zbft F_81cf8 D_81cf8.
    stepn F_81cfc D_81cfc. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_81d00 D_81d00.
  zstep F_81d04 D_81d04.
  zld F_81d08 D_81d08 0x153138 G48.
  zld F_81d0c D_81d0c 0x15c9b8 Csb. unfold SB in *.
  zstep F_81d10 D_81d10. zstep F_81d14 D_81d14. zstep F_81d18 D_81d18.
  zstep F_81d1c D_81d1c.
  zbft F_81d20 D_81d20.
  zstep F_81d24 D_81d24. zld F_81d28 D_81d28 0x153140 G50.
  zstep F_81d2c D_81d2c. zld F_81d30 D_81d30 0x153148 G58.
  zld F_81d34 D_81d34 0x15d6a8 Cmb. zld F_81d38 D_81d38 0x15d6b0 Cme.
  zstep F_81d3c D_81d3c.
  zbtk F_81d40 D_81d40.
  zstep F_81d48 D_81d48. zld F_81d4c D_81d4c 0x153150 G60. zld F_81d50 D_81d50 0x15d6a0 Che.
  zstep F_81d54 D_81d54.
  zstep F_81d58 D_81d58.
  zbft F_81d5c D_81d5c.
  zbtk F_81d60 D_81d60.
  zld F_81e28 D_81e28 0x15d6a0 Che.
  zstep F_81e2c D_81e2c.
  zstep F_81e30 D_81e30.
  zbft F_81e34 D_81e34.
  zbtk F_81e38 D_81e38.
  stepn F_81ef8 D_81ef8. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_81efc D_81efc.
  zstep F_81f00 D_81f00. zstep F_81f04 D_81f04.
  zbft F_81f08 D_81f08.
  zstep F_81f0c D_81f0c. zld F_81f10 D_81f10 0x153140 G50.
  zstep F_81f14 D_81f14. zld F_81f18 D_81f18 0x153148 G58.
  zld F_81f1c D_81f1c 0x15d6a8 Cmb. zld F_81f20 D_81f20 0x15d6b0 Cme.
  zstep F_81f24 D_81f24.
  zbtk F_81f28 D_81f28.
  zstep F_81f30 D_81f30. zld F_81f34 D_81f34 0x153150 G60. zld F_81f38 D_81f38 0x15d6a0 Che.
  zstep F_81f3c D_81f3c.
  zstep F_81f40 D_81f40.
  zbft F_81f44 D_81f44.
  zbft F_81f48 D_81f48.
  zstep F_81f4c D_81f4c. zld F_81f50 D_81f50 0x153158 G68. zld F_81f54 D_81f54 0x155160 Crm.
  zbft F_81f58 D_81f58.
  stepn F_81f5c D_81f5c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_81f60 D_81f60. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_81f64 D_81f64. zstep F_81f68 D_81f68. zstep F_81f6c D_81f6c.
    zbtk F_81f70 D_81f70.
    zstep F_82030 D_82030. stepn F_82034 D_82034.
  zstep F_82040 D_82040.
  zld F_82044 D_82044 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_82048 D_82048 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_8204c D_8204c (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_82050 D_82050 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_82054 D_82054 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_82058 D_82058 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_8205c D_8205c (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_82060 D_82060.
  stepjr F_82064 D_82064 (0x145308 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. zret.
Qed.

End FPX.
