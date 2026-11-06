(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import muslA.Ea0SumsMemset_code.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import muslA.Ea0SumsMemsetS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r60dd4_61420.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EatPoison EatPoisonRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_poison3_hi0_fn : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x1383c0 0xc000 -> apart (sp - 64) 64 0x1d3528 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> kHighMemBeg + 8 <= p + n -> p <= kHighMemEnd -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 2 ^ 61) ->
  msteps ASEGS (mkst regs (0x7b4bc : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 (SB + kHighMemEnd / 8))) 6 (Z_to_bv 64 0x12b88c)) 7 (Z_to_bv 64 kHighMemEnd)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (SB + p / 8))) 11 (Z_to_bv 64 v)) 12 (Z_to_bv 64 (n / 8))) 13 (Z_to_bv 64 (p / 8))) 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 (kHighMemEnd / 8))) 16 (Z_to_bv 64 (2 ^ 64 - 1))) 17 (Z_to_bv 64 0)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21)) 28 (Z_to_bv 64 kHighMemEnd))
       (0x12b88c : word)
       (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom).
Proof.
  intros regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr.
  unfold kHighMemBeg, kHighMemEnd in *.
  zstep F_7b46c D_7b46c.
  zsd F_7b470 D_7b470 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_7b474 D_7b474 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_7b478 D_7b478 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_7b47c D_7b47c (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_7b480 D_7b480 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_7b484 D_7b484 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_7b488 D_7b488 (sp - 56) (U (getr regs 21)) ltac:(rewok W).
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

  - zbtk F_7b48c D_7b48c.
    stepn F_7b4a0 D_7b4a0. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7b4a4 D_7b4a4.
  zstep F_7b4a8 D_7b4a8.
  zld F_7b4ac D_7b4ac 0x1391b8 G48.
  zld F_7b4b0 D_7b4b0 0x1419f8 Csb. unfold SB in *.
  zstep F_7b4b4 D_7b4b4. zstep F_7b4b8 D_7b4b8. zstep F_7b4bc D_7b4bc.
  zstep F_7b4c0 D_7b4c0.
  zbft F_7b4c4 D_7b4c4.
  zstep F_7b4c8 D_7b4c8. zld F_7b4cc D_7b4cc 0x1391c0 G50.
  zstep F_7b4d0 D_7b4d0. zld F_7b4d4 D_7b4d4 0x1391c8 G58.
  zld F_7b4d8 D_7b4d8 0x1426e8 Cmb. zld F_7b4dc D_7b4dc 0x1426f0 Cme.
  zstep F_7b4e0 D_7b4e0.
  zbtk F_7b4e4 D_7b4e4.
  zstep F_7b4ec D_7b4ec. zld F_7b4f0 D_7b4f0 0x1391d0 G60. zld F_7b4f4 D_7b4f4 0x1426e0 Che.
  zstep F_7b4f8 D_7b4f8.
  zstep F_7b4fc D_7b4fc.
  zbft F_7b500 D_7b500.
  zbtk F_7b504 D_7b504.
  zld F_7b5cc D_7b5cc 0x1426e0 Che.
  zstep F_7b5d0 D_7b5d0.
  zstep F_7b5d4 D_7b5d4.
  zbft F_7b5d8 D_7b5d8.
  zbtk F_7b5dc D_7b5dc.
  stepn F_7b69c D_7b69c. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7b6a0 D_7b6a0.
  zstep F_7b6a4 D_7b6a4. zstep F_7b6a8 D_7b6a8.
  zbft F_7b6ac D_7b6ac.
  zstep F_7b6b0 D_7b6b0. zld F_7b6b4 D_7b6b4 0x1391c0 G50.
  zstep F_7b6b8 D_7b6b8. zld F_7b6bc D_7b6bc 0x1391c8 G58.
  zld F_7b6c0 D_7b6c0 0x1426e8 Cmb. zld F_7b6c4 D_7b6c4 0x1426f0 Cme.
  zstep F_7b6c8 D_7b6c8.
  zbtk F_7b6cc D_7b6cc.
  zstep F_7b6d4 D_7b6d4. zld F_7b6d8 D_7b6d8 0x1391d0 G60. zld F_7b6dc D_7b6dc 0x1426e0 Che.
  zstep F_7b6e0 D_7b6e0.
  zstep F_7b6e4 D_7b6e4.
  zbft F_7b6e8 D_7b6e8.
  zbft F_7b6ec D_7b6ec.
  zstep F_7b6f0 D_7b6f0. zld F_7b6f4 D_7b6f4 0x1391d8 G68. zld F_7b6f8 D_7b6f8 0x13b1c8 Crm.
  zbft F_7b6fc D_7b6fc.
  stepn F_7b700 D_7b700. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_7b704 D_7b704. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_7b708 D_7b708. zstep F_7b70c D_7b70c. zstep F_7b710 D_7b710.
    zbft F_7b714 D_7b714.
    zstep F_7b718 D_7b718. zld F_7b71c D_7b71c 0x1391a8 G38. zld F_7b720 D_7b720 (0x1d3528 + 120) Cth.
    zbtk F_7b724 D_7b724.
    zstep F_7b7d4 D_7b7d4. stepn F_7b7d8 D_7b7d8.
  zstep F_7b7e4 D_7b7e4.
  zld F_7b7e8 D_7b7e8 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7ec D_7b7ec (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7f0 D_7b7f0 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7f4 D_7b7f4 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7f8 D_7b7f8 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7fc D_7b7fc (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_7b800 D_7b800 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_7b804 D_7b804.
  stepjr F_7b808 D_7b808 (0x12b88c : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. subst v. zret.

  - zbft F_7b48c D_7b48c.
    zstep F_7b490 D_7b490.
    zlb F_7b494 D_7b494 0x14125c Ccp.
    stepfence F_7b498 D_7b498.
    zbft F_7b49c D_7b49c.
    stepn F_7b4a0 D_7b4a0. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7b4a4 D_7b4a4.
  zstep F_7b4a8 D_7b4a8.
  zld F_7b4ac D_7b4ac 0x1391b8 G48.
  zld F_7b4b0 D_7b4b0 0x1419f8 Csb. unfold SB in *.
  zstep F_7b4b4 D_7b4b4. zstep F_7b4b8 D_7b4b8. zstep F_7b4bc D_7b4bc.
  zstep F_7b4c0 D_7b4c0.
  zbft F_7b4c4 D_7b4c4.
  zstep F_7b4c8 D_7b4c8. zld F_7b4cc D_7b4cc 0x1391c0 G50.
  zstep F_7b4d0 D_7b4d0. zld F_7b4d4 D_7b4d4 0x1391c8 G58.
  zld F_7b4d8 D_7b4d8 0x1426e8 Cmb. zld F_7b4dc D_7b4dc 0x1426f0 Cme.
  zstep F_7b4e0 D_7b4e0.
  zbtk F_7b4e4 D_7b4e4.
  zstep F_7b4ec D_7b4ec. zld F_7b4f0 D_7b4f0 0x1391d0 G60. zld F_7b4f4 D_7b4f4 0x1426e0 Che.
  zstep F_7b4f8 D_7b4f8.
  zstep F_7b4fc D_7b4fc.
  zbft F_7b500 D_7b500.
  zbtk F_7b504 D_7b504.
  zld F_7b5cc D_7b5cc 0x1426e0 Che.
  zstep F_7b5d0 D_7b5d0.
  zstep F_7b5d4 D_7b5d4.
  zbft F_7b5d8 D_7b5d8.
  zbtk F_7b5dc D_7b5dc.
  stepn F_7b69c D_7b69c. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7b6a0 D_7b6a0.
  zstep F_7b6a4 D_7b6a4. zstep F_7b6a8 D_7b6a8.
  zbft F_7b6ac D_7b6ac.
  zstep F_7b6b0 D_7b6b0. zld F_7b6b4 D_7b6b4 0x1391c0 G50.
  zstep F_7b6b8 D_7b6b8. zld F_7b6bc D_7b6bc 0x1391c8 G58.
  zld F_7b6c0 D_7b6c0 0x1426e8 Cmb. zld F_7b6c4 D_7b6c4 0x1426f0 Cme.
  zstep F_7b6c8 D_7b6c8.
  zbtk F_7b6cc D_7b6cc.
  zstep F_7b6d4 D_7b6d4. zld F_7b6d8 D_7b6d8 0x1391d0 G60. zld F_7b6dc D_7b6dc 0x1426e0 Che.
  zstep F_7b6e0 D_7b6e0.
  zstep F_7b6e4 D_7b6e4.
  zbft F_7b6e8 D_7b6e8.
  zbft F_7b6ec D_7b6ec.
  zstep F_7b6f0 D_7b6f0. zld F_7b6f4 D_7b6f4 0x1391d8 G68. zld F_7b6f8 D_7b6f8 0x13b1c8 Crm.
  zbft F_7b6fc D_7b6fc.
  stepn F_7b700 D_7b700. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_7b704 D_7b704. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_7b708 D_7b708. zstep F_7b70c D_7b70c. zstep F_7b710 D_7b710.
    zbtk F_7b714 D_7b714.
    zstep F_7b7d4 D_7b7d4. stepn F_7b7d8 D_7b7d8.
  zstep F_7b7e4 D_7b7e4.
  zld F_7b7e8 D_7b7e8 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7ec D_7b7ec (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7f0 D_7b7f0 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7f4 D_7b7f4 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7f8 D_7b7f8 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7fc D_7b7fc (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_7b800 D_7b800 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_7b804 D_7b804.
  stepjr F_7b808 D_7b808 (0x12b88c : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. zret.
Qed.

#[using="Type"] Theorem art_poison3_hi0_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x1383c0 0xc000 -> apart (sp - 64) 64 0x1d3528 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> kHighMemBeg + 8 <= p + n -> p <= kHighMemEnd -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 2 ^ 61) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x7b4bc : word) M rom)
      (mkst regs' raw (Wf (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)))
                          (SB + p / 8) (Z.to_nat (n / 8)) v) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8) /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, art_poison_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr Wsh.
  pose proof (art_poison3_hi0_fn regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr) as RUN1.
  unfold kHighMemBeg, kHighMemEnd, SB in *.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?M1 _) =>
    assert (OK : store_ok ASEGS M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z.to_nat (n / 8)) = true)
      by (unfold art_poison_frame; apply wr_wok with (a := 2147450880 + p / 8) (n := n / 8); [|lia|lia]; repeat apply wr_Wn; exact Wsh);
    destruct (memset_summary M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z_to_bv 64 v) raw (n / 8) rom
               ltac:(lia) ltac:(rewrite art_u_lit by lia; lia) OK Hret R1
               ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity))
      as (r2 & RUN2 & P10 & AG)
  end.
  exists r2. split.
  { eapply msteps_trans; [exact RUN1|]. unfold Wf. rewrite cbyte_cbz in RUN2. unfold cbz in RUN2. rewrite art_u_lit in RUN2 by lia.
    replace (v mod 256) with v in RUN2 by (symmetry; apply Z.mod_small; lia).
    replace (Z_to_bv 64 ms_base) with (0x12b88c : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
  assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
  cbn [ms_clob In] in K.
  zsplit;
    try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
  intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
  rewrite K by (intuition congruence). kept_solve.
Qed.

#[using="Type"] Lemma art_poison3_lo_fn : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x1383c0 0xc000 -> apart (sp - 64) 64 0x1d3528 256 ->
  art_layout M ->
  8 <= p -> p + 8 <= SB -> p + n <= SB -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 2 ^ 61) ->
  msteps ASEGS (mkst regs (0x7b4bc : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 raw) 2 (Z_to_bv 64 sp)) 6 (Z_to_bv 64 0x12b88c)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (SB + p / 8))) 11 (Z_to_bv 64 v)) 12 (Z_to_bv 64 (n / 8)))
             13 (Z_to_bv 64 (p / 8))) 14 (Z_to_bv 64 (SB - 1))) 15 (Z_to_bv 64 0)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21))
       (0x12b88c : word)
       (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom).
Proof.
  intros regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr.
  unfold kHighMemBeg, kHighMemEnd, SB in *.
  zstep F_7b46c D_7b46c.
  zsd F_7b470 D_7b470 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_7b474 D_7b474 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_7b478 D_7b478 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_7b47c D_7b47c (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_7b480 D_7b480 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_7b484 D_7b484 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_7b488 D_7b488 (sp - 56) (U (getr regs 21)) ltac:(rewok W).
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
  - zbtk F_7b48c D_7b48c.
    stepn F_7b4a0 D_7b4a0. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7b4a4 D_7b4a4.
  zstep F_7b4a8 D_7b4a8.
  zld F_7b4ac D_7b4ac 0x1391b8 G48.
  zld F_7b4b0 D_7b4b0 0x1419f8 Csb. unfold SB in *.
  zstep F_7b4b4 D_7b4b4. zstep F_7b4b8 D_7b4b8. zstep F_7b4bc D_7b4bc.
  zstep F_7b4c0 D_7b4c0.
  zbtk F_7b4c4 D_7b4c4.
  stepn F_7b69c D_7b69c. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7b6a0 D_7b6a0.
  zstep F_7b6a4 D_7b6a4. zstep F_7b6a8 D_7b6a8.
  zbtk F_7b6ac D_7b6ac.
  zstep F_7b6f0 D_7b6f0. zld F_7b6f4 D_7b6f4 0x1391d8 G68. zld F_7b6f8 D_7b6f8 0x13b1c8 Crm.
  zbft F_7b6fc D_7b6fc.
  stepn F_7b700 D_7b700. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_7b704 D_7b704. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_7b708 D_7b708. zstep F_7b70c D_7b70c. zstep F_7b710 D_7b710.
    zbft F_7b714 D_7b714.
    zstep F_7b718 D_7b718. zld F_7b71c D_7b71c 0x1391a8 G38. zld F_7b720 D_7b720 (0x1d3528 + 120) Cth.
    zbtk F_7b724 D_7b724.
    zstep F_7b7d4 D_7b7d4. stepn F_7b7d8 D_7b7d8.
  zstep F_7b7e4 D_7b7e4.
  zld F_7b7e8 D_7b7e8 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7ec D_7b7ec (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7f0 D_7b7f0 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7f4 D_7b7f4 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7f8 D_7b7f8 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7fc D_7b7fc (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_7b800 D_7b800 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_7b804 D_7b804.
  stepjr F_7b808 D_7b808 (0x12b88c : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame. subst v. zret.
  - zbft F_7b48c D_7b48c.
    zstep F_7b490 D_7b490.
    zlb F_7b494 D_7b494 0x14125c Ccp.
    stepfence F_7b498 D_7b498.
    zbft F_7b49c D_7b49c.
    stepn F_7b4a0 D_7b4a0. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7b4a4 D_7b4a4.
  zstep F_7b4a8 D_7b4a8.
  zld F_7b4ac D_7b4ac 0x1391b8 G48.
  zld F_7b4b0 D_7b4b0 0x1419f8 Csb. unfold SB in *.
  zstep F_7b4b4 D_7b4b4. zstep F_7b4b8 D_7b4b8. zstep F_7b4bc D_7b4bc.
  zstep F_7b4c0 D_7b4c0.
  zbtk F_7b4c4 D_7b4c4.
  stepn F_7b69c D_7b69c. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7b6a0 D_7b6a0.
  zstep F_7b6a4 D_7b6a4. zstep F_7b6a8 D_7b6a8.
  zbtk F_7b6ac D_7b6ac.
  zstep F_7b6f0 D_7b6f0. zld F_7b6f4 D_7b6f4 0x1391d8 G68. zld F_7b6f8 D_7b6f8 0x13b1c8 Crm.
  zbft F_7b6fc D_7b6fc.
  stepn F_7b700 D_7b700. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_7b704 D_7b704. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_7b708 D_7b708. zstep F_7b70c D_7b70c. zstep F_7b710 D_7b710.
    zbtk F_7b714 D_7b714.
    zstep F_7b7d4 D_7b7d4. stepn F_7b7d8 D_7b7d8.
  zstep F_7b7e4 D_7b7e4.
  zld F_7b7e8 D_7b7e8 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7ec D_7b7ec (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7f0 D_7b7f0 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7f4 D_7b7f4 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7f8 D_7b7f8 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_7b7fc D_7b7fc (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_7b800 D_7b800 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_7b804 D_7b804.
  stepjr F_7b808 D_7b808 (0x12b88c : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame. zret.
Qed.

#[using="Type"] Theorem art_poison3_lo_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x1383c0 0xc000 -> apart (sp - 64) 64 0x1d3528 256 ->
  art_layout M ->
  8 <= p -> p + 8 <= SB -> p + n <= SB -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 2 ^ 61) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x7b4bc : word) M rom)
      (mkst regs' raw (Wf (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)))
                          (SB + p / 8) (Z.to_nat (n / 8)) v) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8) /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, art_poison_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr Wsh.
  pose proof (art_poison3_lo_fn regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr) as RUN1.
  unfold kHighMemBeg, kHighMemEnd, SB in *.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?M1 _) =>
    assert (OK : store_ok ASEGS M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z.to_nat (n / 8)) = true)
      by (unfold art_poison_frame; apply wr_wok with (a := 2147450880 + p / 8) (n := n / 8); [|lia|lia]; repeat apply wr_Wn; exact Wsh);
    destruct (memset_summary M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z_to_bv 64 v) raw (n / 8) rom
               ltac:(lia) ltac:(rewrite art_u_lit by lia; lia) OK Hret R1
               ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity))
      as (r2 & RUN2 & P10 & AG)
  end.
  exists r2. split.
  { eapply msteps_trans; [exact RUN1|]. unfold Wf. rewrite cbyte_cbz in RUN2. unfold cbz in RUN2. rewrite art_u_lit in RUN2 by lia.
    replace (v mod 256) with v in RUN2 by (symmetry; apply Z.mod_small; lia).
    replace (Z_to_bv 64 ms_base) with (0x12b88c : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
  assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
  cbn [ms_clob In] in K.
  zsplit;
    try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
  intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
  rewrite K by (intuition congruence). kept_solve.
Qed.

Definition art_poison_lo_ok (p n : Z) : Prop := 8 <= p /\ p + 8 <= SB /\ p + n <= SB.
Definition art_poison_hi_ok (p n : Z) : Prop := kHighMemBeg <= p /\ kHighMemBeg + 8 <= p + n /\ p <= kHighMemEnd /\ p + n <= kHighMemEnd + 1.

#[using="Type"] Theorem art_poison3_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x1383c0 0xc000 -> apart (sp - 64) 64 0x1d3528 256 ->
  art_layout M ->
  (art_poison_lo_ok p n \/ art_poison_hi_ok p n) -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 2 ^ 61) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x7b4bc : word) M rom)
      (mkst regs' raw (Wf (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)))
                          (SB + p / 8) (Z.to_nat (n / 8)) v) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8) /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, art_poison_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L [Hl|Hh] Hp8 Hn8 Hn Hv Hthr Wsh.
  - destruct Hl as (Ha & Hb & Hc). exact (art_poison3_lo_run regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Ha Hb Hc Hp8 Hn8 Hn Hv Hthr Wsh).
  - destruct Hh as (Ha & Hb & Hc & Hd). exact (art_poison3_hi0_run regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Ha Hd Hp8 Hn8 Hn Hb Hc Hv Hthr Wsh).
Qed.
End FPX.
