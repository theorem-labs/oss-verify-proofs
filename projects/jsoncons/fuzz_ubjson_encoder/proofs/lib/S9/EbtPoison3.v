(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import muslA.Eb0SumsMemset_code.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import muslA.Eb0SumsMemsetS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r60dd4_61420.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbtPoison EbtPoisonRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_poison3_hi0_fn : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x13d880 0xc000 -> apart (sp - 64) 64 0x1d7c28 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> kHighMemBeg + 8 <= p + n -> p <= kHighMemEnd -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 2 ^ 61) ->
  msteps ASEGS (mkst regs (0x7bce4 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 (SB + kHighMemEnd / 8))) 6 (Z_to_bv 64 0x130034)) 7 (Z_to_bv 64 kHighMemEnd)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (SB + p / 8))) 11 (Z_to_bv 64 v)) 12 (Z_to_bv 64 (n / 8))) 13 (Z_to_bv 64 (p / 8))) 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 (kHighMemEnd / 8))) 16 (Z_to_bv 64 (2 ^ 64 - 1))) 17 (Z_to_bv 64 0)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21)) 28 (Z_to_bv 64 kHighMemEnd))
       (0x130034 : word)
       (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom).
Proof.
  intros regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr.
  unfold kHighMemBeg, kHighMemEnd in *.
  zstep F_7bc94 D_7bc94.
  zsd F_7bc98 D_7bc98 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_7bc9c D_7bc9c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_7bca0 D_7bca0 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_7bca4 D_7bca4 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_7bca8 D_7bca8 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_7bcac D_7bcac (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_7bcb0 D_7bcb0 (sp - 56) (U (getr regs 21)) ltac:(rewok W).
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

  - zbtk F_7bcb4 D_7bcb4.
    stepn F_7bcc8 D_7bcc8. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7bccc D_7bccc.
  zstep F_7bcd0 D_7bcd0.
  zld F_7bcd4 D_7bcd4 0x13d8c8 G48.
  zld F_7bcd8 D_7bcd8 0x1460f8 Csb. unfold SB in *.
  zstep F_7bcdc D_7bcdc. zstep F_7bce0 D_7bce0. zstep F_7bce4 D_7bce4.
  zstep F_7bce8 D_7bce8.
  zbft F_7bcec D_7bcec.
  zstep F_7bcf0 D_7bcf0. zld F_7bcf4 D_7bcf4 0x13d8d0 G50.
  zstep F_7bcf8 D_7bcf8. zld F_7bcfc D_7bcfc 0x13d8d8 G58.
  zld F_7bd00 D_7bd00 0x146de8 Cmb. zld F_7bd04 D_7bd04 0x146df0 Cme.
  zstep F_7bd08 D_7bd08.
  zbtk F_7bd0c D_7bd0c.
  zstep F_7bd14 D_7bd14. zld F_7bd18 D_7bd18 0x13d8e0 G60. zld F_7bd1c D_7bd1c 0x146de0 Che.
  zstep F_7bd20 D_7bd20.
  zstep F_7bd24 D_7bd24.
  zbft F_7bd28 D_7bd28.
  zbtk F_7bd2c D_7bd2c.
  zld F_7bdf4 D_7bdf4 0x146de0 Che.
  zstep F_7bdf8 D_7bdf8.
  zstep F_7bdfc D_7bdfc.
  zbft F_7be00 D_7be00.
  zbtk F_7be04 D_7be04.
  stepn F_7bec4 D_7bec4. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7bec8 D_7bec8.
  zstep F_7becc D_7becc. zstep F_7bed0 D_7bed0.
  zbft F_7bed4 D_7bed4.
  zstep F_7bed8 D_7bed8. zld F_7bedc D_7bedc 0x13d8d0 G50.
  zstep F_7bee0 D_7bee0. zld F_7bee4 D_7bee4 0x13d8d8 G58.
  zld F_7bee8 D_7bee8 0x146de8 Cmb. zld F_7beec D_7beec 0x146df0 Cme.
  zstep F_7bef0 D_7bef0.
  zbtk F_7bef4 D_7bef4.
  zstep F_7befc D_7befc. zld F_7bf00 D_7bf00 0x13d8e0 G60. zld F_7bf04 D_7bf04 0x146de0 Che.
  zstep F_7bf08 D_7bf08.
  zstep F_7bf0c D_7bf0c.
  zbft F_7bf10 D_7bf10.
  zbft F_7bf14 D_7bf14.
  zstep F_7bf18 D_7bf18. zld F_7bf1c D_7bf1c 0x13d8e8 G68. zld F_7bf20 D_7bf20 0x13f8d8 Crm.
  zbft F_7bf24 D_7bf24.
  stepn F_7bf28 D_7bf28. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_7bf2c D_7bf2c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_7bf30 D_7bf30. zstep F_7bf34 D_7bf34. zstep F_7bf38 D_7bf38.
    zbft F_7bf3c D_7bf3c.
    zstep F_7bf40 D_7bf40. zld F_7bf44 D_7bf44 0x13d8b8 G38. zld F_7bf48 D_7bf48 (0x1d7c28 + 120) Cth.
    zbtk F_7bf4c D_7bf4c.
    zstep F_7bffc D_7bffc. stepn F_7c000 D_7c000.
  zstep F_7c00c D_7c00c.
  zld F_7c010 D_7c010 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_7c014 D_7c014 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_7c018 D_7c018 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_7c01c D_7c01c (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_7c020 D_7c020 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_7c024 D_7c024 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_7c028 D_7c028 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_7c02c D_7c02c.
  stepjr F_7c030 D_7c030 (0x130034 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. subst v. zret.

  - zbft F_7bcb4 D_7bcb4.
    zstep F_7bcb8 D_7bcb8.
    zlb F_7bcbc D_7bcbc 0x14595c Ccp.
    stepfence F_7bcc0 D_7bcc0.
    zbft F_7bcc4 D_7bcc4.
    stepn F_7bcc8 D_7bcc8. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7bccc D_7bccc.
  zstep F_7bcd0 D_7bcd0.
  zld F_7bcd4 D_7bcd4 0x13d8c8 G48.
  zld F_7bcd8 D_7bcd8 0x1460f8 Csb. unfold SB in *.
  zstep F_7bcdc D_7bcdc. zstep F_7bce0 D_7bce0. zstep F_7bce4 D_7bce4.
  zstep F_7bce8 D_7bce8.
  zbft F_7bcec D_7bcec.
  zstep F_7bcf0 D_7bcf0. zld F_7bcf4 D_7bcf4 0x13d8d0 G50.
  zstep F_7bcf8 D_7bcf8. zld F_7bcfc D_7bcfc 0x13d8d8 G58.
  zld F_7bd00 D_7bd00 0x146de8 Cmb. zld F_7bd04 D_7bd04 0x146df0 Cme.
  zstep F_7bd08 D_7bd08.
  zbtk F_7bd0c D_7bd0c.
  zstep F_7bd14 D_7bd14. zld F_7bd18 D_7bd18 0x13d8e0 G60. zld F_7bd1c D_7bd1c 0x146de0 Che.
  zstep F_7bd20 D_7bd20.
  zstep F_7bd24 D_7bd24.
  zbft F_7bd28 D_7bd28.
  zbtk F_7bd2c D_7bd2c.
  zld F_7bdf4 D_7bdf4 0x146de0 Che.
  zstep F_7bdf8 D_7bdf8.
  zstep F_7bdfc D_7bdfc.
  zbft F_7be00 D_7be00.
  zbtk F_7be04 D_7be04.
  stepn F_7bec4 D_7bec4. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7bec8 D_7bec8.
  zstep F_7becc D_7becc. zstep F_7bed0 D_7bed0.
  zbft F_7bed4 D_7bed4.
  zstep F_7bed8 D_7bed8. zld F_7bedc D_7bedc 0x13d8d0 G50.
  zstep F_7bee0 D_7bee0. zld F_7bee4 D_7bee4 0x13d8d8 G58.
  zld F_7bee8 D_7bee8 0x146de8 Cmb. zld F_7beec D_7beec 0x146df0 Cme.
  zstep F_7bef0 D_7bef0.
  zbtk F_7bef4 D_7bef4.
  zstep F_7befc D_7befc. zld F_7bf00 D_7bf00 0x13d8e0 G60. zld F_7bf04 D_7bf04 0x146de0 Che.
  zstep F_7bf08 D_7bf08.
  zstep F_7bf0c D_7bf0c.
  zbft F_7bf10 D_7bf10.
  zbft F_7bf14 D_7bf14.
  zstep F_7bf18 D_7bf18. zld F_7bf1c D_7bf1c 0x13d8e8 G68. zld F_7bf20 D_7bf20 0x13f8d8 Crm.
  zbft F_7bf24 D_7bf24.
  stepn F_7bf28 D_7bf28. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_7bf2c D_7bf2c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_7bf30 D_7bf30. zstep F_7bf34 D_7bf34. zstep F_7bf38 D_7bf38.
    zbtk F_7bf3c D_7bf3c.
    zstep F_7bffc D_7bffc. stepn F_7c000 D_7c000.
  zstep F_7c00c D_7c00c.
  zld F_7c010 D_7c010 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_7c014 D_7c014 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_7c018 D_7c018 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_7c01c D_7c01c (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_7c020 D_7c020 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_7c024 D_7c024 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_7c028 D_7c028 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_7c02c D_7c02c.
  stepjr F_7c030 D_7c030 (0x130034 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame, SB. zret.
Qed.

#[using="Type"] Theorem art_poison3_hi0_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x13d880 0xc000 -> apart (sp - 64) 64 0x1d7c28 256 ->
  art_layout M ->
  kHighMemBeg <= p -> p + n <= kHighMemEnd + 1 -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> kHighMemBeg + 8 <= p + n -> p <= kHighMemEnd -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 2 ^ 61) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x7bce4 : word) M rom)
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
    replace (Z_to_bv 64 ms_base) with (0x130034 : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
  assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
  cbn [ms_clob In] in K.
  zsplit;
    try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
  intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
  rewrite K by (intuition congruence). kept_solve.
Qed.

#[using="Type"] Lemma art_poison3_lo_fn : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x13d880 0xc000 -> apart (sp - 64) 64 0x1d7c28 256 ->
  art_layout M ->
  8 <= p -> p + 8 <= SB -> p + n <= SB -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 2 ^ 61) ->
  msteps ASEGS (mkst regs (0x7bce4 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 raw) 2 (Z_to_bv 64 sp)) 6 (Z_to_bv 64 0x130034)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (SB + p / 8))) 11 (Z_to_bv 64 v)) 12 (Z_to_bv 64 (n / 8)))
             13 (Z_to_bv 64 (p / 8))) 14 (Z_to_bv 64 (SB - 1))) 15 (Z_to_bv 64 0)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21))
       (0x130034 : word)
       (art_poison_frame M sp (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom).
Proof.
  intros regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr.
  unfold kHighMemBeg, kHighMemEnd, SB in *.
  zstep F_7bc94 D_7bc94.
  zsd F_7bc98 D_7bc98 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_7bc9c D_7bc9c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_7bca0 D_7bca0 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_7bca4 D_7bca4 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_7bca8 D_7bca8 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_7bcac D_7bcac (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_7bcb0 D_7bcb0 (sp - 56) (U (getr regs 21)) ltac:(rewok W).
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
  - zbtk F_7bcb4 D_7bcb4.
    stepn F_7bcc8 D_7bcc8. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7bccc D_7bccc.
  zstep F_7bcd0 D_7bcd0.
  zld F_7bcd4 D_7bcd4 0x13d8c8 G48.
  zld F_7bcd8 D_7bcd8 0x1460f8 Csb. unfold SB in *.
  zstep F_7bcdc D_7bcdc. zstep F_7bce0 D_7bce0. zstep F_7bce4 D_7bce4.
  zstep F_7bce8 D_7bce8.
  zbtk F_7bcec D_7bcec.
  stepn F_7bec4 D_7bec4. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7bec8 D_7bec8.
  zstep F_7becc D_7becc. zstep F_7bed0 D_7bed0.
  zbtk F_7bed4 D_7bed4.
  zstep F_7bf18 D_7bf18. zld F_7bf1c D_7bf1c 0x13d8e8 G68. zld F_7bf20 D_7bf20 0x13f8d8 Crm.
  zbft F_7bf24 D_7bf24.
  stepn F_7bf28 D_7bf28. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_7bf2c D_7bf2c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_7bf30 D_7bf30. zstep F_7bf34 D_7bf34. zstep F_7bf38 D_7bf38.
    zbft F_7bf3c D_7bf3c.
    zstep F_7bf40 D_7bf40. zld F_7bf44 D_7bf44 0x13d8b8 G38. zld F_7bf48 D_7bf48 (0x1d7c28 + 120) Cth.
    zbtk F_7bf4c D_7bf4c.
    zstep F_7bffc D_7bffc. stepn F_7c000 D_7c000.
  zstep F_7c00c D_7c00c.
  zld F_7c010 D_7c010 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_7c014 D_7c014 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_7c018 D_7c018 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_7c01c D_7c01c (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_7c020 D_7c020 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_7c024 D_7c024 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_7c028 D_7c028 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_7c02c D_7c02c.
  stepjr F_7c030 D_7c030 (0x130034 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame. subst v. zret.
  - zbft F_7bcb4 D_7bcb4.
    zstep F_7bcb8 D_7bcb8.
    zlb F_7bcbc D_7bcbc 0x14595c Ccp.
    stepfence F_7bcc0 D_7bcc0.
    zbft F_7bcc4 D_7bcc4.
    stepn F_7bcc8 D_7bcc8. rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7bccc D_7bccc.
  zstep F_7bcd0 D_7bcd0.
  zld F_7bcd4 D_7bcd4 0x13d8c8 G48.
  zld F_7bcd8 D_7bcd8 0x1460f8 Csb. unfold SB in *.
  zstep F_7bcdc D_7bcdc. zstep F_7bce0 D_7bce0. zstep F_7bce4 D_7bce4.
  zstep F_7bce8 D_7bce8.
  zbtk F_7bcec D_7bcec.
  stepn F_7bec4 D_7bec4. rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
  zbft F_7bec8 D_7bec8.
  zstep F_7becc D_7becc. zstep F_7bed0 D_7bed0.
  zbtk F_7bed4 D_7bed4.
  zstep F_7bf18 D_7bf18. zld F_7bf1c D_7bf1c 0x13d8e8 G68. zld F_7bf20 D_7bf20 0x13f8d8 Crm.
  zbft F_7bf24 D_7bf24.
  stepn F_7bf28 D_7bf28. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  stepn F_7bf2c D_7bf2c. rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
  zstep F_7bf30 D_7bf30. zstep F_7bf34 D_7bf34. zstep F_7bf38 D_7bf38.
    zbtk F_7bf3c D_7bf3c.
    zstep F_7bffc D_7bffc. stepn F_7c000 D_7c000.
  zstep F_7c00c D_7c00c.
  zld F_7c010 D_7c010 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_7c014 D_7c014 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zld F_7c018 D_7c018 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
  zld F_7c01c D_7c01c (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
  zld F_7c020 D_7c020 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
  zld F_7c024 D_7c024 (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
  zld F_7c028 D_7c028 (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
  zstep F_7c02c D_7c02c.
  stepjr F_7c030 D_7c030 (0x130034 : bv 64)%bv ltac:(gres; bveq).
    unfold Mf, art_poison_frame. zret.
Qed.

#[using="Type"] Theorem art_poison3_lo_run : forall regs (M rom : word -> option byte) (raw : word) (sp p n v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 v ->
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x13d880 0xc000 -> apart (sp - 64) 64 0x1d7c28 256 ->
  art_layout M ->
  8 <= p -> p + 8 <= SB -> p + n <= SB -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 2 ^ 61) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x7bce4 : word) M rom)
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
    replace (Z_to_bv 64 ms_base) with (0x130034 : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
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
  64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> apart (sp - 64) 64 0x13d880 0xc000 -> apart (sp - 64) 64 0x1d7c28 256 ->
  art_layout M ->
  (art_poison_lo_ok p n \/ art_poison_hi_ok p n) -> p mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> 0 <= v < 256 ->
  (v = 0 -> n / 8 < 2 ^ 61) ->
  wrA M (SB + p / 8) (n / 8) ->
  exists regs',
    msteps ASEGS (mkst regs (0x7bce4 : word) M rom)
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
