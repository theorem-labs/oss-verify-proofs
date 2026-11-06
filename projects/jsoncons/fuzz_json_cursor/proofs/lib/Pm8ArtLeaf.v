(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  Pm8_code_81000_82000 Pm8_code_83000_84000 Pm8_code_87000_88000 Pm8_code_88000_89000 Pm8_code_89000_8a000 Pm8_code_8a000_8b000 Pm8_code_8d000_8e000 Pm8_code_a1000_a2000 Pm8_code_ae000_af000 Pm8_code_147000_148000

  .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_asan_inited_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x15d698 1 1 ->
  msteps ASEGS (mkst regs (0x873b4 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_87364 D_87364.
  zlb F_87368 D_87368 0x15d698 C.
  stepfence F_8736c D_8736c.
  zstep F_87370 D_87370.
  zstep F_87374 D_87374.
  stepret F_87378 D_87378 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_rss_limit_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1dec22 1 0 ->
  msteps ASEGS (mkst regs (0x8d07c : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_8d02c D_8d02c.
  zlb F_8d030 D_8d030 0x1dec22 C.
  zstep F_8d034 D_8d034.
  stepret F_8d038 D_8d038 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_may_return_null_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1dec21 1 1 ->
  msteps ASEGS (mkst regs (0x8d054 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_8d004 D_8d004.
  zlb F_8d008 D_8d008 0x1dec21 C.
  zstep F_8d00c D_8d00c.
  stepret F_8d010 D_8d010 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_can_poison_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x15c21c 1 1 ->
  msteps ASEGS (mkst regs (0x81d04 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_81cb4 D_81cb4.
  zlb F_81cb8 D_81cb8 0x15c21c C.
  stepfence F_81cbc D_81cbc.
  zstep F_81cc0 D_81cc0.
  stepret F_81cc4 D_81cc4 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_malloc_ctx_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x15d6bc 4 30 ->
  msteps ASEGS (mkst regs (0x8904c : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 30)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_88ffc D_88ffc.
  zlw F_89000 D_89000 0x15d6bc C.
  stepfence F_89004 D_89004.
  stepret F_89008 D_89008 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_get_pc_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw ->
  msteps ASEGS (mkst regs (0xa1b28 : word) M rom) (mkst (regupd regs 10 raw) raw M rom).
Proof.
  intros regs M rom raw H1 Hret.
  zstep F_a1ad8 D_a1ad8.
  stepret F_a1adc D_a1adc raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_try_init_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> cellA M 0x15d698 1 1 -> apart (sp - 16) 16 0x15d698 1 ->
  msteps ASEGS (mkst regs (0x882c4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 1))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' W C Ap.
  zstep F_88274 D_88274.
  zsd F_88278 D_88278 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_8827c D_8827c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zstep F_88280 D_88280. zstep F_88284 D_88284.
  assert (C1 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) 0x15d698 1 1) by (unfold apart in *; recell C).
  zlb F_88288 D_88288 0x15d698 C1.
  zstep F_8828c D_8828c.
  stepfence F_88290 D_88290.
  zbft F_88294 D_88294.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  assert (Cs0 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 16) 8 (U (getr regs 8))) by (apply cell_Wn_hit; lia).
  zld F_88298 D_88298 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_8829c D_8829c (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zstep F_882a0 D_882a0.
  stepret F_882a4 D_882a4 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_lsan_off_fn : forall regs (M rom : word -> option byte) (raw : word) (tp off : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= off -> tp + off + 4 < 2 ^ 64 ->
  cellA M 0x153d98 8 off -> cellA M (tp + off) 4 0 ->
  msteps ASEGS (mkst regs (0xae6a4 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw tp off H1 Hret H4 Htp Htp' Hoff Hoff' Cg Ct.
  zstep F_ae654 D_ae654.
  zld F_ae658 D_ae658 0x153d98 Cg.
  zstep F_ae65c D_ae65c.
  zlw F_ae660 D_ae660 (tp + off) Ct.
  zstep F_ae664 D_ae664.
  stepret F_ae668 D_ae668 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_tsd_get_fn : forall regs (M rom : word -> option byte) (raw : word) (tp key tsd ctx : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 4096 <= tp -> tp + 4096 < 2 ^ 64 ->
  0 <= key < 128 -> 0 <= tsd -> tsd + 1024 < 2 ^ 64 -> 0 <= ctx < 2 ^ 64 ->
  cellA M 0x15c220 1 1 -> cellA M 0x15c224 4 key -> cellA M (tp - 88) 8 tsd -> cellA M (tsd + 8 * key) 8 ctx ->
  msteps ASEGS (mkst regs (0x83144 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 ctx)) 11 (Z_to_bv 64 tsd)) raw M rom).
Proof.
  intros regs M rom raw tp key tsd ctx H1 Hret H4 Htp Htp' Hkey Htsd Htsd' Hctx Ci Ck Ctsd Cctx.
  zstep F_830f4 D_830f4. zstep F_830f8 D_830f8.
  zlbu F_830fc D_830fc 0x15c220 Ci.
  zbft F_83100 D_83100.
  zlw F_83104 D_83104 0x15c224 Ck.
  stepn F_83108 D_83108.
  zstep F_147aec D_147aec.
  zld F_147af0 D_147af0 (tp - 88) Ctsd.
  zstep F_147af4 D_147af4.
  stepn F_147af8 D_147af8. rwH. rewrite (art_zb_srli_exact _ 29 (8 * key)) by lia.
  zstep F_147afc D_147afc.
  zld F_147b00 D_147b00 (tsd + 8 * key) Cctx.
  stepret F_147b04 D_147b04 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Definition art_tsd (M : word -> option byte) (tp key tsd ctx t : Z) : Prop :=
  cellA M 0x15c220 1 1 /\ cellA M 0x15c224 4 key /\ cellA M (tp - 88) 8 tsd /\ cellA M (tsd + 8 * key) 8 ctx /\ cellA M (ctx + 152) 8 t
  /\ 4096 <= tp /\ tp + 4096 < 2 ^ 64 /\ 0 <= key < 128 /\ 0 <= tsd /\ tsd + 1024 < 2 ^ 64 /\ 4096 <= ctx /\ ctx + 4096 < 2 ^ 64 /\ 0 <= t < 2 ^ 64.

Lemma art_tsd_Wn : forall n M a v tp key tsd ctx t,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  apart a (Z.of_nat n) 0x15c220 8 -> apart a (Z.of_nat n) (tp - 88) 8 -> apart a (Z.of_nat n) (tsd + 8 * key) 8 -> apart a (Z.of_nat n) (ctx + 152) 8 ->
  art_tsd M tp key tsd ctx t -> art_tsd (Wn n M a v) tp key tsd ctx t.
Proof.
  intros n M a v tp key tsd ctx t Ha Hn A1 A2 A3 A4 (C1 & C2 & C3 & C4 & C5 & R).
  unfold art_tsd. unfold apart in *.
  repeat split; try lia; (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia| assumption]).
Qed.

Lemma art_cur_thread_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> art_tsd M tp key tsd ctx t ->
  apart (sp - 16) 16 0x15c220 8 -> apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x8aac4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 t)) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD A1 A2 A3 A4.
  pose proof (art_tsd_Wn 8 M (sp - 8) (U raw) tp key tsd ctx t ltac:(lia) ltac:(lia)
                ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) TSD)
    as (C1 & C2 & C3 & C4 & C5 & R).
  zstep F_8aa74 D_8aa74.
  zsd F_8aa78 D_8aa78 (sp - 8) (U raw) ltac:(rewok W).
  stepn F_8aa7c D_8aa7c.
  zcall (art_tsd_get_fn _ _ _ _ tp key tsd ctx).
  zbft F_8aa80 D_8aa80.
  zld F_8aa84 D_8aa84 (ctx + 152) C5.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_8aa88 D_8aa88 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_8aa8c D_8aa8c.
  stepret F_8aa90 D_8aa90 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_thread_stats_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 32 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 32) 32 0x15c220 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x89c90 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800))) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 24) 0x89c9c) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD Ht A1 A2 A3 A4.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  zstep F_89c40 D_89c40.
  zsd F_89c44 D_89c44 (sp - 8) (U raw) ltac:(rewok W).
  stepn F_89c48 D_89c48.
  zcall (art_cur_thread_fn _ _ _ _ (sp - 16) tp key tsd ctx t).
  { apply art_tsd_Wn; unfold apart in *; cbn; try lia. exact TSD. }
  zbft F_89c4c D_89c4c.
  zstep F_89c50 D_89c50. zstep F_89c54 D_89c54.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16 - 8) (U (Z_to_bv 64 0x89c9c : word))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  zld F_89c58 D_89c58 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_89c5c D_89c5c.
  stepret F_89c60 D_89c60 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_stack_top_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x8ac88 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 top)) 11 (Z_to_bv 64 top)) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_8ac38 D_8ac38 (t + 40) C40.
  stepfence F_8ac3c D_8ac3c.
  zbtk F_8ac40 D_8ac40.
  zld F_8ac78 D_8ac78 (t + 8) C8.
  zld F_8ac7c D_8ac7c (t + 16) C16.
  zstep F_8ac80 D_8ac80. zstep F_8ac84 D_8ac84.
  stepn F_8ac88 D_8ac88. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_l by lia | rewrite art_land_full_r by lia].
  stepret F_8ac8c D_8ac8c raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_stack_bottom_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x8ace0 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 bot)) 11 (Z_to_bv 64 (2 ^ 64 - 1))) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_8ac90 D_8ac90 (t + 40) C40.
  stepfence F_8ac94 D_8ac94.
  zbtk F_8ac98 D_8ac98.
  zld F_8acd0 D_8acd0 (t + 8) C8.
  zld F_8acd4 D_8acd4 (t + 16) C16.
  zstep F_8acd8 D_8acd8. zstep F_8acdc D_8acdc.
  stepn F_8ace0 D_8ace0. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_r by lia | rewrite art_land_full_l by lia].
  stepret F_8ace4 D_8ace4 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
