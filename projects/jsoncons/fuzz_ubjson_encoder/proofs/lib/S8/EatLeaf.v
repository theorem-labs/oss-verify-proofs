(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r65f44_65f5c Ea0_code_r67bcc_67d3c Ea0_code_r6bbd4_6bc28 Ea0_code_r60dd4_61420 Ea0_code_r80560_806c8 Ea0_code_r66e54_66ef4
  Ea0_code_r8d0d0_8d0e8 Ea0_code_r61f50_61f68 Ea0_code_rcd208_cd224 Ea0_code_r69654_69674 Ea0_code_r68820_68858 Ea0_code_r69818_698c8
  Ea0_code_r6de28_6df9c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_asan_inited_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1426d8 1 1 ->
  msteps ASEGS (mkst regs (0x80b58 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_80b08 D_80b08.
  zlb F_80b0c D_80b0c 0x1426d8 C.
  stepfence F_80b10 D_80b10.
  zstep F_80b14 D_80b14.
  zstep F_80b18 D_80b18.
  stepret F_80b1c D_80b1c raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_rss_limit_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1c3c62 1 0 ->
  msteps ASEGS (mkst regs (0x86820 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_867d0 D_867d0.
  zlb F_867d4 D_867d4 0x1c3c62 C.
  zstep F_867d8 D_867d8.
  stepret F_867dc D_867dc raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_may_return_null_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1c3c61 1 1 ->
  msteps ASEGS (mkst regs (0x867f8 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_867a8 D_867a8.
  zlb F_867ac D_867ac 0x1c3c61 C.
  zstep F_867b0 D_867b0.
  stepret F_867b4 D_867b4 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_can_poison_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x14125c 1 1 ->
  msteps ASEGS (mkst regs (0x7b4a8 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_7b458 D_7b458.
  zlb F_7b45c D_7b45c 0x14125c C.
  stepfence F_7b460 D_7b460.
  zstep F_7b464 D_7b464.
  stepret F_7b468 D_7b468 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_malloc_ctx_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1426fc 4 30 ->
  msteps ASEGS (mkst regs (0x827f0 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 30)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_827a0 D_827a0.
  zlw F_827a4 D_827a4 0x1426fc C.
  stepfence F_827a8 D_827a8.
  stepret F_827ac D_827ac raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_get_pc_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw ->
  msteps ASEGS (mkst regs (0x9b2cc : word) M rom) (mkst (regupd regs 10 raw) raw M rom).
Proof.
  intros regs M rom raw H1 Hret.
  zstep F_9b27c D_9b27c.
  stepret F_9b280 D_9b280 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_try_init_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> cellA M 0x1426d8 1 1 -> apart (sp - 16) 16 0x1426d8 1 ->
  msteps ASEGS (mkst regs (0x81a68 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 1))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' W C Ap.
  zstep F_81a18 D_81a18.
  zsd F_81a1c D_81a1c (sp - 8) (U raw) ltac:(rewok W).
  zsd F_81a20 D_81a20 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zstep F_81a24 D_81a24. zstep F_81a28 D_81a28.
  assert (C1 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) 0x1426d8 1 1) by (unfold apart in *; recell C).
  zlb F_81a2c D_81a2c 0x1426d8 C1.
  zstep F_81a30 D_81a30.
  stepfence F_81a34 D_81a34.
  zbft F_81a38 D_81a38.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  assert (Cs0 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 16) 8 (U (getr regs 8))) by (apply cell_Wn_hit; lia).
  zld F_81a3c D_81a3c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_81a40 D_81a40 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zstep F_81a44 D_81a44.
  stepret F_81a48 D_81a48 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_lsan_off_fn : forall regs (M rom : word -> option byte) (raw : word) (tp off : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= off -> tp + off + 4 < 2 ^ 64 ->
  cellA M 0x139e18 8 off -> cellA M (tp + off) 4 0 ->
  msteps ASEGS (mkst regs (0xa7e48 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw tp off H1 Hret H4 Htp Htp' Hoff Hoff' Cg Ct.
  zstep F_a7df8 D_a7df8.
  zld F_a7dfc D_a7dfc 0x139e18 Cg.
  zstep F_a7e00 D_a7e00.
  zlw F_a7e04 D_a7e04 (tp + off) Ct.
  zstep F_a7e08 D_a7e08.
  stepret F_a7e0c D_a7e0c raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_tsd_get_fn : forall regs (M rom : word -> option byte) (raw : word) (tp key tsd ctx : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 4096 <= tp -> tp + 4096 < 2 ^ 64 ->
  0 <= key < 128 -> 0 <= tsd -> tsd + 1024 < 2 ^ 64 -> 0 <= ctx < 2 ^ 64 ->
  cellA M 0x141260 1 1 -> cellA M 0x141264 4 key -> cellA M (tp - 88) 8 tsd -> cellA M (tsd + 8 * key) 8 ctx ->
  msteps ASEGS (mkst regs (0x7c8e8 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 ctx)) 11 (Z_to_bv 64 tsd)) raw M rom).
Proof.
  intros regs M rom raw tp key tsd ctx H1 Hret H4 Htp Htp' Hkey Htsd Htsd' Hctx Ci Ck Ctsd Cctx.
  zstep F_7c898 D_7c898. zstep F_7c89c D_7c89c.
  zlbu F_7c8a0 D_7c8a0 0x141260 Ci.
  zbft F_7c8a4 D_7c8a4.
  zlw F_7c8a8 D_7c8a8 0x141264 Ck.
  stepn F_7c8ac D_7c8ac.
  zstep F_12e070 D_12e070.
  zld F_12e074 D_12e074 (tp - 88) Ctsd.
  zstep F_12e078 D_12e078.
  stepn F_12e07c D_12e07c. rwH. rewrite (art_zb_srli_exact _ 29 (8 * key)) by lia.
  zstep F_12e080 D_12e080.
  zld F_12e084 D_12e084 (tsd + 8 * key) Cctx.
  stepret F_12e088 D_12e088 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Definition art_tsd (M : word -> option byte) (tp key tsd ctx t : Z) : Prop :=
  cellA M 0x141260 1 1 /\ cellA M 0x141264 4 key /\ cellA M (tp - 88) 8 tsd /\ cellA M (tsd + 8 * key) 8 ctx /\ cellA M (ctx + 152) 8 t
  /\ 4096 <= tp /\ tp + 4096 < 2 ^ 64 /\ 0 <= key < 128 /\ 0 <= tsd /\ tsd + 1024 < 2 ^ 64 /\ 4096 <= ctx /\ ctx + 4096 < 2 ^ 64 /\ 0 <= t < 2 ^ 64.

#[using="Type"] Lemma art_tsd_Wn : forall n M a v tp key tsd ctx t,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  apart a (Z.of_nat n) 0x141260 8 -> apart a (Z.of_nat n) (tp - 88) 8 -> apart a (Z.of_nat n) (tsd + 8 * key) 8 -> apart a (Z.of_nat n) (ctx + 152) 8 ->
  art_tsd M tp key tsd ctx t -> art_tsd (Wn n M a v) tp key tsd ctx t.
Proof.
  intros n M a v tp key tsd ctx t Ha Hn A1 A2 A3 A4 (C1 & C2 & C3 & C4 & C5 & R).
  unfold art_tsd. unfold apart in *.
  repeat split; try lia; (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia| assumption]).
Qed.

#[using="Type"] Lemma art_cur_thread_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> art_tsd M tp key tsd ctx t ->
  apart (sp - 16) 16 0x141260 8 -> apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x84268 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 t)) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD A1 A2 A3 A4.
  pose proof (art_tsd_Wn 8 M (sp - 8) (U raw) tp key tsd ctx t ltac:(lia) ltac:(lia)
                ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) TSD)
    as (C1 & C2 & C3 & C4 & C5 & R).
  zstep F_84218 D_84218.
  zsd F_8421c D_8421c (sp - 8) (U raw) ltac:(rewok W).
  stepn F_84220 D_84220.
  zcall (art_tsd_get_fn _ _ _ _ tp key tsd ctx).
  zbft F_84224 D_84224.
  zld F_84228 D_84228 (ctx + 152) C5.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_8422c D_8422c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_84230 D_84230.
  stepret F_84234 D_84234 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_thread_stats_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 32 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 32) 32 0x141260 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x83434 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800))) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 24) 0x83440) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD Ht A1 A2 A3 A4.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  zstep F_833e4 D_833e4.
  zsd F_833e8 D_833e8 (sp - 8) (U raw) ltac:(rewok W).
  stepn F_833ec D_833ec.
  zcall (art_cur_thread_fn _ _ _ _ (sp - 16) tp key tsd ctx t).
  { apply art_tsd_Wn; unfold apart in *; cbn; try lia. exact TSD. }
  zbft F_833f0 D_833f0.
  zstep F_833f4 D_833f4. zstep F_833f8 D_833f8.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16 - 8) (U (Z_to_bv 64 0x83440 : word))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  zld F_833fc D_833fc (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_83400 D_83400.
  stepret F_83404 D_83404 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_stack_top_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x8442c : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 top)) 11 (Z_to_bv 64 top)) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_843dc D_843dc (t + 40) C40.
  stepfence F_843e0 D_843e0.
  zbtk F_843e4 D_843e4.
  zld F_8441c D_8441c (t + 8) C8.
  zld F_84420 D_84420 (t + 16) C16.
  zstep F_84424 D_84424. zstep F_84428 D_84428.
  stepn F_8442c D_8442c. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_l by lia | rewrite art_land_full_r by lia].
  stepret F_84430 D_84430 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_stack_bottom_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x84484 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 bot)) 11 (Z_to_bv 64 (2 ^ 64 - 1))) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_84434 D_84434 (t + 40) C40.
  stepfence F_84438 D_84438.
  zbtk F_8443c D_8443c.
  zld F_84474 D_84474 (t + 8) C8.
  zld F_84478 D_84478 (t + 16) C16.
  zstep F_8447c D_8447c. zstep F_84480 D_84480.
  stepn F_84484 D_84484. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_r by lia | rewrite art_land_full_l by lia].
  stepret F_84488 D_84488 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
