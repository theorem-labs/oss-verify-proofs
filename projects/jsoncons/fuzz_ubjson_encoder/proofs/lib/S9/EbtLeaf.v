(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r65f44_65f5c Eb0_code_r67bcc_67d3c Eb0_code_r6bbd4_6bc28 Eb0_code_r60dd4_61420 Eb0_code_r80560_806c8 Eb0_code_r66e54_66ef4
  Eb0_code_r8d0d0_8d0e8 Eb0_code_r61f50_61f68 Eb0_code_rcd208_cd224 Eb0_code_r69654_69674 Eb0_code_r68820_68858 Eb0_code_r69818_698c8
  Eb0_code_r6de28_6df9c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_asan_inited_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x146dd8 1 1 ->
  msteps ASEGS (mkst regs (0x81380 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_81330 D_81330.
  zlb F_81334 D_81334 0x146dd8 C.
  stepfence F_81338 D_81338.
  zstep F_8133c D_8133c.
  zstep F_81340 D_81340.
  stepret F_81344 D_81344 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_rss_limit_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1c8362 1 0 ->
  msteps ASEGS (mkst regs (0x87048 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_86ff8 D_86ff8.
  zlb F_86ffc D_86ffc 0x1c8362 C.
  zstep F_87000 D_87000.
  stepret F_87004 D_87004 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_may_return_null_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1c8361 1 1 ->
  msteps ASEGS (mkst regs (0x87020 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_86fd0 D_86fd0.
  zlb F_86fd4 D_86fd4 0x1c8361 C.
  zstep F_86fd8 D_86fd8.
  stepret F_86fdc D_86fdc raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_can_poison_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x14595c 1 1 ->
  msteps ASEGS (mkst regs (0x7bcd0 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_7bc80 D_7bc80.
  zlb F_7bc84 D_7bc84 0x14595c C.
  stepfence F_7bc88 D_7bc88.
  zstep F_7bc8c D_7bc8c.
  stepret F_7bc90 D_7bc90 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_malloc_ctx_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x146dfc 4 30 ->
  msteps ASEGS (mkst regs (0x83018 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 30)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_82fc8 D_82fc8.
  zlw F_82fcc D_82fcc 0x146dfc C.
  stepfence F_82fd0 D_82fd0.
  stepret F_82fd4 D_82fd4 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_get_pc_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw ->
  msteps ASEGS (mkst regs (0x9baf4 : word) M rom) (mkst (regupd regs 10 raw) raw M rom).
Proof.
  intros regs M rom raw H1 Hret.
  zstep F_9baa4 D_9baa4.
  stepret F_9baa8 D_9baa8 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_try_init_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> cellA M 0x146dd8 1 1 -> apart (sp - 16) 16 0x146dd8 1 ->
  msteps ASEGS (mkst regs (0x82290 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 1))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' W C Ap.
  zstep F_82240 D_82240.
  zsd F_82244 D_82244 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_82248 D_82248 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zstep F_8224c D_8224c. zstep F_82250 D_82250.
  assert (C1 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) 0x146dd8 1 1) by (unfold apart in *; recell C).
  zlb F_82254 D_82254 0x146dd8 C1.
  zstep F_82258 D_82258.
  stepfence F_8225c D_8225c.
  zbft F_82260 D_82260.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  assert (Cs0 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 16) 8 (U (getr regs 8))) by (apply cell_Wn_hit; lia).
  zld F_82264 D_82264 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_82268 D_82268 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zstep F_8226c D_8226c.
  stepret F_82270 D_82270 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_lsan_off_fn : forall regs (M rom : word -> option byte) (raw : word) (tp off : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= off -> tp + off + 4 < 2 ^ 64 ->
  cellA M 0x13e528 8 off -> cellA M (tp + off) 4 0 ->
  msteps ASEGS (mkst regs (0xa8670 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw tp off H1 Hret H4 Htp Htp' Hoff Hoff' Cg Ct.
  zstep F_a8620 D_a8620.
  zld F_a8624 D_a8624 0x13e528 Cg.
  zstep F_a8628 D_a8628.
  zlw F_a862c D_a862c (tp + off) Ct.
  zstep F_a8630 D_a8630.
  stepret F_a8634 D_a8634 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_tsd_get_fn : forall regs (M rom : word -> option byte) (raw : word) (tp key tsd ctx : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 4096 <= tp -> tp + 4096 < 2 ^ 64 ->
  0 <= key < 128 -> 0 <= tsd -> tsd + 1024 < 2 ^ 64 -> 0 <= ctx < 2 ^ 64 ->
  cellA M 0x145960 1 1 -> cellA M 0x145964 4 key -> cellA M (tp - 88) 8 tsd -> cellA M (tsd + 8 * key) 8 ctx ->
  msteps ASEGS (mkst regs (0x7d110 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 ctx)) 11 (Z_to_bv 64 tsd)) raw M rom).
Proof.
  intros regs M rom raw tp key tsd ctx H1 Hret H4 Htp Htp' Hkey Htsd Htsd' Hctx Ci Ck Ctsd Cctx.
  zstep F_7d0c0 D_7d0c0. zstep F_7d0c4 D_7d0c4.
  zlbu F_7d0c8 D_7d0c8 0x145960 Ci.
  zbft F_7d0cc D_7d0cc.
  zlw F_7d0d0 D_7d0d0 0x145964 Ck.
  stepn F_7d0d4 D_7d0d4.
  zstep F_132818 D_132818.
  zld F_13281c D_13281c (tp - 88) Ctsd.
  zstep F_132820 D_132820.
  stepn F_132824 D_132824. rwH. rewrite (art_zb_srli_exact _ 29 (8 * key)) by lia.
  zstep F_132828 D_132828.
  zld F_13282c D_13282c (tsd + 8 * key) Cctx.
  stepret F_132830 D_132830 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Definition art_tsd (M : word -> option byte) (tp key tsd ctx t : Z) : Prop :=
  cellA M 0x145960 1 1 /\ cellA M 0x145964 4 key /\ cellA M (tp - 88) 8 tsd /\ cellA M (tsd + 8 * key) 8 ctx /\ cellA M (ctx + 152) 8 t
  /\ 4096 <= tp /\ tp + 4096 < 2 ^ 64 /\ 0 <= key < 128 /\ 0 <= tsd /\ tsd + 1024 < 2 ^ 64 /\ 4096 <= ctx /\ ctx + 4096 < 2 ^ 64 /\ 0 <= t < 2 ^ 64.

#[using="Type"] Lemma art_tsd_Wn : forall n M a v tp key tsd ctx t,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  apart a (Z.of_nat n) 0x145960 8 -> apart a (Z.of_nat n) (tp - 88) 8 -> apart a (Z.of_nat n) (tsd + 8 * key) 8 -> apart a (Z.of_nat n) (ctx + 152) 8 ->
  art_tsd M tp key tsd ctx t -> art_tsd (Wn n M a v) tp key tsd ctx t.
Proof.
  intros n M a v tp key tsd ctx t Ha Hn A1 A2 A3 A4 (C1 & C2 & C3 & C4 & C5 & R).
  unfold art_tsd. unfold apart in *.
  repeat split; try lia; (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia| assumption]).
Qed.

#[using="Type"] Lemma art_cur_thread_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> art_tsd M tp key tsd ctx t ->
  apart (sp - 16) 16 0x145960 8 -> apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x84a90 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 t)) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD A1 A2 A3 A4.
  pose proof (art_tsd_Wn 8 M (sp - 8) (U raw) tp key tsd ctx t ltac:(lia) ltac:(lia)
                ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) TSD)
    as (C1 & C2 & C3 & C4 & C5 & R).
  zstep F_84a40 D_84a40.
  zsd F_84a44 D_84a44 (sp - 8) (U raw) ltac:(rewok W).
  stepn F_84a48 D_84a48.
  zcall (art_tsd_get_fn _ _ _ _ tp key tsd ctx).
  zbft F_84a4c D_84a4c.
  zld F_84a50 D_84a50 (ctx + 152) C5.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_84a54 D_84a54 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_84a58 D_84a58.
  stepret F_84a5c D_84a5c raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_thread_stats_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 32 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 32) 32 0x145960 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x83c5c : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800))) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 24) 0x83c68) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD Ht A1 A2 A3 A4.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  zstep F_83c0c D_83c0c.
  zsd F_83c10 D_83c10 (sp - 8) (U raw) ltac:(rewok W).
  stepn F_83c14 D_83c14.
  zcall (art_cur_thread_fn _ _ _ _ (sp - 16) tp key tsd ctx t).
  { apply art_tsd_Wn; unfold apart in *; cbn; try lia. exact TSD. }
  zbft F_83c18 D_83c18.
  zstep F_83c1c D_83c1c. zstep F_83c20 D_83c20.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16 - 8) (U (Z_to_bv 64 0x83c68 : word))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  zld F_83c24 D_83c24 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_83c28 D_83c28.
  stepret F_83c2c D_83c2c raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_stack_top_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x84c54 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 top)) 11 (Z_to_bv 64 top)) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_84c04 D_84c04 (t + 40) C40.
  stepfence F_84c08 D_84c08.
  zbtk F_84c0c D_84c0c.
  zld F_84c44 D_84c44 (t + 8) C8.
  zld F_84c48 D_84c48 (t + 16) C16.
  zstep F_84c4c D_84c4c. zstep F_84c50 D_84c50.
  stepn F_84c54 D_84c54. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_l by lia | rewrite art_land_full_r by lia].
  stepret F_84c58 D_84c58 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_stack_bottom_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x84cac : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 bot)) 11 (Z_to_bv 64 (2 ^ 64 - 1))) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_84c5c D_84c5c (t + 40) C40.
  stepfence F_84c60 D_84c60.
  zbtk F_84c64 D_84c64.
  zld F_84c9c D_84c9c (t + 8) C8.
  zld F_84ca0 D_84ca0 (t + 16) C16.
  zstep F_84ca4 D_84ca4. zstep F_84ca8 D_84ca8.
  stepn F_84cac D_84cac. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_r by lia | rewrite art_land_full_l by lia].
  stepret F_84cb0 D_84cb0 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
