(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  Pm4_code_83000_84000 Pm4_code_84000_85000 Pm4_code_88000_89000 Pm4_code_89000_8a000 Pm4_code_8a000_8b000 Pm4_code_8b000_8c000 Pm4_code_8c000_8d000 Pm4_code_8e000_8f000 Pm4_code_a2000_a3000 Pm4_code_af000_b0000 Pm4_code_155000_156000               
       
  .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_asan_inited_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x16abd8 1 1 ->
  msteps ASEGS (mkst regs (0x88780 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_88730 D_88730.
  zlb F_88734 D_88734 0x16abd8 C.
  stepfence F_88738 D_88738.
  zstep F_8873c D_8873c.
  zstep F_88740 D_88740.
  stepret F_88744 D_88744 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_rss_limit_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1ec162 1 0 ->
  msteps ASEGS (mkst regs (0x8e448 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_8e3f8 D_8e3f8.
  zlb F_8e3fc D_8e3fc 0x1ec162 C.
  zstep F_8e400 D_8e400.
  stepret F_8e404 D_8e404 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_may_return_null_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1ec161 1 1 ->
  msteps ASEGS (mkst regs (0x8e420 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_8e3d0 D_8e3d0.
  zlb F_8e3d4 D_8e3d4 0x1ec161 C.
  zstep F_8e3d8 D_8e3d8.
  stepret F_8e3dc D_8e3dc raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_can_poison_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x16975c 1 1 ->
  msteps ASEGS (mkst regs (0x830d0 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_83080 D_83080.
  zlb F_83084 D_83084 0x16975c C.
  stepfence F_83088 D_83088.
  zstep F_8308c D_8308c.
  stepret F_83090 D_83090 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_malloc_ctx_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x16abfc 4 30 ->
  msteps ASEGS (mkst regs (0x8a418 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 30)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_8a3c8 D_8a3c8.
  zlw F_8a3cc D_8a3cc 0x16abfc C.
  stepfence F_8a3d0 D_8a3d0.
  stepret F_8a3d4 D_8a3d4 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_get_pc_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw ->
  msteps ASEGS (mkst regs (0xa2ef4 : word) M rom) (mkst (regupd regs 10 raw) raw M rom).
Proof.
  intros regs M rom raw H1 Hret.
  zstep F_a2ea4 D_a2ea4.
  stepret F_a2ea8 D_a2ea8 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_try_init_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> cellA M 0x16abd8 1 1 -> apart (sp - 16) 16 0x16abd8 1 ->
  msteps ASEGS (mkst regs (0x89690 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 1))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' W C Ap.
  zstep F_89640 D_89640.
  zsd F_89644 D_89644 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_89648 D_89648 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zstep F_8964c D_8964c. zstep F_89650 D_89650.
  assert (C1 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) 0x16abd8 1 1) by (unfold apart in *; recell C).
  zlb F_89654 D_89654 0x16abd8 C1.
  zstep F_89658 D_89658.
  stepfence F_8965c D_8965c.
  zbft F_89660 D_89660.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  assert (Cs0 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 16) 8 (U (getr regs 8))) by (apply cell_Wn_hit; lia).
  zld F_89664 D_89664 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_89668 D_89668 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zstep F_8966c D_8966c.
  stepret F_89670 D_89670 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_lsan_off_fn : forall regs (M rom : word -> option byte) (raw : word) (tp off : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= off -> tp + off + 4 < 2 ^ 64 ->
  cellA M 0x161878 8 off -> cellA M (tp + off) 4 0 ->
  msteps ASEGS (mkst regs (0xafa70 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw tp off H1 Hret H4 Htp Htp' Hoff Hoff' Cg Ct.
  zstep F_afa20 D_afa20.
  zld F_afa24 D_afa24 0x161878 Cg.
  zstep F_afa28 D_afa28.
  zlw F_afa2c D_afa2c (tp + off) Ct.
  zstep F_afa30 D_afa30.
  stepret F_afa34 D_afa34 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_tsd_get_fn : forall regs (M rom : word -> option byte) (raw : word) (tp key tsd ctx : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 4096 <= tp -> tp + 4096 < 2 ^ 64 ->
  0 <= key < 128 -> 0 <= tsd -> tsd + 1024 < 2 ^ 64 -> 0 <= ctx < 2 ^ 64 ->
  cellA M 0x169760 1 1 -> cellA M 0x169764 4 key -> cellA M (tp - 88) 8 tsd -> cellA M (tsd + 8 * key) 8 ctx ->
  msteps ASEGS (mkst regs (0x84510 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 ctx)) 11 (Z_to_bv 64 tsd)) raw M rom).
Proof.
  intros regs M rom raw tp key tsd ctx H1 Hret H4 Htp Htp' Hkey Htsd Htsd' Hctx Ci Ck Ctsd Cctx.
  zstep F_844c0 D_844c0. zstep F_844c4 D_844c4.
  zlbu F_844c8 D_844c8 0x169760 Ci.
  zbft F_844cc D_844cc.
  zlw F_844d0 D_844d0 0x169764 Ck.
  stepn F_844d4 D_844d4.
  zstep F_155688 D_155688.
  zld F_15568c D_15568c (tp - 88) Ctsd.
  zstep F_155690 D_155690.
  stepn F_155694 D_155694. rwH. rewrite (art_zb_srli_exact _ 29 (8 * key)) by lia.
  zstep F_155698 D_155698.
  zld F_15569c D_15569c (tsd + 8 * key) Cctx.
  stepret F_1556a0 D_1556a0 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Definition art_tsd (M : word -> option byte) (tp key tsd ctx t : Z) : Prop :=
  cellA M 0x169760 1 1 /\ cellA M 0x169764 4 key /\ cellA M (tp - 88) 8 tsd /\ cellA M (tsd + 8 * key) 8 ctx /\ cellA M (ctx + 152) 8 t
  /\ 4096 <= tp /\ tp + 4096 < 2 ^ 64 /\ 0 <= key < 128 /\ 0 <= tsd /\ tsd + 1024 < 2 ^ 64 /\ 4096 <= ctx /\ ctx + 4096 < 2 ^ 64 /\ 0 <= t < 2 ^ 64.

Lemma art_tsd_Wn : forall n M a v tp key tsd ctx t,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  apart a (Z.of_nat n) 0x169760 8 -> apart a (Z.of_nat n) (tp - 88) 8 -> apart a (Z.of_nat n) (tsd + 8 * key) 8 -> apart a (Z.of_nat n) (ctx + 152) 8 ->
  art_tsd M tp key tsd ctx t -> art_tsd (Wn n M a v) tp key tsd ctx t.
Proof.
  intros n M a v tp key tsd ctx t Ha Hn A1 A2 A3 A4 (C1 & C2 & C3 & C4 & C5 & R).
  unfold art_tsd. unfold apart in *.
  repeat split; try lia; (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia| assumption]).
Qed.

(* [comment removed for export] *)
Lemma art_cur_thread_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> art_tsd M tp key tsd ctx t ->
  apart (sp - 16) 16 0x169760 8 -> apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x8be90 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 t)) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD A1 A2 A3 A4.
  pose proof (art_tsd_Wn 8 M (sp - 8) (U raw) tp key tsd ctx t ltac:(lia) ltac:(lia)
                ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) TSD)
    as (C1 & C2 & C3 & C4 & C5 & R).
  zstep F_8be40 D_8be40.
  zsd F_8be44 D_8be44 (sp - 8) (U raw) ltac:(rewok W).
  stepn F_8be48 D_8be48.
  zcall (art_tsd_get_fn _ _ _ _ tp key tsd ctx).
  zbft F_8be4c D_8be4c.
  zld F_8be50 D_8be50 (ctx + 152) C5.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_8be54 D_8be54 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_8be58 D_8be58.
  stepret F_8be5c D_8be5c raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_thread_stats_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 32 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 32) 32 0x169760 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x8b05c : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800))) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 24) 0x8b068) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD Ht A1 A2 A3 A4.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  zstep F_8b00c D_8b00c.
  zsd F_8b010 D_8b010 (sp - 8) (U raw) ltac:(rewok W).
  stepn F_8b014 D_8b014.
  zcall (art_cur_thread_fn _ _ _ _ (sp - 16) tp key tsd ctx t).
  { apply art_tsd_Wn; unfold apart in *; cbn; try lia. exact TSD. }
  zbft F_8b018 D_8b018.
  zstep F_8b01c D_8b01c. zstep F_8b020 D_8b020.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16 - 8) (U (Z_to_bv 64 0x8b068 : word))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  zld F_8b024 D_8b024 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_8b028 D_8b028.
  stepret F_8b02c D_8b02c raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_stack_top_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x8c054 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 top)) 11 (Z_to_bv 64 top)) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_8c004 D_8c004 (t + 40) C40.
  stepfence F_8c008 D_8c008.
  zbtk F_8c00c D_8c00c.
  zld F_8c044 D_8c044 (t + 8) C8.
  zld F_8c048 D_8c048 (t + 16) C16.
  zstep F_8c04c D_8c04c. zstep F_8c050 D_8c050.
  stepn F_8c054 D_8c054. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_l by lia | rewrite art_land_full_r by lia].
  stepret F_8c058 D_8c058 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_stack_bottom_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x8c0ac : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 bot)) 11 (Z_to_bv 64 (2 ^ 64 - 1))) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_8c05c D_8c05c (t + 40) C40.
  stepfence F_8c060 D_8c060.
  zbtk F_8c064 D_8c064.
  zld F_8c09c D_8c09c (t + 8) C8.
  zld F_8c0a0 D_8c0a0 (t + 16) C16.
  zstep F_8c0a4 D_8c0a4. zstep F_8c0a8 D_8c0a8.
  stepn F_8c0ac D_8c0ac. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_r by lia | rewrite art_land_full_l by lia].
  stepret F_8c0b0 D_8c0b0 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
