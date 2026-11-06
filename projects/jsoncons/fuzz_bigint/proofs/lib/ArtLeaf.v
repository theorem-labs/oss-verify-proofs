(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  As0_code_660d4_660ec As0_code_67d5c_67ecc As0_code_6bd64_6bdb8 As0_code_60f64_615b0 As0_code_8082c_80994 As0_code_66fe4_67084
  As0_code_8d3a8_8d3c0 As0_code_620e0_620f8 As0_code_cd550_cd56c As0_code_697e4_69804 As0_code_689b0_689e8 As0_code_699a8_69a58
  As0_code_6dfb8_6e12c.
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
  getr regs 1 = raw -> ret_ok raw -> cellA M 0xde818 1 1 ->
  msteps ASEGS (mkst regs (0x660d4 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_660d4 D_660d4.
  zlb F_660d8 D_660d8 0xde818 C.
  stepfence F_660dc D_660dc.
  zstep F_660e0 D_660e0.
  zstep F_660e4 D_660e4.
  stepret F_660e8 D_660e8 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_rss_limit_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x15fda2 1 0 ->
  msteps ASEGS (mkst regs (0x6bd9c : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_6bd9c D_6bd9c.
  zlb F_6bda0 D_6bda0 0x15fda2 C.
  zstep F_6bda4 D_6bda4.
  stepret F_6bda8 D_6bda8 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_may_return_null_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x15fda1 1 1 ->
  msteps ASEGS (mkst regs (0x6bd74 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_6bd74 D_6bd74.
  zlb F_6bd78 D_6bd78 0x15fda1 C.
  zstep F_6bd7c D_6bd7c.
  stepret F_6bd80 D_6bd80 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_can_poison_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0xdd39c 1 1 ->
  msteps ASEGS (mkst regs (0x60f64 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_60f64 D_60f64.
  zlb F_60f68 D_60f68 0xdd39c C.
  stepfence F_60f6c D_60f6c.
  zstep F_60f70 D_60f70.
  stepret F_60f74 D_60f74 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_malloc_ctx_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0xde83c 4 30 ->
  msteps ASEGS (mkst regs (0x67d6c : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 30)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_67d6c D_67d6c.
  zlw F_67d70 D_67d70 0xde83c C.
  stepfence F_67d74 D_67d74.
  stepret F_67d78 D_67d78 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_get_pc_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw ->
  msteps ASEGS (mkst regs (0x8082c : word) M rom) (mkst (regupd regs 10 raw) raw M rom).
Proof.
  intros regs M rom raw H1 Hret.
  zstep F_8082c D_8082c.
  stepret F_80830 D_80830 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_try_init_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> cellA M 0xde818 1 1 -> apart (sp - 16) 16 0xde818 1 ->
  msteps ASEGS (mkst regs (0x66fe4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 1))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' W C Ap.
  zstep F_66fe4 D_66fe4.
  zsd F_66fe8 D_66fe8 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_66fec D_66fec (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zstep F_66ff0 D_66ff0. zstep F_66ff4 D_66ff4.
  assert (C1 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) 0xde818 1 1) by (unfold apart in *; recell C).
  zlb F_66ff8 D_66ff8 0xde818 C1.
  zstep F_66ffc D_66ffc.
  stepfence F_67000 D_67000.
  zbft F_67004 D_67004.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  assert (Cs0 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 16) 8 (U (getr regs 8))) by (apply cell_Wn_hit; lia).
  zld F_67008 D_67008 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_6700c D_6700c (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zstep F_67010 D_67010.
  stepret F_67014 D_67014 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_lsan_off_fn : forall regs (M rom : word -> option byte) (raw : word) (tp off : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= off -> tp + off + 4 < 2 ^ 64 ->
  cellA M 0xd6510 8 off -> cellA M (tp + off) 4 0 ->
  msteps ASEGS (mkst regs (0x8d3a8 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw tp off H1 Hret H4 Htp Htp' Hoff Hoff' Cg Ct.
  zstep F_8d3a8 D_8d3a8.
  zld F_8d3ac D_8d3ac 0xd6510 Cg.
  zstep F_8d3b0 D_8d3b0.
  zlw F_8d3b4 D_8d3b4 (tp + off) Ct.
  zstep F_8d3b8 D_8d3b8.
  stepret F_8d3bc D_8d3bc raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_tsd_get_fn : forall regs (M rom : word -> option byte) (raw : word) (tp key tsd ctx : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 4096 <= tp -> tp + 4096 < 2 ^ 64 ->
  0 <= key < 128 -> 0 <= tsd -> tsd + 1024 < 2 ^ 64 -> 0 <= ctx < 2 ^ 64 ->
  cellA M 0xdd3a0 1 1 -> cellA M 0xdd3a4 4 key -> cellA M (tp - 88) 8 tsd -> cellA M (tsd + 8 * key) 8 ctx ->
  msteps ASEGS (mkst regs (0x620e0 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 ctx)) 11 (Z_to_bv 64 tsd)) raw M rom).
Proof.
  intros regs M rom raw tp key tsd ctx H1 Hret H4 Htp Htp' Hkey Htsd Htsd' Hctx Ci Ck Ctsd Cctx.
  zstep F_620e0 D_620e0. zstep F_620e4 D_620e4.
  zlbu F_620e8 D_620e8 0xdd3a0 Ci.
  zbft F_620ec D_620ec.
  zlw F_620f0 D_620f0 0xdd3a4 Ck.
  stepn F_620f4 D_620f4.
  zstep F_cd550 D_cd550.
  zld F_cd554 D_cd554 (tp - 88) Ctsd.
  zstep F_cd558 D_cd558.
  stepn F_cd55c D_cd55c. rwH. rewrite (art_zb_srli_exact _ 29 (8 * key)) by lia.
  zstep F_cd560 D_cd560.
  zld F_cd564 D_cd564 (tsd + 8 * key) Cctx.
  stepret F_cd568 D_cd568 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Definition art_tsd (M : word -> option byte) (tp key tsd ctx t : Z) : Prop :=
  cellA M 0xdd3a0 1 1 /\ cellA M 0xdd3a4 4 key /\ cellA M (tp - 88) 8 tsd /\ cellA M (tsd + 8 * key) 8 ctx /\ cellA M (ctx + 152) 8 t
  /\ 4096 <= tp /\ tp + 4096 < 2 ^ 64 /\ 0 <= key < 128 /\ 0 <= tsd /\ tsd + 1024 < 2 ^ 64 /\ 4096 <= ctx /\ ctx + 4096 < 2 ^ 64 /\ 0 <= t < 2 ^ 64.

Lemma art_tsd_Wn : forall n M a v tp key tsd ctx t,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  apart a (Z.of_nat n) 0xdd3a0 8 -> apart a (Z.of_nat n) (tp - 88) 8 -> apart a (Z.of_nat n) (tsd + 8 * key) 8 -> apart a (Z.of_nat n) (ctx + 152) 8 ->
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
  apart (sp - 16) 16 0xdd3a0 8 -> apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x697e4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 t)) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD A1 A2 A3 A4.
  pose proof (art_tsd_Wn 8 M (sp - 8) (U raw) tp key tsd ctx t ltac:(lia) ltac:(lia)
                ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) TSD)
    as (C1 & C2 & C3 & C4 & C5 & R).
  zstep F_697e4 D_697e4.
  zsd F_697e8 D_697e8 (sp - 8) (U raw) ltac:(rewok W).
  stepn F_697ec D_697ec.
  zcall (art_tsd_get_fn _ _ _ _ tp key tsd ctx).
  zbft F_697f0 D_697f0.
  zld F_697f4 D_697f4 (ctx + 152) C5.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_697f8 D_697f8 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_697fc D_697fc.
  stepret F_69800 D_69800 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_thread_stats_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 32 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 32) 32 0xdd3a0 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x689b0 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800))) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 24) 0x689bc) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD Ht A1 A2 A3 A4.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  zstep F_689b0 D_689b0.
  zsd F_689b4 D_689b4 (sp - 8) (U raw) ltac:(rewok W).
  stepn F_689b8 D_689b8.
  zcall (art_cur_thread_fn _ _ _ _ (sp - 16) tp key tsd ctx t).
  { apply art_tsd_Wn; unfold apart in *; cbn; try lia. exact TSD. }
  zbft F_689bc D_689bc.
  zstep F_689c0 D_689c0. zstep F_689c4 D_689c4.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16 - 8) (U (Z_to_bv 64 0x689bc : word))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  zld F_689c8 D_689c8 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_689cc D_689cc.
  stepret F_689d0 D_689d0 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_stack_top_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x699a8 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 top)) 11 (Z_to_bv 64 top)) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_699a8 D_699a8 (t + 40) C40.
  stepfence F_699ac D_699ac.
  zbtk F_699b0 D_699b0.
  zld F_699e8 D_699e8 (t + 8) C8.
  zld F_699ec D_699ec (t + 16) C16.
  zstep F_699f0 D_699f0. zstep F_699f4 D_699f4.
  stepn F_699f8 D_699f8. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_l by lia | rewrite art_land_full_r by lia].
  stepret F_699fc D_699fc raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_stack_bottom_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x69a00 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 bot)) 11 (Z_to_bv 64 (2 ^ 64 - 1))) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_69a00 D_69a00 (t + 40) C40.
  stepfence F_69a04 D_69a04.
  zbtk F_69a08 D_69a08.
  zld F_69a40 D_69a40 (t + 8) C8.
  zld F_69a44 D_69a44 (t + 16) C16.
  zstep F_69a48 D_69a48. zstep F_69a4c D_69a4c.
  stepn F_69a50 D_69a50. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_r by lia | rewrite art_land_full_l by lia].
  stepret F_69a54 D_69a54 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
