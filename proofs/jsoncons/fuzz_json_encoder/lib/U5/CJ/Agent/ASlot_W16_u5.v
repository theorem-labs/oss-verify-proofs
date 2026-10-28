(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_syscalls_u5 MallocRep_u5 F_malloc_free_u5 F_malloc_fast_u5 F_malloc_entry_u5 F_malloc_enframe_u5 MallocTree_u5 MallocKit_A_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import MallocKit_AB_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import Malloc_fp_u5 MallocKit_A2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import MallocKit_A3_u5.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mm_usage1 (st1 : mstate) (sc usage0 : Z) : Z :=
  if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0.

Definition mm_cnt_red (sc size cnt usage1 : Z) (nosmall : bool) : Z :=
  if (usage1 <? 4 * cnt) && negb nosmall then
    if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
    else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
    else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
    else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
    else cnt
  else cnt.

Definition mm_small (size req usage1 cnt needed : Z) : Z * Z :=
  let req := round_up_pg (req + IB + UNIT) in
  if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed).

Definition mm_final (size req usage1 cnt : Z) (nosmall : bool) : Z * Z :=
  let needed := round_up_pg (size * cnt + UNIT) in
  if negb nosmall && (cnt <=? 7) then mm_small size req usage1 cnt needed else (cnt, needed).

(* [comment removed for export] *)
Lemma land_4095_wrap x : 0 <= x -> x + 16 <= 2^64 ->
  Z.land (18446744073709551600 - x) 4095 = Z.land (- (x + 16)) 4095.
Proof.
  intros H0 H1. change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
  replace (18446744073709551600 - x) with (- (x + 16) + 2^52 * 2^12) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma land_4095_wrap20 x : 0 <= x -> x + 20 <= 2^64 ->
  Z.land (18446744073709551596 - x) 4095 = Z.land (- (x + 20)) 4095.
Proof.
  intros H0 H1. change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
  replace (18446744073709551596 - x) with (- (x + 20) + 2^52 * 2^12) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma land_4095_word z : Z.land (bv_unsigned (Z_to_bv 64 z)) 4095 = Z.land z 4095.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^52 * 2^12).
  change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
  apply Z.mod_mod_divide. exists (2^52). reflexivity.
Qed.

Lemma land3_range x : 0 <= Z.land x 3 <= 3.
Proof. change (Z.land x 3) with (Z.land x (Z.ones 2)). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound x (2^2) ltac:(lia)). lia. Qed.

Lemma land_4095_range y : 0 <= Z.land y 4095 < 4096.
Proof. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma round_up_pg_alt x : Z.land (- x) 4095 + x = round_up_pg x.
Proof. unfold round_up_pg. change (PGSZ - 1) with 4095. lia. Qed.

Lemma round_up_pg_range x : 0 <= x -> x <= round_up_pg x < x + 4096.
Proof. intros. unfold round_up_pg. change (PGSZ - 1) with 4095. pose proof (land_4095_range (- x)). lia. Qed.
End CEIL_WRAP_1.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac bool_hyp b K := destruct b; cbn in K; first [reflexivity | discriminate | congruence | (exfalso; apply K; reflexivity)].
Section CEIL_WRAP_2.
Context {RUNp : RunP}.


Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.

Definition mmc_post (ra sp gp tp t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (res : Z * Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t4' a0' a1' a2' a3' a4' a5' a6' t5' : word),
    ms' = MS (mkR ra sp gp tp t0' (wz size) t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4' t5' t6)
             F (Z_to_bv 64 0x16914) fc None m (seg_rom asegs)
    /\ a1' = wz (snd res) /\ a6' = wz (fst res).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End MMC.
End CEIL_WRAP_2.

