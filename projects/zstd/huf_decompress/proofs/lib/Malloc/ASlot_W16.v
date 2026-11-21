(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (land_4095_wrap, land_4095_wrap20, land_4095_word and 4 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W16 () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr06K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op203C45stdpp9bitvector;definitions7bv_wrapK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega6VarMap1t03C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W16?land_4095_rangeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Ltac bool_hyp b K := destruct b; cbn in K; first [reflexivity | discriminate | congruence | (exfalso; apply K; reflexivity)].

Section CANSEC2. Context {rc : runConstT}.
Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.
End MMC.


End CANSEC2.
