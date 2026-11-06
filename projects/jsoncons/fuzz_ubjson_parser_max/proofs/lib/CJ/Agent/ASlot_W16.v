(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_A3.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_W16 () := ([""; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1and"; "1eq"; "2Z"; "3round_up_pg"; "4add"; "4land"; "4le"; "4lt"; "4opp"; "4pow"; "4sub"; "5Z_to_bv"; "5bv_unsigned"; "0x"; "0y"; "0z"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
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
Lemma land_4095_wrap : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W16 "N'2&6zr1%3221&4r2+@%3221&9+2+R0%3221%<251'1&5&:+_ooooooooooo@r3%3221+SoO%6221&8%B25@%211%:215%<3J51p0>1p0H1pLM1").
Proof. intros x.
intros H0 H1. change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
replace (18446744073709551600 - x) with (- (x + 16) + 2^52 * 2^12) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma land_4095_wrap20 : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W16 "N'2&6zr1%3221&4r2+D%3221&9+2+R0%3221%<251'1&5&:+_ooooooooooo<r3%3221+SoO%6221&8%B25@%211%:215%<3J51p0>1p0H1pLM1").
Proof. intros x.
intros H0 H1. change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
replace (18446744073709551596 - x) with (- (x + 20) + 2^52 * 2^12) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma land_4095_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W16 ">'2'1&5&<yR0&;r1%2231%5241+SoO%8221%9252%;3<21pQ0=1").
Proof. intros z.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^52 * 2^12).
change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
apply Z.mod_mod_divide. exists (2^52). reflexivity.
Qed.
Lemma land3_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W16 "<'2'0&6z&5r1+3%3221%6251%7223%9221pL;1").
Proof. intros x. change (Z.land x 3) with (Z.land x (Z.ones 2)). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound x (2^2) ltac:(lia)). lia. Qed.
Lemma land_4095_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W16 ">'2'0&6z&5r1+SoO%3221%6251&7+TP0%2241%;241pN=1").
Proof. intros y. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma round_up_pg_alt : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W16 ">'2'1&4&5&8r1%211+SoO%5221%7214&3%116%;3<31pL=1").
Proof. intros x. unfold round_up_pg. change (PGSZ - 1) with 4095. lia. Qed.
Lemma round_up_pg_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W16 "B'2&6zr1%3221'0r2&3%112%8231&7&4+TP0%2271%4261%:261p0<1pLA1").
Proof. intros x. intros. unfold round_up_pg. change (PGSZ - 1) with 4095. pose proof (land_4095_range (- x)). lia. Qed.
End CEIL_WRAP_1.
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
F (Z_to_bv 64 0x1675c) fc None m (seg_rom asegs)
/\ a1' = wz (snd res) /\ a6' = wz (fst res).
End MMC.
End CEIL_WRAP_2.
