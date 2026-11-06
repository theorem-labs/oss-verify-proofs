(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA
L5Defs L5Core L5CoreKit L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa
PmAEmbKit PmAEmmE PmAEmmF PmAEmmGStmts PmAEmmG1 PmAEmmG2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMAEM.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Theorem push_ms_ok : PMA.opnew_spec L ar HI -> PMA.opdel_spec L ar HI -> PMA.push_ms_spec L ar HI.
Proof.
intros NEW DEL. unfold PMA.push_ms_spec, PMSAX.push_ms_spec, PMSAX.push_spec_at.
intros fx R M model K LBX FF LK Aw cr v b k stk own c sp r HH AM K0 ENT FRS A10 AOV V8 ACCV PRE FULL K10 CELLS CRED KONT.
cbn [paa_esp_ms PmLayoutA.AADDR_A] in *.
destruct CELLS as (p1 & p2 & m & n & A11 & A12 & P14 & P24 & SP1 & SP2 & AG1 & AG2 & SB1 & SB2 & U1 & U2 & RM & RN & ->).
destruct PRE as [(V0 & V8' & V16 & -> & -> & -> & ->) | (VEC & ->)].
-
cbn [app] in HH.
apply (PMAEME.empty L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr v sp r p1 p2 m n HH AM K0 ENT A10 AOV V8 ACCV V0 V8' V16
A11 A12 P14 P24 SB1 SB2 AG1 AG2 U1 U2 RM RN (CRED (or_introl eq_refl))).
intros fx' R' M' model' LK' Aw' b' RP VEC' ACC' HP MRT INC IA AM' HH'.
apply (KONT fx' R' M' model' LK' Aw' b' 0 (adebit L cr 32) RP VEC' ACC'); try assumption.
right. split; [left; reflexivity|]. split; reflexivity.
-
assert (BIN : In (b, 32 * 2 ^ k) (PM.vec_own b k ++ LBX)) by (left; reflexivity).
destruct (PMAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (32 * 2 ^ k) HH BIN) as (Bq0 & _).
assert (Bnz : Z.eqb b 0 = false) by (apply Z.eqb_neq; lia).
rewrite Bnz in CRED.
assert (LENk : Z.of_nat (length stk) <= 2 ^ k) by (destruct VEC as (_ & _ & _ & _ & X & _); exact X).
destruct (Z_lt_le_dec (Z.of_nat (length stk)) (2 ^ k)) as [LT | GE].
+
apply (PMAEMF.fast L ar C HI LY HIok EXT fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 m n HH AM K0 ENT A10 AOV V8 ACCV VEC LT
A11 A12 P14 P24 SB1 SB2 AG1 AG2 U1 U2 RM RN).
intros fx' R' M' model' LK' Aw' RP VEC' ACC' HP MRT INC IA AM' HH'.
apply (KONT fx' R' M' model' LK' Aw' b k cr RP VEC' ACC'); try assumption.
left. split; [unfold PM.vec_own; discriminate|]. split; [exact LT|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
+
assert (EQ : Z.of_nat (length stk) = 2 ^ k) by lia.
assert (Kle : k <= 10) by (apply K10; right; exact EQ).
assert (Kr : 0 <= k <= 10) by (destruct VEC as (_ & _ & _ & X & _); lia).
pose proof (CRED (or_intror EQ)) as CR.
pose proof ENT as (_ & _ & _ & _ & _ & ASTK & _).
assert (RP1 : 0 <= p1 < 2 ^ 47).
{ destruct (PMAEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) v p1 4 HH
ASTK ltac:(unfold PMSPA.pm_scr; lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & _). lia. }
assert (RP2 : 0 <= p2 < 2 ^ 47).
{ destruct (PMAEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) v p2 8 HH
ASTK ltac:(unfold PMSPA.pm_scr; lia) AG2 ltac:(lia)) as (Pb0 & Pb1 & _). lia. }
apply (PMAEMG1.grow1 L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 m n HH AM K0 ENT A10 AOV V8 ACCV VEC EQ Kle
A11 A12 P14 P24 SB1 SB2 AG1 AG2 U1 U2 RM RN CR).
intros fx6 R6 M6 model6 Aw6 B MID.
apply (PMAEMG2.grow2 L ar C HI LY HIok EXT DEL fx6 R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 m n B R6 M6 model6 Aw6 HH K0 ENT AOV V8 EQ Kr
RP1 RP2 MID).
intros fx' R' M' model' LK' Aw' b' RP VEC' ACC' HP MRT INC IA AM' HH'.
apply (KONT fx' R' M' model' LK' Aw' b' (k + 1) (adebit L cr (32 * 2 ^ (k + 1))) RP VEC' ACC'); try assumption.
right. split; [right; exact EQ|]. rewrite Bnz. split; reflexivity.
Qed.
End WithHeap.
End PMAEM.
