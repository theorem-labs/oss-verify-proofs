(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanSoundSums
     L5Defs L5Core L5CoreKit L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8 PnModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAX_b PnSpecsAa_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXR_b PnAEmbKit_b PnAEmbCGStmts_b PnAEmbCG1_b PnAEmbCG2_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNAEC.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Lemma u32_of_defined (M : word -> option byte) a : 0 <= a -> a + 4 <= 2 ^ 64 -> L5.defined M a 4 -> exists w, 0 <= w < 2 ^ 32 /\ L5.u32_at RSEGS M a w.
Proof.
  intros Ha Hn D. destruct (PMCG.rdn_some RSEGS M 4%nat a Ha ltac:(cbn; lia) ltac:(intros i Hi; apply D; cbn in Hi; lia)) as (bs & E & Hl).
  exists (bytes_le_to_Z bs). pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. cbn in Hb.
  split; [lia|]. unfold L5.u32_at. rewrite E. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl| lia].
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.

Theorem push_cont_slow_ok : PMA.opnew_spec L ar HI -> PMA.opdel_spec L ar HI -> PNSAXR.push_cont_slow_spec RSEGS PMA.AD L ar HI 0xb2758.
Proof.
  intros NEW DEL. unfold PNSAXR.push_cont_slow_spec. unfold PNM.BSZ.
  intros fx R M model K LBX FF LK Aw cr v b k stk own det sp r HH AM K0 ENT FRS A10 AOV V8 ACCV PRE DOM FOE K10 BASE CELLS CRED KONT.
  destruct det as (m & q).
  destruct CELLS as (p1 & p2 & p3 & A11 & A12 & A13 & (P14 & AC1 & AG1 & SB1) & (P24 & AC2 & AG2 & SB2) & (P38 & AC3 & AG3 & SB3) & U1 & D2 & U3 & RM & RQ).
  cbn [fst snd] in U1, U3, RM, RQ. unfold PNSAX.mk_cont in KONT. cbn [fst snd] in KONT.
  unfold PNSAX.dom_cont in DOM.
  destruct PRE as [(V0 & V8' & V16 & -> & -> & -> & ->) | (VEC & ->)]; [exfalso; apply DOM; reflexivity|].
  pose proof ENT as (_ & _ & _ & _ & _ & ASTK & _).
  assert (RP1 : 0 <= p1 < 2 ^ 47).
  { destruct (PNAEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) v p1 4 HH ASTK ltac:(unfold PMSPA.pm_scr; lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & _). lia. }
  assert (RP2 : 0 <= p2 < 2 ^ 47).
  { destruct (PNAEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) v p2 4 HH ASTK ltac:(unfold PMSPA.pm_scr; lia) AG2 ltac:(lia)) as (Pb0 & Pb1 & _). lia. }
  assert (RP3 : 0 <= p3 < 2 ^ 47).
  { destruct (PNAEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) v p3 8 HH ASTK ltac:(unfold PMSPA.pm_scr; lia) AG3 ltac:(lia)) as (Pc0 & Pc1 & _). lia. }
  (* [comment removed for export] *)
  destruct (u32_of_defined M p2 ltac:(lia) ltac:(lia) D2) as (n & RN & U2).
  assert (BIN : In (b, 40 * 2 ^ k) (PNM.bvec_own b k ++ LBX)) by (left; reflexivity).
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (40 * 2 ^ k) HH BIN) as (Bq0 & _).
  assert (Bnz : Z.eqb b 0 = false) by (apply Z.eqb_neq; lia).
  unfold PNSAX.k_next in CRED, KONT. rewrite Bnz in CRED, KONT.
  assert (LENk : Z.of_nat (length stk) <= 2 ^ k) by (destruct VEC as (_ & _ & _ & _ & X & _); exact X).
  assert (EQ : Z.of_nat (length stk) = 2 ^ k) by (unfold PNSAX.full_or_empty in FOE; destruct FOE as [X|X]; [exfalso; exact (DOM X)| exact X]).
  + (* [comment removed for export] *)
    assert (Kle : k <= 10) by exact K10.
    assert (Kr : 0 <= k <= 10) by (destruct VEC as (_ & _ & _ & X & _); lia).
    pose proof CRED as CR.
    apply (PNAECG1.grow1 L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n q HH AM K0 ENT A10 AOV V8 ACCV VEC EQ Kle
             A11 A12 A13 P14 P24 P38 SB1 SB2 SB3 AG1 AG2 AG3 U1 U2 U3 RM RN RQ CR BASE).
    intros fx6 R6 M6 model6 Aw6 B MID.
    apply (PNAECG2.grow2 L ar C HI LY HIok EXT DEL fx6 R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m q B R6 M6 model6 Aw6 HH K0 ENT AOV V8 EQ Kr
             RP1 RP2 RP3 BASE MID).
    intros fx' R' M' model' LK' Aw' b' lenv RP LV X10 B4 B47 VEC' DJ ACC' BASE' HP MRT INC IA AM' HH'.
    apply (KONT fx' R' M' model' LK' Aw' b' lenv); assumption.
Qed.
End WithHeap.
End PNAEC.
