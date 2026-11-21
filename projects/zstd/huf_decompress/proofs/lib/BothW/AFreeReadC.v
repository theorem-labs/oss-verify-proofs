(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (3 recorded proofs replaced by written proofs (other_key, freed_vs_slot24, read_dkC)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes AQConst ARep ARepQ ARepQP ARepFrame ARepKit ALayout AHeapP
     AModelFacts AFreeModel AFreeRep AFreeGeo F_afree_tail F_afree_icpt.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import AFreeRead F_afreeC_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFreeReadC () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2hdC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qcoupledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4qnumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4q_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6aintalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7aqcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9aq_tcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5q_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ@aquar_glob_constC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5BothW7AQConst9AQ_GCACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead4HCKRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead9other_keyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead?freed_vs_slot24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead<qfirst_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead;qlast_casesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5BothW5ARepQ5qlastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ;abatch_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notI47Corelib4Init5Logic2or00C59OSSVerify5KrLib5BothW<F_afree_tail4ek_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead4g_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5BothW5ARepQ6qfirstC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead3fhmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib5BothW5ARepQ9qentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qentriesC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib5BothW5ARepQ9qprim_idsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_pendC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic3iffK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib5BothW5ARepQ8AQUAR_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8abatchesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=batches_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib5BothW6ARepQP@batches_bytes_lbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib5BothW7ALayout9alayout_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7qb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead9bslot_geoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib5BothW:AFreeReadC<qfirst_casesC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5BothW:AFreeReadC;qlast_casesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4ListCapp_removelast_lastC46Stdlib5Lists4List:removelastC47Corelib4Init5Logic9False_indC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Peano2ltC46Stdlib5Lists4List4lastC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega7Formula01I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW5ARepQ;abatches_toC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6qaddrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQP?abatches_to_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ<abatch_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7b_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qb_ksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qhdrsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib5BothW6ARepQP:qlast_app1C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib5BothW9AFreeRead:bslot_busyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib5BothW:AFreeReadC9other_keyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeReadC?freed_vs_slot24C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8in_splitC46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib5BothW9AFreeReadBbslots_nodup_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>slots_disjointC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapC47Corelib4Init5Logic8iff_reflC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init5Logic3and01C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K59OSSVerify5KrLib5BothW<F_afree_tail3gqd01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_afreeC_iface7dk_preCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_icpt7dk_sepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail5g_lstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail7dk_glstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail7g_drainC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead;bslot_rangeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib5BothW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeReadC2WFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeReadC2CPC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib5BothW9AFreeRead;dummy_batchC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW<F_afree_tail3gqd00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:AFreeReadC4HCKRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst6AQ_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AQ_MUTEXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib5BothW9AFreeRead8dummy_qbC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_BATCHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQP@size_of_class_24C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section VariantC.
Variables (H : aholes) (L : alayout) (st : astate) (X : aconc) (Q : qconc) (m : amem) (RNG : footprint)
          (s0 : bstate) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Hypothesis ALO : alayout_ok L.
Hypothesis ARNG : arng L RNG st.
Hypothesis AR : AREP H L st X m.
Hypothesis AQ : AQUAR_at L st X Q m.
Hypothesis XB : x_busy X = l1 ++ bany s0 c k n b1 ctx :: l2.
Hypothesis NBT : s0 <> BBatch.
Hypothesis N1 : 1 <= n.

Lemma WF : awf L st X.
Proof.
ltac2:(KReplay.run1 (kr_t_AFreeReadC ()) ["CANSEC1"; "VariantC"] "h01cp;4p;2p;3p;1p;5p10000p4p710p1000Mp4p710p8p1000ip4p70R0p1001`p4p710p8P0p1002:p4p710p8P0p1002Qp4p710p8P0p1002op4p710p8g003Lj4DTg004?j2CTg0056j33Tg005oj42Tg006fj1BTg007Dj29Tg007`j24Tg008<j21Tg008Wj45Tg009Tj56Tg00:Nj57Tg00;Dj58Tg00<@j5ATg00=7j5:Tg00=mj3;Tg00>ej1<Tg00?[j1=Tg00@Sj4>Tg00APj1?Tg00BHj3@Tf2f1R0f0R1'1'1p=0p,2rcp,1LR2p,2stR3p,1XR4CDp,1mR5,C2A3235P2P3P4P5C2g00BcR6g00CA#B/91g00Cf,41'1R1P2P3P5P0C5P2P3P4P5P0D6P2P3P4P5P0D7P2P3P4P5P0D8'130[]0p,1HR7P2P3P4P5DAP7P2P3P4P5D:A;725%<5%=5P2P3P5P0C>\1^06%?53030303030p,2AR3@o"). Qed.
Lemma CP : qcoupled L st X Q.
Proof.
ltac2:(KReplay.run1 (kr_t_AFreeReadC ()) ["CANSEC1"; "VariantC"] "p;4p;1p;2p;6p;3p10000p4p710p1000Mp4p710p8p1000ip4p70R0p1001`p4p710p8P0p1002:p4p710p8P0p1002Qp4p710p8P0p1002op4p710p8g00Dfj4?Tg00E_j1>Tg00FTj14Tg00GIj23Tg008<j21Tg00H@j1;Tg00I:j1:Tg00J1j15Tg00K1j62Tg00Kij16Tg00Lej17Tg00M^j18Tg00NTj19Tg00OSj1=Tg00PTj30Tg00BHj3<Tp,1LR0p,2stR1p,1Xp,1QR2C?R3%>1R4%42p,1mR5'3R61134R4P0P5g00Po%;1%:2%51E2R31164R4P0P5%60%71%82%91E2R11134R4%=51114p,2AQ303030303<o"). Qed.
Lemma HCKR : 1 <= c < K_NUM_CLASSES /\ 0 <= k < ndist st c.
Proof.
ltac2:(KReplay.run1 (kr_t_AFreeReadC ()) ["CANSEC1"; "VariantC"] "p;@p10000p4p710p1000Mp4p710p8p1000ip4p70R0p1001`p4p710p8P0p1002:p4p710p8P0p1002Qp4p710p8P0p1002op4p710p8g00Qkl@0Tp,2rcp,1Hp,1Lp,2stp,1Xp,1mp,2s0p,1cp,1kp,1np,2b1p,3ctxp,2l1p,2l2p,2ARp,2XBM@0o"). Qed.
Lemma other_key : forall y, In y (x_busy X) -> xb_st y <> s0 -> c <> xb_class y \/ k <> xb_slot y.
Proof. exact (AFreeRead.other_key H L st X m s0 c k n b1 ctx l1 l2 AR XB). Qed.
Lemma freed_vs_slot24 : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> c <> K_BATCH_CLASS \/ k <> kk ->
  fhm L c k n + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= fhm L c k n.
Proof. exact (AFreeRead.freed_vs_slot24 H L st X m s0 c k n b1 ctx l1 l2 ALO AR XB NBT). Qed.
Lemma qfirst_cases : forall qs, qfirst L qs = 0 \/ (exists q, In q qs /\ qfirst L qs = abatch_addr L (qb_slot q)).
Proof.
ltac2:(KReplay.run1 (kr_t_AFreeReadC ()) ["CANSEC1"; "VariantC"] "p;1p10000p4p710p1000Mp4p710p8p1000ip4p70R0p1001`p4p710p8P0p1002:p4p710p8P0p1002Qp4p710p8P0p1002op4p710p8g00Tfj10Tp,1L#0o"). Qed.
Lemma qlast_cases : forall qs, qlast L qs = 0 \/ (exists q, In q qs /\ qlast L qs = abatch_addr L (qb_slot q)).
Proof.
ltac2:(KReplay.run1 (kr_t_AFreeReadC ()) ["CANSEC1"; "VariantC"] "p;1p10000p4p710p1000Mp4p710p8p1000ip4p70R0p1001`p4p710p8P0p1002:p4p710p8P0p1002Qp4p710p8P0p1002op4p710p8g00Ugj10Tp,1L#0o"). Qed.

Lemma read_dkC : forall (eb delta : Z) (ek : enq_kind),
  0 <= delta -> delta <= Q_MAX + 8192 ->
  (eb = qlast L (q_loc Q) \/ exists kk, eb = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))) ->
  Q_CACHE < a_qloc_bytes st + delta -> Q_MAX < a_qglob_bytes st + (a_qloc_bytes st + delta) ->
  ek_b ek (qlast L (q_loc Q)) = eb ->
  let g := g_of L st Q delta in
     dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes st + delta) m
  /\ dk_seps g L (fhm L c k n)
  /\ g_lst g = qlast L (q_glob Q) /\ dk_glst g (qlast L (q_loc Q)) = qlast L (q_glob Q) /\ g_drain g = true.
Proof.
  intros eb delta ek D0 DMAX EB REC1 REC2 EKB g. subst g. unfold g_of. cbv beta iota zeta delta [dk_preC dk_seps g_drain g_full g_nb g_fst g_lst g_qb g_nx dk_glst].
  destruct HCKR as [HC KR]. pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BS & _).
  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GC ABG] & IA & _ & NUM). destruct NUM as (NB1 & NB2 & NF & NC & NM).
  apply Forall_app in NF. destruct NF as [NFl NFg].
  pose proof (batches_bytes_lb _ NFg) as GLB0. rewrite <- NB2 in GLB0.
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as (B0 & B1 & _). atop_facts. lia. }
  assert (GF64 : 0 <= qfirst L (q_glob Q) < 2^64).
  { destruct (qfirst_cases (q_glob Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; right; exact Hq]. }
  assert (GL64 : 0 <= qlast L (q_glob Q) < 2^64).
  { destruct (qlast_cases (q_glob Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; right; exact Hq]. }
  (* [comment removed for export] *)
  assert (GFULL : a_qglob st <> [] ->
      0 < Z.of_nat (length (a_qglob st))
   /\ rw_cells bsegs m (qlast L (q_glob Q)) [C8 (Z_to_bv 64 0)]
   /\ 0x10007fff8000 <= qlast L (q_glob Q) /\ qlast L (q_glob Q) + 8192 <= ATOP
   /\ (al_t L + 4096 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_t L)
   /\ (fhm L c k n + 24 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= fhm L c k n)
   /\ (qlast L (q_loc Q) + 8192 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= qlast L (q_loc Q))
   /\ (eb + 8192 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= eb)
   /\ (al_nodes L + 1048576 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_nodes L)
   /\ (al_store L + 8388608 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_store L)
   /\ rng RNG (qlast L (q_glob Q)) 8192).
  { intros GNE.
    assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
    assert (LQ : (0 < length (q_glob Q))%nat) by (rewrite LN2; destruct (a_qglob st); [congruence| cbn; lia]).
    assert (QQ : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]).
    { apply app_removelast_last. destruct (q_glob Q); [cbn in LQ; lia| discriminate]. }
    set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
    set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
    assert (LNg : length qg = length lg) by (rewrite QQ, QG, !length_app in LN2; cbn in LN2; lia).
    unfold abatches in ABG. rewrite QG, QQ in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [_ ABz].
    cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & _) _].
    assert (QLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQ; apply qlast_app1). rewrite QLST.
    assert (INz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQ; apply in_or_app; right; left; reflexivity).
    pose proof (bslot_range L st X Q WF CP qgz INz) as KZ.
    pose proof (bslot_geo L st X ALO WF (qb_slot qgz) KZ) as (B0 & B1 & BAL & BT & BN & BSR & BR).
    destruct (bslot_busy L st X Q CP qgz INz) as (yz & Hyz & Syz & Cyz & Kyz).
    pose proof (freed_vs_slot24 (qb_slot qgz) KZ ltac:(rewrite <- Cyz, <- Kyz; apply other_key; [exact Hyz| rewrite Syz; intros EE; exact (NBT (eq_sym EE))])) as DH.
    (* [comment removed for export] *)
    assert (DL : qlast L (q_loc Q) + 8192 <= abatch_addr L (qb_slot qgz) \/ abatch_addr L (qb_slot qgz) + 8192 <= qlast L (q_loc Q)).
    { destruct (qlast_cases (q_loc Q)) as [E0 |(q & Hq & Eq)]; [rewrite E0; left; lia| rewrite Eq].
      assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
      pose proof (bslot_range L st X Q WF CP q INq) as KQ.
      assert (NEq : qb_slot q <> qb_slot qgz).
      { apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl).
        apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ qg) qgz []). rewrite EQl, QQ. rewrite <- ?app_assoc. cbn [app]. rewrite <- ?app_assoc. reflexivity. }
      pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q) (qb_slot qgz) ltac:(lia) ltac:(lia) NEq ltac:(rewrite size_of_class_24; lia)) as DD.
      rewrite size_of_class_24 in DD. unfold abatch_addr. exact DD. }
    assert (DE : eb + 8192 <= abatch_addr L (qb_slot qgz) \/ abatch_addr L (qb_slot qgz) + 8192 <= eb).
    { destruct EB as [-> |(kk & -> & KK & NIK)]; [exact DL|].
      assert (NEq : kk <> qb_slot qgz) by (intros ->; apply NIK; apply in_map; exact INz).
      pose proof (slots_disjoint L K_BATCH_CLASS kk (qb_slot qgz) ltac:(lia) ltac:(lia) NEq ltac:(rewrite size_of_class_24; lia)) as DD.
      rewrite size_of_class_24 in DD. unfold abatch_addr. exact DD. }
    split; [rewrite QG, length_app; cbn; lia|].
    split; [pose proof Z1 as Z1'; rw_split Z1' 1%nat ZN ZR; exact ZN|].
    split; [exact B0|]. split; [exact B1|]. split; [exact BT|]. split; [exact DH|]. split; [exact DL|]. split; [exact DE|].
    split; [exact BN|]. split; [exact BSR|]. apply BR. exact ARNG. }
  (* [comment removed for export] *)
  unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES in *.
  assert (GDT : (1048576 <? a_qloc_bytes st + delta) = true) by (apply Z.ltb_lt; exact REC1).
  rewrite GDT.
  split; [| split; [| split; [reflexivity| split; reflexivity]]].
  - split; [reflexivity|]. split; [exact MX|]. split; [exact GC|].
    split; [lia|]. split; [lia|]. split; [exact GF64|]. split; [exact GL64|].
    split; [exact REC1|]. split; [exact REC2|]. split; [lia|].
    destruct (a_qglob st) as [|bg lg0] eqn:QG0.
    + split; [reflexivity|]. assert (QQ0 : q_glob Q = []) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). rewrite QQ0. reflexivity.
    + rewrite <- QG0 in *. destruct (GFULL ltac:(rewrite QG0; discriminate)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
      rewrite EKB. unfold fhm in *.
      split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|]. split; [generalize F6; clear; intros; lia|].
      split; [exact F7|]. split; [exact F8|]. exact F11.
  - intros _ FU. destruct (a_qglob st) as [|bg lg0] eqn:QG0; [discriminate|]. rewrite <- QG0 in *.
    destruct (GFULL ltac:(rewrite QG0; discriminate)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    unfold fhm in *. split; [generalize F6; clear; intros; lia|]. split; [exact F9| exact F10].
Qed.
End VariantC.
End CANSEC1.
