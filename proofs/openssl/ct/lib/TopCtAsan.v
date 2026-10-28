(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ModelInvCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling Image Stage Nodes Tac Cfg RzCPS.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib Require Import TopLevel Obligations ProofBaseG TopE TopSides TopSidesG TopRows TopCtPlain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv Unforced LB_Sum LB_Inv LB_Raw LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import BnBase BnModel BnTree BgState ApBase ApState ApLogic ApOwner ApBridge CtCaps CtBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import ClassifierRows.

From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXP Require Import HxpInstAp.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXP Require HxpFinal HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocP Require RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtP Require Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import RT_iface RT_rep RT_closed RT_io D_defs D_libiface I_iodefs X_xdefs TopA_io.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require ARun EdgesInstA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import LibaAp.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require CtFuzzStmtA CtFuzzGapA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require HxaFinal.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarA Require HarStmtA HarTopA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require SctStmtA SctStmtA2 RtGenStmtA O2iSctStmtB O2iSctListStmtB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require UnwindRecInstA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRtA Require I_strcpylift.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require I_strcpyA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require EncStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require AFrameKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require I_vsnclosed RT_closedG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtAxBdA Require Import BdAParams.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtAxA Require Import TargetA.
Require OssFuzzTheorems.openssl.ct.images.Plain.
Require OssFuzzTheorems.openssl.ct.images.Asan.




Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation imgAct := (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs) (only parsing).




(* [comment removed for export] *)



Section OpenObligations.
(* [comment removed for export] *)
Let PMA : posix_memalign_init_contract RTA := RT_closed.rta_posix_memalign_closed.

(* [comment removed for export] *)
Local Notation ARo SP0 PMc FD MST := (CtRepA.CtFuzzGapA.ar_of RTA rta_contracts_all SP0 PMc FD MST).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Let WALK : forall (SP0 : Z) (PMc : Model -> Prop) (FD : fdfs_only PMc) (MST : mat_stable PMc),
  @CtRepA.CtFuzzStmtA.ct_fuzz_stmtA (ARo SP0 PMc FD MST) CtKitA.EdgesInstA.UK_A :=
  fun SP0 PMc FD MST =>
    @CtHarA.HarTopA.ct_fuzz_walkA_open (ARo SP0 PMc FD MST) CtKitA.EdgesInstA.UK_A CtKitA.EdgesInstA.BE_A
      CtKitA.UnwindRecInstA.UR_asn1_collect_B CtKitA.UnwindRecInstA.UR_i2o_SCT_LIST_A CtRtA.I_strcpylift.rta_strcpy
      CtA.I_vsnclosed.printf_contracts_A CtA.RT_closedG.rta_realloc_gen_closed.

(* [comment removed for export] *)
Let INIT : init_cps RTA (LIBA RTA) := CtHXA.HxaFinal.init_cps_A RTA (rc_facts RTA rta_contracts_all) rta_contracts_all rta_live_pos PMA.
(* [comment removed for export] *)
Let FUZZ : fuzz_one_cps' RTA (LIBA RTA) := CtRepA.CtFuzzGapA.fuzz_one_cpsA_of_walk RTA rta_contracts_all WALK.

(* [comment removed for export] *)
Lemma main_asan_ct : forall (argv : list (list byte)) (fs : Fs.Fs) c, valid_argv argv ->
  START RTA OUT_repA ERR_repA XENVA lib_startA argv fs c -> AS.ShapeAlg.realizes ctasegs c (Canon.canonT (Prog.argv_Z argv) fs).
Proof.
  intros argv fs c Hva HS.
  exact (main_rta rta_contracts_all rta_io (LIBA RTA) INIT FUZZ (liba_frameA RTA) (liba_exitA RTA) argv fs Hva c HS).
Qed.

(* [comment removed for export] *)
Lemma side_asan_ct : side_canon_off ncfg Tc imgAct target_alloc_limit.
Proof. intros en inp He Hi. exact (target_canon_A_main main_asan_ct en inp He Hi). Qed.

(* [comment removed for export] *)
Theorem base_ct_asan :
  strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target imgPct imgAct.
Proof. exact (glue_scfg_budgets_lim ncfg Tc _ _ _ _ side_plain_ctP_san side_asan_ct). Qed.
(* [comment removed for export] *)



(* [comment removed for export] *)
Check (base_ct_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.openssl.ct.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.ct.images.Plain.M.init_pc OssFuzzTheorems.openssl.ct.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.openssl.ct.images.Asan.M.loaded_segments OssFuzzTheorems.openssl.ct.images.Asan.M.init_pc OssFuzzTheorems.openssl.ct.images.Asan.M.phdrs)).
End OpenObligations.
