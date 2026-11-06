(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt ImageCtA.
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ModelInvCt.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling Image Stage Nodes Tac Cfg RzCPS.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.ct.lib Require Import TopLevel Obligations ProofBaseG TopE TopSides TopSidesG TopRows TopCtPlain.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv Unforced LB_Sum LB_Inv LB_Raw LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnModel BnTree BgState ApBase ApState ApLogic ApOwner ApBridge CtCaps CtBridge.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import ClassifierRows.

From OSSVerify.Proofs.openssl.ct.lib.CtHXP Require Import HxpInstAp.
From OSSVerify.Proofs.openssl.ct.lib.CtHXP Require HxpFinal HxpInit.
From OSSVerify.Proofs.openssl.ct.lib.CtMallocP Require RAligned_iface.
From OSSVerify.Proofs.openssl.ct.lib.P Require Rnd.
From OSSVerify.Proofs.openssl.ct.lib.CtP Require Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import RT_iface RT_rep RT_closed RT_io D_defs D_libiface I_iodefs X_xdefs TopA_io.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require ARun EdgesInstA.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import LibaAp.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require CtFuzzStmtA CtFuzzGapA.
From OSSVerify.Proofs.openssl.ct.lib.CtHXB Require HxbFinal.
From OSSVerify.Proofs.openssl.ct.lib.CtHarB Require HarStmtA HarTopA.
From OSSVerify.Proofs.openssl.ct.lib.CtSctB Require SctStmtA SctStmtA2 RtGenStmtA O2iSctStmtB O2iSctListStmtB.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require UnwindRecInstA.
From OSSVerify.Proofs.openssl.ct.lib.CtRtB Require I_strcpylift.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require I_strcpyA.
From OSSVerify.Proofs.openssl.ct.lib.CtEncB Require EncStmtA.
From OSSVerify.Proofs.openssl.ct.lib.CtFrameB Require AFrameKit.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require I_vsnclosed RT_closedG.
From OSSVerify.Proofs.openssl.ct.lib.CtAxBdB Require Import BdBParams.
From OSSVerify.Proofs.openssl.ct.lib.CtAxB Require Import TargetB.
Require OSSVerify.openssl.ct.images.Plain.
Require OSSVerify.openssl.ct.images.AsanUbsan.




Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation imgBct := (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs) (only parsing).




(* [comment removed for export] *)



Section OpenObligations.
(* [comment removed for export] *)
Let PMA : posix_memalign_init_contract RTA := RT_closed.rta_posix_memalign_closed.

(* [comment removed for export] *)
Local Notation ARo SP0 PMc FD MST := (CtRepB.CtFuzzGapA.ar_of RTA rta_contracts_all SP0 PMc FD MST).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Let WALK : forall (SP0 : Z) (PMc : Model -> Prop) (FD : fdfs_only PMc) (MST : mat_stable PMc),
  @CtRepB.CtFuzzStmtA.ct_fuzz_stmtA (ARo SP0 PMc FD MST) CtKitB.EdgesInstA.UK_A :=
  fun SP0 PMc FD MST =>
    @CtHarB.HarTopA.ct_fuzz_walkA_open (ARo SP0 PMc FD MST) CtKitB.EdgesInstA.UK_A CtKitB.EdgesInstA.BE_A
      CtKitB.UnwindRecInstA.UR_asn1_collect_B CtKitB.UnwindRecInstA.UR_i2o_SCT_LIST_A CtRtB.I_strcpylift.rta_strcpy
      CtB.I_vsnclosed.printf_contracts_A CtB.RT_closedG.rta_realloc_gen_closed.

(* [comment removed for export] *)
Let INIT : init_cps RTA (LIBA RTA) := CtHXB.HxbFinal.init_cps_A RTA (rc_facts RTA rta_contracts_all) rta_contracts_all rta_live_pos PMA.
(* [comment removed for export] *)
Let FUZZ : fuzz_one_cps' RTA (LIBA RTA) := CtRepB.CtFuzzGapA.fuzz_one_cpsA_of_walk RTA rta_contracts_all WALK.

(* [comment removed for export] *)
Lemma main_both_ct : forall (argv : list (list byte)) (fs : Fs.Fs) c, valid_argv argv ->
  START RTA OUT_repA ERR_repA XENVA lib_startA argv fs c -> AS.ShapeAlg.realizes ctbsegs c (Canon.canonT (Prog.argv_Z argv) fs).
Proof.
  intros argv fs c Hva HS.
  exact (main_rta rta_contracts_all rta_io (LIBA RTA) INIT FUZZ (liba_frameA RTA) (liba_exitA RTA) argv fs Hva c HS).
Qed.

(* [comment removed for export] *)
Lemma side_both_ct : side_canon_off ncfg Tc imgBct target_alloc_limit.
Proof. intros en inp He Hi. exact (target_canon_B_main main_both_ct en inp He Hi). Qed.

(* [comment removed for export] *)
Theorem base_ct_both :
  strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target imgPct imgBct.
Proof. exact (glue_scfg_budgets_lim ncfg Tc _ _ _ _ side_plain_ctP_san side_both_ct). Qed.
(* [comment removed for export] *)



(* [comment removed for export] *)
Check (base_ct_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.ct.images.Plain.M.loaded_segments OSSVerify.openssl.ct.images.Plain.M.init_pc OSSVerify.openssl.ct.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.ct.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.ct.images.AsanUbsan.M.init_pc OSSVerify.openssl.ct.images.AsanUbsan.M.phdrs)).
End OpenObligations.
