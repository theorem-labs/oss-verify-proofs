(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import AsanCeil PropExec AgentLib PureModel AllocSim MmapSim RefNodes AllocRefusal.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require AR.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_VmLedger () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backed_bytesC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes3orbI47Corelib4Init5Logic2or00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indK47Corelib4Init5Logic3and01c59OSSVerify5KrLib6Common8VmLedger<vm_budget_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib6Common8ShapeAlg:BUDGET_BIGC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_Reflexivec59OSSVerify5KrLib6Common8VmLedger@vm_budget_ok_iffC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool;orb_false_rC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib6Common8VmLedger>vm_budget_leafC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic2eq01C46Stdlib4Bool4Bool;andb_true_rC47Corelib4Init5Logic6eq_indC46Stdlib4Bool4Bool=andb_true_iffC46Stdlib4Bool4Bool=negb_true_iffK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib6Common8VmLedger:mprot_leafC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedger<vm_unprotectC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedger;mprot_ok_vmC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib6Common2AR@vm_gap_availableC1?~~~~~~~~~~~~~~~zzzzzzC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topI47Corelib4Init9Datatypes4prod00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib6Common2ARDvm_gap_available_iffC1?~~~~~~~~~~~~~~~zzzzzzC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC47Corelib7Classes9MorphismsDiff_impl_subrelationC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init9Datatypes3appc59OSSVerify5KrLib6Common8VmLedger>grant_ok_na_vmC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsBsubrelation_properC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK47Corelib7Numbers7BinNums1Z01C47Corelib7Program6Basics4implK47Corelib4Init9Datatypes4unit01C46Stdlib4Bool4Bool>negb_false_iffc59OSSVerify5KrLib6Common8VmLedgerGvm_gap_available_na_iffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedgerDmmap_na_refusable_vmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedgerNmmap_na_refusable_vm_false_iffC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib6Common8VmLedger;grant_ok_vmC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=orb_false_iffc59OSSVerify5KrLib6Common8VmLedgerAmmap_refusable_vmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedgerKmmap_refusable_vm_false_iffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedgerBmprot_refusable_vmC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common9PureModel7md_pure00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC59OSSVerify5KrLib6Common8RefNodesFvm_backing_used_simpleC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC59OSSVerify5KrLib6Common8RefNodesBvm_forget_range_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9PureModelCmd_pure_with_vmmapsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC59OSSVerify5KrLib6Common8RefNodes?with_vmmaps_etaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedgerCvm_budget_ok_noleafC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedgerDvm_backing_used_pureC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7MmapSim8grant_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions6bv_subC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;brk_grow_okc59OSSVerify5KrLib6Common8VmLedger>brk_grow_ok_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8AllocSim8vm_modelC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedger@brk_grow_ok_pureC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8AllocSim;brk_grow_okC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectCmprotect_model_nextC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_budget_okc59OSSVerify5KrLib6Common8VmLedgerBmprot_ok_vm_noleafC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedgerGmprotect_budget_ok_realC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7MmapSim>mmap_refusableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7MmapSimEmmap_refusable_unfoldC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedgerGmprotect_budget_ok_pureC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<AllocRefusalBmprotect_refusableC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedger7vm_mmapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedger8vm_noaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7MmapSim<munmap_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedger9vm_munmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8RefNodesCmunmap_model_simpleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8RefNodesDfixed_noaccess_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedger;vm_fixed_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8RefNodesKfixed_noaccess_model_simpleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8RefNodesEfixed_destroyed_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedger@vm_fixed_destroyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8RefNodesLfixed_destroyed_model_simpleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>brk_model_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@forget_vm_rangesc59OSSVerify5KrLib6Common8VmLedger;vm_brk_growC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_grantsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_unmapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapDmaps_subtract_rangesK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib6Common8AllocSim?brk_unmaps_growC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8AllocSim?brk_grants_growC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<andb_false_rC59OSSVerify5KrLib6Common8AllocSim9brk_modelC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203C59OSSVerify5KrLib6Common8RefNodes>brk_model_keepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8VmLedgerBgrant_ok_vm_unpackC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indc59OSSVerify5KrLib6Common8VmLedgerEgrant_ok_na_vm_unpackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8AsanCeil:init_sp_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removec59OSSVerify5KrLib6Common8VmLedger;init_sp_winC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelI4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib6Common8AsanCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizec59OSSVerify5KrLib6Common8VmLedger=alloc_top_winC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>alloc_top_roomK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_mmap (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) (vm_noaccess h)
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
(* [comment removed for export] *)
Definition vm_noacc (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
(* [comment removed for export] *)
Definition vm_munmap (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
               (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
(* [comment removed for export] *)
Definition vm_fixed_ok (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h)
               ((a, n) :: maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
(* [comment removed for export] *)
Definition vm_fixed_destroy (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (maps_subtract (vm_maps h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
               (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
(* [comment removed for export] *)
Definition vm_unprotect (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h)
               (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
(* [comment removed for export] *)
Definition vm_brk_grow (req : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((vm_brk h, (req - vm_brk h)%bv) :: vm_maps h) (vm_noaccess h)
               (vm_start_brk h) req (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_budget_ok (h : VmMaps) (n : Z) : bool :=
  (vm_backed_bytes h + n <=? vm_limit h)%Z || (vm_limit h <? ShapeAlg.BUDGET_BIG)%Z.

Definition vm_budget_leaf (h : VmMaps) (n : Z) : bool :=
  (vm_limit h <? ShapeAlg.BUDGET_BIG)%Z && negb (vm_backed_bytes h + n <=? vm_limit h)%Z.

Lemma vm_budget_ok_iff : forall h n,
  vm_budget_ok h n = true <-> (vm_backed_bytes h + n <= vm_limit h \/ vm_limit h < ShapeAlg.BUDGET_BIG)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h05lemmah12H0h21Bh31Hh41hh51np;1p;2p;3p;4p;6p;;p;9p-1R0g0000R1p4p710p9P0p1000\p4p710p9P0p1001HR2p4p710p9P0P2p4p7210p9P0P2p4p73110p9P0p1001fp4p710p9P0g002MR0p4p710p9g003Gj18Tg004Ej27Tg004bj16Tg005Yj29Tg0066j2<Tg006Sj2:Tg0070R2j21Tg007JR3j22Tg007cj24Tg008?j23TP1j2=Tg008[j2KTg009;j3JTg00:1j4;Tg00:dR1j6ITg00;Uj2HTg00<5j4ETg00<\l;CTg00=Wj2BTg00>7j3ATg00>Qj3@Tg00>kj6?Tg00?Gj4DTg00?bj2>Tg00@cj3FTP0l9GTg00A=f0R0g00A]3Fp=0p-0R4P3g00B=f5f4f3R5f2R6f1R7P0M9Gp=5g00Bng00Ce%87/70R8%67R9'9R:g00DCR;,<9R<':#0%0:R=%0<R>'1'2%86/77R?%66R@'9RA1<@;RB':#0%0ARA%0BRB'1RCP014?@R?13@;R@'1RDPD1=4DREE5W01K:<1489R<,2=PC11?BRCPAP?P0PBPBP4P3g00EB9J43RAPBC;EIPDPDPEE5W01H89139;R8,2>PCPDP4P4^24P3P4P4P3P3CEP2P1P?P4P3PAP?C;PBP@P0M;CPDPDPEE5W01B9;11<8R8PD[R<P<P?P@PD%85/76%65R5'4R6135;R5;A0X1?A@650X1@P0E?X38R@P@CDO2O2O21>70#0/28eW5W4o"). Qed.

Lemma vm_budget_ok_real : forall h n, (vm_backed_bytes h + n <= vm_limit h)%Z -> vm_budget_ok h n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh11nh21Hh32H0p;1p;2p;3g003Gj11Tg004Ej26Tg004bj14Tg007cj20Tg00?bj25Tg008?j23Tg0070j27Tg00F2j2:Tg00>7j39Tg00@cj38Tg00A=f0R0g00A]38p=2g00BnR1g00CeR2f1R3#1/60%43R4'0R5g00G71530#2f2R6#1/63%46R7'0g00DCR8,37'7R7[1348,751563#2[R5f3R4/56#2\71:30P0n2001000000120000000X12X01P5^12^01P0P4P6%14/66%44R4'01348;93O3b3W2W1W0o"). Qed.

Lemma vm_budget_ok_small : forall h n, (vm_limit h < ShapeAlg.BUDGET_BIG)%Z -> vm_budget_ok h n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh11nh21Hh32H0p;1p;2p;3g004bj11Tg008?j26Tg00?bj24Tg003Gj15Tg004Ej22Tg007cj23Tg0070j27Tg00F2j2:Tg00>Qj39Tg00@cj38Tg00A=f0R0g00A]38p=0g00BnR1g00CeR2f1R3#1R4g00DCR5'6R6g00G71430#0f2R7#5/23%17R8'31685'7R8[%53/20/34/761473#0[R6f3R4/47#0\81:30P0n2001000000120000000X12X01P6^12^01P0P4P7%54/27%14R4'31645;93O3b3W2W1W0o"). Qed.

Lemma vm_budget_ok_big : forall h n, (ShapeAlg.BUDGET_BIG <= vm_limit h)%Z ->
  vm_budget_ok h n = (vm_backed_bytes h + n <=? vm_limit h)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01Hh11bh21hh31np;1p;2p;3p;4p;6g004bj12Tg007cj21Tg003Gj14Tg004Ej25Tg005Yj26Tg006Sj2<Tg00@cj30Tg00GRj1;Tg0066j23Tg00H1j2:Tg00HQj47Tg00Hlj68Tg00?bj29Tg00Bng00Ceg00DCR0f1R1#2'1g00A=R2g00IJR3f3R4#4f2R5'5%24R4'6R6f0R7'<=026X12%45/51%25R6'6R8#;1360R9A02931104[11061340=023[1:60P7C7E81951=028eW0W3W2o"). Qed.

Lemma vm_budget_ok_noleaf : forall h n, vm_budget_leaf h n = false ->
  vm_budget_ok h n = (vm_backed_bytes h + n <=? vm_limit h)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "p'0h01Hh11bi001bh21hh31np;2p;1p;3p;6g00Ijj2?Tg003Gj19Tg004Ej28Tg004bj12Tg005Yj2;Tg0066j25Tg00Jmj14Tg00KKj21Tg006Sj26Tg00@cj33Tg00Kij27Tg00LCj1:Tg00Lbj6>Tg00Hlj6=Tg00?bj2<Tg00A=R0f0R1g00IJR233p=0g00Bng00Cef1R3/?1#0f2R4#9/83%24';R5P0P0f4#2g00DCR6'5R7%41'1#0f5#2/56R8,63=303]0P1f3#2/56R6g00A]R9#4'1#01709W0%42,16#0P01179%01X10P1P7%:7E>%07P0P21621#0X101702P8P1E=b0W0n0110000020000P3O1b11<43=305eW0W3W2o"). Qed.

Lemma vm_budget_leaf_true : forall h n, vm_budget_leaf h n = true ->
  (vm_limit h < ShapeAlg.BUDGET_BIG)%Z /\ (vm_backed_bytes h + n <=? vm_limit h)%Z = false.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01Hh11nh22H1h32H2h41bh52b1h62b2h71mh82H0h91hp;2p;1p;4p;3g00Ijj2@Tg00KKj2:Tg00G7R0j27Tg00M>j2?Tg004bj11Tg0066j29Tg003Gj13Tg004Ej22Tg005Yj25Tg00Jmj18Tg008?j24Tg00=Wj2>Tg00M_j1=Tg00?Gj4<Tg00@cj3;Tg00A=R1f0R2g00A]3;p=0g00IJ9;12p=6g00Bng00CeR3f1R4/@2#0P01:42#0f2R5#0R6%04R7'7[R8%02,771:54#0R7[f3R9#0/76\71?42P4n2001000000120000000X61X51P8^61^51P2%19R8g00DCR7'9R6%39/25/58#8R8P4O3%06%08'7P0f4R8#1R6/97#0%38/29/56#8#0f5R6#1R:/47%36/28/5:#6'7P2f6R:#1/97#0f7R8#3/2:%18'5#8#0P01942#01454[R814421954#0R:[1495\:1>42P4n2001000000120000000X73X13P8^73^13P2f9#1R3P7P5O31437P0%82#0%64[R0%62%84#0R3[%65\3%=2P4n2001000000120000000X41P0^41P2f;R1#3f:'2%11'5R0P9O2%60f<R0#1R9/47%30/21/59#6P5P2C<b3b0b2b0W3W2P4P2O2n2001000000120000000b0b8W0W1W9o"). Qed.

(* [comment removed for export] *)
Definition grant_ok_vm (h : VmMaps) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n)
  && vm_budget_ok h n.

(* [comment removed for export] *)
Definition grant_ok_na_vm (h : VmMaps) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n).

(* [comment removed for export] *)
Definition brk_grow_ok_vm (h : VmMaps) (req r : word) : bool :=
  if Z.ltb 0 (bv_unsigned (vm_brk h))
     && Z.ltb (bv_unsigned (vm_brk h)) (bv_unsigned r)
  then let lo := page_round_up_Z (bv_unsigned (vm_brk h)) in
       let hi := page_round_up_Z (bv_unsigned r) in
       (if Z.ltb lo hi
        then Z.leb hi (alloc_top h)
             && region_free (vm_reserved h ++ vm_maps h)
                            (Z_to_bv 64 lo) (Z_to_bv 64 (hi + page_size - lo))
        else true)
       && Z.leb (vm_backed_bytes h + bv_unsigned (r - vm_brk h)) (vm_limit h)
  else true.

(* [comment removed for export] *)
Definition mprot_ok_vm (h : VmMaps) (addr n : word) : bool :=
  (vm_backed_bytes (vm_unprotect addr n h) <=? vm_limit h)%Z || (vm_limit h <? ShapeAlg.BUDGET_BIG)%Z.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprot_leaf (h : VmMaps) (addr n : word) : bool :=
  (vm_limit h <? ShapeAlg.BUDGET_BIG)%Z && negb (vm_backed_bytes (vm_unprotect addr n h) <=? vm_limit h)%Z.

Lemma mprot_ok_vm_noleaf : forall h addr n, mprot_leaf h addr n = false ->
  mprot_ok_vm h addr n = (vm_backed_bytes (vm_unprotect addr n h) <=? vm_limit h)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "p'0h01Hh11bi001bh24addrh31hh41np;1p;3p;2p;6g00N@j11Tg00Nej1BTg00OCj1;Tg00Ofj39Tg00Pej3@Tg003Gj1<Tg004bj12Tg005Yj2:Tg0066j25Tg00Jmj14Tg00KKj23Tg006Sj27Tg00@cj36Tg00Kij28Tg00LCj1ATg00Lbj6?Tg00Hlj6=Tg00Qfj3>Tg00A=R0f0R1g00IJR236p=0g00Bng00Rf#1#1#1#1#1#1#B#;R3f2R4f1R5;91#0f3R69@45#<%26':R7P0P0f5#2g00DCR8'5R9%41'3#0f6#2/58R:,75=605]0P1f4#2/58R8g00A]R;#4'3#0180;W0%42,38#0P0139;%01X10P1P9%A9E?%09P0P21721#0X101802P:P1E=b0W0n0110000020000P5O1b1A>645=607eW0X43W2W3o"). Qed.

Lemma mprot_leaf_true : forall h addr n, mprot_leaf h addr n = true ->
  (vm_limit h < ShapeAlg.BUDGET_BIG)%Z /\ (vm_backed_bytes (vm_unprotect addr n h) <=? vm_limit h)%Z = false.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01Hh11nh22H1h32H2h41bh52b1h62b2h71mh82H0h94addrh:1hp;1p;3p;2p;4g00N@j13Tg00Nej1CTg00OCj1?Tg00Ofj3=Tg00KKj2<Tg00G7R0j29Tg00M>j2>Tg004bj11Tg0066j28Tg00Pej32Tg003Gj15Tg005Yj27Tg00Jmj1:Tg008?j26Tg00=Wj2BTg00M_j1ATg00?Gj4@Tg00@cj3;Tg00A=R1f0R2g00A]3;p=0g00IJ9;12p=4g00Bng00Rf#3#3#3#3#3#3#C#?R3f2R4f1R5;=2#0P01<52#0%04R6%05R7'9[R8%02,971<45#0R7[f3R9#0/96\71>52P5n2001000000120000000X61X51P8^61^51P2f4R8#1R7g00DCR6'8R:A2948#5/77#:R7P5O3%0:%07'9P0f5R7#1R:/86#0A2897#5/7:#:#0f6R:#1R;/66A278:#5/7;#4'9P2f7R;#1/86#0f8R792;:#5%17'7#:#0g00CeR7P01852#01645[R;16521845#0R:[1694\:1B52P5n2001000000120000000X77W1P;^77^17P2f:R7#1R;P6P4O316;6P0%:2#0%45[R0%42%:5#0R;[%44\;%A2P5n2001000000120000000X41P0^41P2f;R1f<R0727#5%10'7R7P9O2%47f=R7#1R9/66A2017#5/79#4P4P2C@b3b0b2b0W3W2P5P2O2n2001000000120000000b0b8W0X13W9W:o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_refusable_vm (h : VmMaps) (n : Z) : bool :=
  negb (vm_budget_ok h n) || negb (vm_gap_available h n).   (* [comment removed for export] *)
Definition mmap_na_refusable_vm (h : VmMaps) (n : Z) : bool :=
  negb (vm_gap_available h n).
Definition mprot_refusable_vm (h : VmMaps) (addr n : word) : bool :=
  negb (mprot_ok_vm h addr n).

Lemma vm_gap_available_na_iff : forall h n,
  vm_gap_available h n = true <-> exists a, grant_ok_na_vm h a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "p'0h01ah11Hh21nh31mh42Hah51bh65lemmah72H1h82H2h92H3h:2H4h;1Ah<1Bh=1hi001xp;2p;1p;9p;4p;3p;8p;6p;=g00SKj2]Tg00N@j1ETg00Nej1aTg00OCj1pTg00TPj21Tg004Ej23Tg00U:j12Tg00V2j2_Tg00VRR0j2?Tg007JR1j2JTg0000j2fTg002Ml9eTg00Vlj2cTg007cj2:Tg00X5j1HTg00Xoj1GTg00Yej2FTg00KKj26Tg005Yj28Tg00Kij2`Tg00;Uj2YTg00HQj4OTg00=Wj2XTg00ZKj2WTg00Zkj4VTg00G7R2j25Tg00[Ej3NTg00\?R3j3nTg00M>j2UTg00<5j4LTg00]0j2mTg00]]j8\Tg009;j3hTg00^PR4j6gTg00_Bj2QTg00@cj3>Tg0066j2RTg008?j2MTg00?Gj4KTg00__j2dTg00`?j3TTg00`\j3iTg00Hlj6jTg00:1j4kTg00a_l=bTg00A=R5f0R6g00A]R73>p=0g00bN,d6p=4g00CeR8g00cFR97>6p=@1M96p=;f5R:f4R;#Hf3R<#G3Tf2R=f1R>/F63N=>57p=71:=>/56p=D15>6,5=p=<Ai=>6=>57p=AAT;<=?N>6p=P13=>/:6p=Z1R96p==16>6=>57p=BP5P7P<P=P>P6Ejp=I1Q69p=9%H>%G65T=p=^AN=>6=>57p=oA>567,5>p=Cp-0R?P?P1P1P6P1g00cdR@P3G\p=lP?P1P>P6Ckp=SP6P>P2P4P=g00dBP<P;P:f6R4f7R3f8RAf9RBM=bp=[g00Bn1]>6#0g00Rf#E#E#E#E#E#E#aRC#pRD11C6RE#4#@RF%;ERG13E>%2=1_DDRHP=P=P6PCP>E73D3<X0D'?RI'JP?P1g00B=1]=>#013E=%2<PHP<P<P6PCP=E73D9<FGX0DRJ,?DRKP6AA<6=X0DRL,?DRMPM1f?MM9eW61c>6PM\IAA=6>X0D,?DRMPK[P0PDPJAA;6<X0D,?DP613E;%2:PHP:P:P6PCP;E73D9<FGP211C>RJ#4RK#@%;J13J:RN%24RO':PH%H4%G4P>1FC:DPRP#0RQ3<AAA63X0D,?DP611C<RR#4RS#@11C;RT#;13TARU%2BRV':PHPBPBP;PCPAE7RW3<P211C:RX#;RY13XBf:RZ#2PHPZPZP:PCPBE73DR[f<R\f;R]7A6X0D,?DP611C3R^#;11CA/3\f=R_#2PHP_P_PAPCP\E7R`3DP211CBRaf>Rb#27Z_RcPHPbPbPBPCP_E7Rdf@Ref?Rf7A6X0D,?DP611C]/3fRg%2eRh':PHfARiPiP\PCPeE7RePDfCRjfBRk7A6X0DP_11CbRl#=Rm,6613lkRn%2jRo'8Rp'6PH%Hj%GjPb1FCkDPRb'BX551676/6p/BbX551677Rq/66/BbX5516q7/B6X551`57PH%Hk%GkP_1FCiDPR7P6CI11C_R5/3iRq%2kRb'8Rr%0r1:no[1:qbRo%0pRp[1YqbP>COCI%=5Rb%0bRb%;l[%;5Rq%0m[1X95P:COCI%45R5#9Rm%0m%4lRl#@[%@5Rm%9l#0[1W59PBCOCIAAk_ieCVW:W9P>P6O2n2001000000121000000W1W8P>P6O2n2001000000121000000W1W7P>P6O2n2001000000121000000W1X0DP>P6O2n2001000000121100000X1IP0PDPL13E<%2;PHP;P;P6PCP<E73D9<FGX0D,?DP6AA:6;PD13E4%23REA^H33RL1FC4R07o63D9<FGX0DP>%9K%=J'618NO'6RO/BP%0O/5QRQ'J11C=RN#4#9%=N'6RJ13N4/8ERE'6RNANL=0R0'B%0NRN%00R0'5;n6W61UOPP6O2PQ%0J/CERQ,JNP?^<?RN^;?ROP?P?\?P1P?P?P1P1CLRPCLRLP?PNP1P?P?P1P@CLR@CLRKP?PNP1P11m?1RNPPP@%lNG\RN%9SRS%=RR@'6RP13R3%2A'8RR'B%0PRP%0RRR'5P6PHPAPAP<PCP3E7R3P3g00EB9h?1R?/S3M:[W61UJEP6O215Q0%0S/C@RQ,JPPOPLPKPN%4T#9RN%=TRT'BRK18UV#0RV'5%0N/CTRT/5VRNPKPTP6PVPV1S?VEgPWPW1S?WM:[W61US@P6O215QR/53P2PNPW%4X#@?<Y[P611C4R[#4#9#0%=['C13[Z%2]'8'CP2%4^#9#0%=^'C13^]%2\'8#0%4aR^#@%;a15cd3<\`P6%9^#0%=a'CP211CZRZ#4#9#0%=Z#018gh#01Co79<mq\e[P611C\#4#9#0PHfDR\P\PfPCPjE7P21Q>6#0A>8=>[RfA>8>61Q=>#0R\[A>8<=\\1W>6P>n2001000000120000000X38X28Pf^38^28P611Ci#4RiP9P;O3%@iP21R>6#01M=>[Ri1M>61R=>#0Rf[1M<=\f1X>6P>n2001000000120000000X38X28Pi^38^28P6P911CjRjP:O3%;jP218>6#01:=>[R21:>618=>#0Rj[1:<=\j1Y>6P>n2001000000120000000X38X28P2^38^28P6fE,1CfI'3R2fJRj#2R<P4O31:2<fFR<,1CR2#4#@%;2R:fKR9#29Z2jR2PHP9P9P<PCPjE7Rj'5RC'5P;P:PCP=P2PjP6P4CKCKCKb9b1b8b1b7b1W:X9pX8bW7P>P6O2n2001000000121000000W1P>P6O2n2001000000121000000W1P>P6O2n2001000000121000000b4b4b4CVW4X0DP>P6O2n2001000000121100000X1MCKO2X28W=o"). Qed.

Lemma mmap_na_refusable_vm_false_iff : forall h n,
  mmap_na_refusable_vm h n = false <-> exists a, grant_ok_na_vm h a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh25lemmah31np;2p;1p;3p;9g00SKj28Tg00Jmj15Tg007JR0j27Tg00N@j10Tg00Nej1=Tg00OCj1<Tg00`\j33Tg00VRj26Tg0000j2;Tg002Ml9:Tg00dbj19Tg00eDj2?Tg00fPj2>Tg00@cj34Tg00A=R1f0R2g00IJ34p=2g00A]9412p=1g00Bng00Cef1R1/82R3#5#2%13'7p-0R4P0g00B=f2R0/81R5#5#2%15P2g00Rf#0#0#0#0#0#0#=#<R5f3?320#1X05'6R6P61;46M9:W2%931?12O21>12#2A3021#1X05,65'7eW3W1o"). Qed.

Lemma mmap_na_refusable_vm_iff : forall h n,
  mmap_na_refusable_vm h n = true <-> forall a, grant_ok_na_vm h a n = false.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "p'0h01Eh11ah21hh31nh42H0h51Hh61bi001bh72Hah82Hfh91ei011xp;2p;1p;3p;4p;6g00fPj24Tg00N@j15Tg00Nej1<Tg00OCj1>Tg00`\j31Tg00Kij28Tg00@cj33Tg00VRR0j26Tg00gYj2;Tg00Zkj4:Tg00Lbj67Tg00hlj29Tg00?Gj4=Tg00A=R1f0R2g00A]R333p=0g00IJR49312p=2g00BnR5g00CeR6f1R7/42R8#0R9g00Rf#5#5#5#5#5#5#<#>R:f3R;f2R<712R=#2]1[A1<27R>#2^1:R?14<7R@#0[P=P11812RAf4RB?17;=312P1f6RCf5RD71;=312%27]0P7A1D<BRE#0g00G7RF%28%0=X1:,6:R=[R8%0>X1:,6:%2@R>[RG14;<R<#2\=1;72R=P2n2001000000120000000X36X25PG^36^25P2f7RHPCP:f8?12H#0X1:RIPBP7C:O3b414CD#2P114HC%02X61RJPDP4P2E7A3143RKP1P4P1p-0P2g00iKRLg00ihn0110000020000X91g00jDP3P2E7RMPLA3134/92b4b5b8W0%2E1814W0n0110000020100P2O1b0b6X1:X59P@P1PAA31<2P114DB=312%07]0P714B;R<#01813W0%2<PFP8PGA1B2;#0X1:,6:\>P=P7n2001000000120000000X36X25P8^36^25P2PCPDP7O3A1H2C#0X1:,6:P0P:PIPKP2f:RIf9R0712#0P1f;?17IPJP2P4P0P7O1E7PKPMPL19K2b4b7W7X1:P7P2O2n2001000000120101000b0b4W0n0110000020001P2O1b0b6X5?C=W3W2o"). Qed.

Lemma mmap_refusable_vm_false_iff : forall h n,
  mmap_refusable_vm h n = false <-> exists a, grant_ok_vm h a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "p'0h01ah11Hh22Hah35lemmah42Hbh51bh62b1h72b2h81Bh91hh:1ni001xp;2p;1p;3p;4p;6p;9p;;g00?bj22Tg00Jmj1=Tg00SKj2LTg006Sj2JTg00G7R0j21Tg007JR1j29Tg00N@j18Tg00Nej1UTg00OCj1STg00j`j36Tg00VRR2j24Tg0000j2`Tg00k`j2]Tg009;j3YTg00:1j4OTg00^PR3j6XTg00dbj1NTg00<5j4WTg00eDj2VTg00KKj23Tg00Kij2TTg00Hlj6KTg00TPj2:Tg00__j2;Tg00_Bj2ATg0066j2BTg004Ej2?Tg00U:j1FTg005Yj2>Tg00V2j2RTg00X5j1ETg00Xoj1HTg00`?j3DTg00Yej2GTg00[Ej3<Tg00Zkj4QTg00M>j2_Tg00?Gj4PTg00lAj2^Tg00@cj3ITg002Ml9\Tg00<\l;ZTg00`\j3[Tg00A=R4f0R5g00IJ3Ip=7g00A]R69I45p=0p-0R7P1g00B=f5R8f4R9f3R:f2R;f1R<P5M9\p=@P7f6R=P1P8P0P3P9P:P;P<P5M;Zp=MA[;<5=I46p=513;</35p=Cg00Bng00Ce12<5R3#=R>1L<5R?#=R@'J#7%7>RA%7@RB'1'912;<RC#=RD1L;<RE#=RF'J#7%7DRD%7FRF'1RGP5g00Rf#8#8#8#8#8#8#URH#SRIA6:5;#0X0IRJ'4RKPK1`7KRLE@W31]>@%03R@,9APG%0CRC/1FRGPDPCP5PFPFP7P1g00EB9Y71RDPFCOEXPKPKPLE@W3%N3%0?R3,9BPG%0ERE,1CRGP7^87RBP7P7P1P1CWRAPCP7P1PDPCCORDPFPEP5FMPKPKPLE@W3%N?A5;5<X0I,4IR?,93PGA5:5;X0I,4IRG,1CR3PBPAPCPDPEPGP5FMPKPKPLE@W31V<511@?R?PK[A6;5<#0X0I,4IRKP3[P0PCPGA695:#0X0I,4IP5129:#0A5=58X0I,4IP2PIf7RG?55=X0If8RC?65G#0X0I,4IP5f9R3?55CPIf;R@f:RL765#0X0IP<P4P612@LRE,35#0X54P4P61365#0X541T4612L3P8EK1:H<R6g00bNRD';g00cFRA'A1BA6'31?63%FLR6'>1RIIRB%EL%HL3DRF1GH3R17<<3CP5EKA6L<3#0eCQW2X0IP<P5O2n2001000000120100000W1W4P<P5O2n2001000000121000000X1?P2PIPJ12:;#0A595:X0I,4I'1P5A6859#0P013<5#0%0;R9%0<RJ'1[R2%05,1J13;<#0RJ[%0:/19\J1_<5P<n2001000000120000000X74X64P2^74^64P51:H;R4/;D/AA1BA4'31?4=%FG'>%EG%HG5DB1GH=7<;3CR;12G=R=P<O3%0;%0='1P01:H:R0/;D/AA1BA0'31?0G%FC'>%EC%HC5DB1GHG7<:3C#012CG#0123C#0A5L53X0I,4I'1P51:H8RH/;D/AA1BAH'31?H3/>6A<F813C#0%0Ef<RE/2@#0f=?55EX0IRE,4IP5PIPEPGP<CQCPW4W2P<P5O2n2001000000120000000b2b1W2X0IP<P5O2n2001000000121100000X1KCPO2O2O2O21^<5#7/9KeW:W9o"). Qed.

Lemma mmap_refusable_vm_iff : forall h n,
  mmap_refusable_vm h n = true <-> forall a, grant_ok_vm h a n = false.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "p'0h01Eh11ah21hh31nh42H0h51Hh61bi001bh72Hah82Hfh91ei011xp;2p;1p;3p;4p;6g00lAj24Tg00N@j15Tg00Nej1<Tg00OCj1>Tg00j`j31Tg00Kij28Tg00@cj33Tg00VRR0j26Tg00mGj2;Tg00Zkj4:Tg00Lbj67Tg00hlj29Tg00?Gj4=Tg00A=R1f0R2g00A]R333p=0g00IJR49312p=2g00BnR5g00CeR6f1R7/42R8#0R9g00Rf#5#5#5#5#5#5#<#>R:f3R;f2R<712R=#2]1[A1<27R>#2^1:R?14<7R@#0[P=P11812RAf4RB?17;=312P1f6RCf5RD71;=312%27]0P7A1D<BRE#0g00G7RF%28%0=X1:,6:R=[R8%0>X1:,6:%2@R>[RG14;<R<#2\=1;72R=P2n2001000000120000000X36X25PG^36^25P2f7RHPCP:f8?12H#0X1:RIPBP7C:O3b414CD#2P114HC%02X61RJPDP4P2E7A3143RKP1P4P1p-0P2g00iKRLg00ihn0110000020000X91g00jDP3P2E7RMPLA3134/92b4b5b8W0%2E1814W0n0110000020100P2O1b0b6X1:X59P@P1PAA31<2P114DB=312%07]0P714B;R<#01813W0%2<PFP8PGA1B2;#0X1:,6:\>P=P7n2001000000120000000X36X25P8^36^25P2PCPDP7O3A1H2C#0X1:,6:P0P:PIPKP2f:RIf9R0712#0P1f;?17IPJP2P4P0P7O1E7PKPMPL19K2b4b7W7X1:P7P2O2n2001000000120101000b0b4W0n0110000020001P2O1b0b6X5?C=W3W2o"). Qed.

Lemma mprot_refusable_vm_iff : forall h addr n,
  mprot_refusable_vm h addr n = true <-> mprot_ok_vm h addr n = false.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h04addrh11hh21np;1p;3p;2g00N@j10Tg00Nej17Tg00OCj13Tg00Qfj32Tg00M_j16Tg00nWj35Tg00@cj31Tg007Jj24Tg00Bng00Rf#0#0#0#0#0#0#7#3R0f2R1f1R2f0R332R4#6g00A=R5A5123g00A]31g00IJ9154'4eX20W0W1o"). Qed.

Lemma mprot_refusable_vm_false_iff : forall h addr n,
  mprot_refusable_vm h addr n = false <-> mprot_ok_vm h addr n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h04addrh11hh21np;1p;3p;2g00N@j10Tg00Nej17Tg00OCj13Tg00Qfj32Tg00dbj16Tg00nWj35Tg00@cj31Tg007Jj24Tg00Bng00Rf#0#0#0#0#0#0#7#3R0f2R1f1R2f0R332R4#6g00A=R5A5123g00IJ31g00A]9154'4eX20W0W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma vm_backing_used_pure : forall md,
  md_pure md -> vm_backing_used md = vm_backed_bytes (m_vmmaps md).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "p'0h01Hh12Hlh22Hmh32_Hh42mdi009mp_haltedi017mp_lazyi026mp_matp;1p;3p;2g00o^R0j1@Tg010]j1?Tg011[j1:Tg003Gj14Tg00@cj31Tg00N@j10Tg00Nej1;Tg00OCj19Tg012Rj15Tg0134j16Tg013kj17Tg00V2j28Tg014Mj12Tg014mj1>Tg015ej13Tg016Ej1=Tg017Ej3<Tg018Pf0R1#@P0f1R0g00Cef2R2#?%:2#431P1g00Rf#0#0#0#0#0#0#;#9R3#5f4#6%73311833R4#2f5#>%3431%23f6#=%3331f7?<01W2W1W3P2P0P1O3n101000000130100101102W0W4o"). Qed.

Lemma with_vm_backing_pure : forall md,
  md_pure md -> with_vm_backing [] [] md = md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "p'0h02Hlh12Hmh21lh36m_fsysi006m_fsysh44m_ioi014m_ioh55m_limi025m_limh66m_proci036m_proch76m_timei046m_timeh82mth91Hh:2_Hh;4m_fdi054m_fdh<4m_vmi064m_vmh=2mdh>9vmst_mapsi079vmst_mapsi081mi099mp_haltedi0:7mp_lazyi0;6mp_mati0<1vi0=9vmst_lazyi0>Avmst_materializedp;1p;2p;3p;7p;6g00o^R0j1ATg00N@j12Tg00Nej1>Tg00OCj1;Tg00V2j2@Tg015ej19Tg019Fj34Tg00@cj30Tg012Rj1=Tg0134j1<Tg013kj1:Tg014Mj17Tg014mj15Tg016Ej16Tg01:Dj71Tg01;:j33Tg00Kij2?Tg00Hlj68Tg018PR1f0R2#AP0f1R0g00Rf#2#2#2#2#2#2#>#;R3/@3R4#9R5%93R6f2R734=017R8P2%=3f4R9#<%:330%74R4f5R:#5;05%73R3f6R;#6;06P1%52=045%60=036P8]1]0f7R8g01<2g01<jR<P<g01=bR<g01>ZR=g01?RR>g01@LR?g01AER@P8P:P9f3RAP7P0P2F1#5=045f8RBP;P:P9PAP7P0F1#6=036f9RCP8P;P:P9PAP7F1RD9456=01D]1]0]7]5]6]3]4P2g00Bnf<A38;:P9PAP7P0P2F1#5=045f=A3B8;P:P9PAP7P0F1#6=036P4P5f?RDf:RE?32BP8P;P:P9PAF1RF9456=01FX24P3P6PDA3E52P8P;P:P9PAF1RE9456=01EX83f>A3C56P;P:P9PAP7F1,?1P8P2E8PBP0E8W1W0X7@X5?X6>X3=X4<X83X24W>P7P0P2O3n0110<00013110710=10>W<W;P;P:P9PAP7P0P2O7n01108000171105106101100103102104P0P2O2W1W0W:P7P0P2O3n10100000013110910:10;W9W=o"). Qed.

Lemma vm_forget_range_pure : forall lo hi md,
  md_pure md -> vm_forget_range lo hi md = md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "p'0h01Hh12Hlh22Hmh32_Hh42hih52loh62mdi009mp_haltedi017mp_lazyi026mp_matp;1p;3p;2p;5g00o^R0j1>Tg01B?j3=Tg00@cj31Tg00N@j10Tg00Nej1<Tg00OCj19Tg012Rj18Tg0134j15Tg013kj16Tg00V2j27Tg014Mj12Tg014mj14Tg015ej13Tg016Ej1;Tg01C=j5:Tg00CeR1g018PR2f0R3#>P0f1R0f4R4f3f2R53==125P3g00Rf#0#0#0#0#0#0#<#9R2#8%54%62311722R4#2f5#4%3431%22f6#;%3231f9f8f7P0P3D:W2W1W3P5P0P3O3n101000000130100101102W0W6X41W5o"). Qed.

(* [comment removed for export] *)
Lemma md_pure_vmmaps : forall h md, md_pure md -> md_pure (with_vmmaps h md).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "g01DDo"). Qed.

Lemma with_vmmaps_vmmaps : forall h md, m_vmmaps (with_vmmaps h md) = h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh12mdp;2g00Kij20Tg00BnR0g018Pf1,00W1W0o"). Qed.
Lemma with_vmmaps_twice : forall h h' md, with_vmmaps h (with_vmmaps h' md) = with_vmmaps h md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh12h'h22mdp;2g01EMj21Tg00Kij20Tg00BnR0g018PR1f2f0'1,01W2X10W0o"). Qed.
Lemma with_vmmaps_same : forall md, with_vmmaps (m_vmmaps md) md = md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "g01FGo"). Qed.

(* [comment removed for export] *)
Lemma grant_ok_pure : forall hint md a n,
  md_pure md -> vm_budget_leaf (m_vmmaps md) n = false ->   (* [comment removed for export] *)
  grant_ok hint md a n = grant_ok_vm (m_vmmaps md) a n.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h03Hnlh12Hph21ah31bh44hinth52mdh61nh71zp;1p;2p;3p;6p;4g00N@j11Tg00Nej1NTg00OCj1HTg00o^j1DTg011[j15Tg00Ijj2MTg00@cj34Tg003Gj1:Tg00TPj2;Tg00__j2?Tg00_Bj26Tg0066j28Tg00KKj20Tg004Ej22Tg00U:j1CTg005Yj23Tg00V2j2LTg00X5j1@Tg00Xoj1>Tg00`?j3=Tg00Yej2ATg00[Ej37Tg004bj1<Tg00?bj29Tg00Kij2GTg01GKj3FTg00Hlj6BTg010]j1ITg01HSj2ETg01I\j4JTg00j`j3KTg00Rf#1#1#1#1#1#1#NR0#HR1g018Pg00CeR2f2R3#Dg00A=R4f3R5#5f1R6'Mg00IJ34P2f4R7#5R8#:R91;07R:g00bNR;'?g00cFR<'618<:'012:5f5R:#5R=#C'3'01L11R>%@=%>=3=1A05777'0R?f0R@/25%<=RA'3'019=5,0?544X72P41293%<8'3R9%:=/25/3A,0?10?@544X341;05R?/?;/6<18<?'012?3%C8'3'0%@8%>85=>1A03775'0/09,G41983AF83@EB%I71E76EBP:P7P5P3CJAK853544eW0W1W6X21W5W4o"). Qed.

Lemma grant_ok_na_pin_vm : forall md a n,
  grant_ok_na_pin md a n = grant_ok_na_vm (m_vmmaps md) a n.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah12mdh21np;1p;3p;2g00N@j10Tg00Nej15Tg00OCj12Tg011[j11Tg00`\j34Tg00Kij23Tg018Pg00Rf#0#0#0#0#0#0#5#2g00Ceg00A=f2#1f1f034'3W2W0W1o"). Qed.

Lemma grant_ok_vm_na : forall h a n,
  grant_ok_vm h a n = true -> grant_ok_na_vm h a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01Hh12b1h22b2h32H0h42_Hh51ah61hh71np;1p;3p;2g00N@j12Tg00Nej1HTg00OCj1DTg00j`j3BTg00KKj21Tg00G7R0j2;Tg00M>j2CTg00TPj26Tg00__j27Tg00_Bj23Tg0066j29Tg004Ej2:Tg00U:j1@Tg005Yj2?Tg00V2j2GTg00X5j1<Tg00Xoj1=Tg00`?j3>Tg00Yej28Tg00[Ej35Tg00?bj2ATg00`\j3ETg00@cj3FTg00A=R1f0R2g00A]3Fp=0f2R3f1R4'1/12p=4g00Bng00Rf#2#2#2#2#2#2#HR5#DR6g00CeAB342#0P01142#0%03R7%04R8';[R9%02,;81134#0R8[f3R:#0/;7\81C42P4n2001000000120000000X21X11P9^21^11P2165:R1g00bNR9'7g00cFR8'31981'11:13f4R1#@'?1G66R6%<1%=13>185375:34R71A13R;P4O3%07%0;';P01651R0/79/381980'11:0:f5R0#@'?%<0%=05>6185:75134#01A0:#01650R;/79/38198;'11:;1f6R;#@'?%<;%=;5>6185175034#0P2165;R1/79/381981'11:10f7R1#@'?%<1%=15>6185075;34#0f8/A;#0P4W4W0P4P2O2n2001000000120000000b0b3AE:34#0eW0W7W5W6o"). Qed.

Lemma brk_grow_ok_pure : forall md req r,
  md_pure md -> Mmap.brk_grow_ok md req r = brk_grow_ok_vm (m_vmmaps md) req r.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h02Hph12mdh21rh33reqh41zp;1p;2p;3p;6g00N@j13Tg00Nej1MTg00OCj1JTg00o^j1DTg011[j1CTg003Gj1>Tg01JXj1<Tg00TPj21Tg0066j22Tg00KKj20Tg01KMj16Tg00U:j18Tg005Yj24Tg00V2j2LTg00X5j1BTg00Xoj1ATg00`?j3=Tg00Yej27Tg004Ej25Tg01LKj2?Tg00[Ej3@Tg01Lhj39Tg004bj1;Tg00@cj3:Tg00Kij2ITg010]j1FTg01HSj2GTg00Hlj6HTg01MMj3ETg01NMj3KTg018Pg00Rf#3#3#3#3#3#3#MR0#JR1f2R2#Dg00CeR3f3R4#CR5#>R6g00A=R7P7P7g00cFR8f4#CR9#<R:,10R;'21102R<,2;'0R=P7P7%6;R;%6<R<'2%89,4<1L11R>%B9%A93=170;g00bNR?,5</?;,703@'0g00A]R;n0100000020000R<f0R@A902:,10R:'5%;9RA'4'0P;n0100000020000P7P7P=%>9/5:/4A,0<P;n01000000200003:X43P7P7%<5R3,10R<,28f1R8,10RA,2<'0P7P7%6<R<%6ARA'2%85,4A%B5%A55=>170<15A?/?<,703@'0P;n0100000020000A9083,10,56%;5'4'0P;n0100000020000,I7%F41G4@EHAE428AK5285:7eW0X21W3W1o"). Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_allocsim : forall h req r,
  AllocSim.brk_grow_ok h req r = brk_grow_ok_vm h req r.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01bh11hh21rh33reqp;1p;3p;2p;4p;6g00N@j10Tg00Nej1ATg00OCj1;Tg01OPj16Tg011[j1@Tg01NMj32Tg00@cj34Tg00Kij21Tg01MMj3:Tg012Rj19Tg013kj17Tg00V2j28Tg014Mj13Tg015ej15Tg01PMj4?Tg01QLj4>Tg00Hlj6<Tg01RQj3=Tg00Bng00Rf#0#0#0#0#0#0#A#;R0g00A=R1f2R2#6R3#@f1R4f0R532f3?2249415X01A2245R6,11A:345P3P4P5P3%90%70'11800R3#3%53'1%30%50'1C?C>E<A=245=416eX20W3W1o"). Qed.

(* [comment removed for export] *)
Lemma mprotect_budget_ok_real : forall md addr n,
  md_pure md -> mprotect_budget_ok md addr n = (vm_backed_bytes (vm_unprotect addr n (m_vmmaps md)) <=? vm_limit (m_vmmaps md))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h02Hph14addrh22mdh31nh41zp;1p;3p;2p;8p;6g00N@j10Tg00Nej1KTg00OCj1>Tg00o^j17Tg01SQj39Tg011[j11Tg003Gj13Tg004bj14Tg005Yj22Tg00Pej36Tg00@cj35Tg00Kij2;Tg010]j1:Tg00X5j1JTg00Xoj1ITg01T]j1HTg00TPj28Tg004Ej2CTg01UWj3BTg01VSj1?Tg01JXj1@Tg01WNj1ATg01XIj1=Tg01YBj8DTg01DDj3ETg01HSj2<Tg00Hlj6FTg01Z9j3GTg018Pg00Rf#0#0#0#0#0#0#KR0#>R1f2R2#7g00CeR3f3R4f1R5792R6#1#3g00A=R7f0R8f4R9?942#1#4'2%19R99642#3%49'235X43%14R39625#3%43R9'2R:,;7%:6%J3%I3%H31802R;1805,C;3B%?3%@3P9%A3%=3GD?E48%76e,<6EFAG425=57:eW0X31W1W2o"). Qed.

Lemma mprotect_budget_ok_pure : forall md addr n,
  md_pure md -> mprot_leaf (m_vmmaps md) addr n = false ->   (* [comment removed for export] *)
  mprotect_budget_ok md addr n = mprot_ok_vm (m_vmmaps md) addr n.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01bh13Hnlh22Hph34addrh42mdh51np;1p;3p;2p;4p;6g00N@j10Tg00Nej1@Tg00OCj1;Tg00o^j19Tg011[j12Tg00Ofj3<Tg00@cj31Tg00Pej34Tg003Gj16Tg004bj17Tg005Yj23Tg00Qfj35Tg00Kij2:Tg01[Dj4?Tg00Hlj68Tg01Z9j3>Tg01\Kj4=Tg018Pg00Rf#0#0#0#0#0#0#@#;R0f2R1#9g00A=R2f3R3#2f1R47<1g00IJ31P2f4R5#2R69431#6%76'3R7f0R8f5#2R9?553512X02P2P7A4539#6%79'3=128X021:27A5631P6P3P1P8C?E8A>531P5P3P1P4C=E8W1W2X50W3W4o"). Qed.

(* [comment removed for export] *)
Lemma mmap_refusable_pure : forall md n,
  md_pure md -> vm_budget_leaf (m_vmmaps md) n = false ->   (* [comment removed for export] *)
  mmap_refusable md n = mmap_refusable_vm (m_vmmaps md) n.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01bh13Hnlh22Hph32mdh41nh51zp;1p;2p;3p;6g00o^j1CTg011[j16Tg00Ijj2<Tg00@cj32Tg010]j1BTg004Ej24Tg004bj1:Tg005Yj23Tg00Jmj10Tg00SKj28Tg006Sj21Tg00lAj27Tg003Gj19Tg00?bj2;Tg00Kij2ATg01GKj3@Tg00Hlj65Tg01HSj2>Tg01]Wj2?Tg01^Yj2=Tg018Pg00CeR0f1R1#Cg00A=R2f2R3#6/<1g00IJ32P2f3R4#BR5/43%64R6#:R7'3#01863#0R8'1R9f0R:f4#6R;/74522X02P0%96R<14:4%:;R='3#018;4#0R>'11;;4#0/1>522X50P214<3/37R7%9;/44/3=#0/1>%0:/1>522X02%07/18,A21;63A@63:E5P51>41E517639229e1?431=43E5W1W2W4W3o"). Qed.

Lemma mmap_reserve_refusable_vm : forall md n,
  mmap_reserve_refusable md n = mmap_na_refusable_vm (m_vmmaps md) n.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h02mdh11np;1p;2g011[j12Tg00fPj21Tg00Kij20Tg018Pg00Ceg00A=f1#2f0'1'0W1W0o"). Qed.

Lemma mprotect_refusable_pure : forall md addr n,
  md_pure md -> mprot_leaf (m_vmmaps md) addr n = false ->   (* [comment removed for export] *)
  mprotect_refusable md addr n = mprot_refusable_vm (m_vmmaps md) addr n.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h03Hnlh12Hph24addrh31bh42mdh51np;1p;3p;2p;5p;6g00N@j10Tg00Nej1>Tg00OCj16Tg00o^j15Tg011[j13Tg00Ofj3;Tg00@cj31Tg00Qfj34Tg00Jmj12Tg00Kij27Tg01Z9j38Tg01_bj59Tg00Hlj6:Tg01`nj3=Tg00nWj3<Tg018Pg00Rf#0#0#0#0#0#0#>#6R0f2R1#5g00A=R2f3R3#3f1R47;1g00IJ31P2f4R5#3R6?431R7f0R8#2f5#3?453#2512X32%27,72A8531P5P3P1P4P8D9E:A=531A<631512eW0W1X50W2W4o"). Qed.

(* [comment removed for export] *)
Lemma mmap_model_vm : forall a n md,
  mmap_model a n md = with_vmmaps (vm_mmap a n (m_vmmaps md)) md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah12mdh21np;1p;3p;2g00N@j10Tg00Nej16Tg00OCj12Tg011[j11Tg01b9j35Tg01EMj24Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g018PR1f2f1f0R2#135/42,31W1X20W0o"). Qed.

Lemma noaccess_model_vm : forall a n md,
  noaccess_model a n md = with_vmmaps (vm_noacc a n (m_vmmaps md)) md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah12mdh21np;1p;3p;2g00N@j10Tg00Nej16Tg00OCj12Tg011[j11Tg01c5j35Tg01EMj24Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g018PR1f2f1f0R2#135/42,31W1X20W0o"). Qed.

Lemma mprotect_model_vm : forall a n md,
  mprotect_model a n md = with_vmmaps (vm_unprotect a n (m_vmmaps md)) md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah12mdh21np;1p;3p;2g00N@j10Tg00Nej16Tg00OCj12Tg011[j11Tg00Pej35Tg01EMj24Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g018PR1f2f1f0R2#135/42,31W1X20W0o"). Qed.

Lemma mprotect_model_next_vm : forall a n md,
  mprotect_model_next md a n = with_vmmaps (vm_unprotect a n (m_vmmaps md)) md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah12mdh21np;1p;3p;2g00N@j10Tg00Nej16Tg00OCj12Tg011[j11Tg00Pej35Tg01EMj24Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g018PR1f2f1f0R2#135/42,31W1X20W0o"). Qed.

Lemma munmap_model_pure : forall a n md,
  md_pure md -> munmap_model a n md = with_vmmaps (vm_munmap a n (m_vmmaps md)) md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "p'0h01Hh12Hlh22Hmh32_Hh41ah52mdh61ni009mp_haltedi017mp_lazyi026mp_matp;1p;3p;2p;5g00N@j10Tg00Nej1ATg00OCj16Tg00o^R0j14Tg01d2j3@Tg011[j1<Tg01e2j3;Tg01EMj25Tg00@cj31Tg012Rj17Tg0134j18Tg013kj19Tg00V2j2:Tg014Mj13Tg014mj1?Tg015ej12Tg016Ej1=Tg01f0j5>Tg00Rf#0#0#0#0#0#0#A#6R1g018PR2f0R3#4P0f1R0f4R4f3R5f2R63@%<69;45/56512P3%71%84%91311:11R4#3f5#?%2431%31f6#=%2131f9f8f7P0P3D>W2W1W3P6P0P3O3n101000000130100101102W0W5X61W4o"). Qed.

Lemma fixed_noaccess_model_pure : forall a n md,
  md_pure md -> fixed_noaccess_model a n md = with_vmmaps (vm_fixed_ok a n (m_vmmaps md)) md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "p'0h01Hh12Hlh22Hmh32_Hh41ah52mdh61ni009mp_haltedi017mp_lazyi026mp_matp;1p;3p;2p;5g00N@j10Tg00Nej1ATg00OCj16Tg00o^R0j14Tg01g8j3@Tg011[j1<Tg01hAj3;Tg01EMj25Tg00@cj31Tg012Rj17Tg0134j18Tg013kj19Tg00V2j2:Tg014Mj13Tg014mj1?Tg015ej12Tg016Ej1=Tg01iAj5>Tg00Rf#0#0#0#0#0#0#A#6R1g018PR2f0R3#4P0f1R0f4R4f3R5f2R63@%<69;45/56512P3%71%84%91311:11R4#3f5#?%2431%31f6#=%2131f9f8f7P0P3D>W2W1W3P6P0P3O3n101000000130100101102W0W5X61W4o"). Qed.

Lemma fixed_destroyed_model_pure : forall a n md,
  md_pure md -> fixed_destroyed_model a n md = with_vmmaps (vm_fixed_destroy a n (m_vmmaps md)) md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "p'0h01Hh12Hlh22Hmh32_Hh41ah52mdh61ni009mp_haltedi017mp_lazyi026mp_matp;1p;3p;2p;5g00N@j10Tg00Nej1ATg00OCj16Tg00o^R0j14Tg01jQj3@Tg011[j1<Tg01k[j3;Tg01EMj25Tg00@cj31Tg012Rj17Tg0134j18Tg013kj19Tg00V2j2:Tg014Mj13Tg014mj1?Tg015ej12Tg016Ej1=Tg01l`j5>Tg00Rf#0#0#0#0#0#0#A#6R1g018PR2f0R3#4P0f1R0f4R4f3R5f2R63@%<69;45/56512P3%71%84%91311:11R4#3f5#?%2431%31f6#=%2131f9f8f7P0P3D>W2W1W3P6P0P3O3n101000000130100101102W0W5X61W4o"). Qed.

(* [comment removed for export] *)
Lemma brk_model_grow_vm : forall md req,
  let h := m_vmmaps md in
  (0 < bv_unsigned (vm_brk h))%Z -> (bv_unsigned (vm_brk h) < bv_unsigned req)%Z ->
  brk_model req req md = with_vmmaps (vm_brk_grow req h) md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h04__x1h11Hh21lh32H0h42Hah53Hlth67__arithh74__ffh84__p1h96__sat1h:6__sat2h;8__varmaph<5__with=4__x2h>1bh?3reqh@1EhA2H1hB2H2hC3Hb0hD2HrhE5Hreq0hF1hhG2mdp;1p;2p;3p;6p;4p;8p;7g00N@j16Tg00Nej1wTg00OCj1aTg011[j1DTg01JXj13Tg00TPj20Tg008?j21Tg01n1j1JTg01noj1ETg01oMj2ZTg00G7R0j2CTg00Yej2TTg00@cj37Tg00Lbj6uTg01ojj2oTg020Rj3iTg015ej1MTg014Mj1LTg0216j2QTg021Tj1cTg0222j1bTg022]j2RTg023@j2^Tg013kj1]Tg023cj6\Tg024Gj2[Tg00Kij2KTg024ij2YTg025Uj3XTg0264j4WTg026fj1VTg00V2j2UTg027?j3BTg01EMj25Tg028Bj2=Tg029Gj2OTg00X5j1vTg0066j2<Tg00KKj2STg00Xoj1tTg01UWj3sTg02:Gj3PTg00`?j3>Tg01T]j1nTg02;Fj2ATg02<Ej2NTg01VSj1hTg004bj1gTg01WNj1fTg01XIj1eTg01YBj8:Tg01Lhj3HTg02=Nj4GTg02=nj3ITg007cj28Tg02>Nj1dTg02>lj4jTg02?Jj4FTg02@5j3kTg00Hlj69Tg02A9j6lTg02B=j1mTg00H1j2`Tg00HQj4_Tg02B]j3pTg02C[j7qTg02D?j8rTg00cFR1f0R2'8p=2g00CeR3f1R4g02DcP2CFp=?P4g02EJR5g02EiR6P6g02FIR7P2g00dBFqp=;f3R8P5P6P6P7f2R9P4P2Grp=@g018PR:?742p=4g00RfR;#6R<#6#6#6#6#6R=#wR>#aR?%D4g00Bn%32,0>,11%34,0>10>9'1%J810>8R@#2%E<RA%E=R='ZRB,1@'Cf4R@1T>1RC57?RDP?f5RE%3ERF,0>RG10>2'1X??P9PCP2Eu%3@RH,0>RI10>C'1%JF%2G11GB'C1oA=RC111A%2=111B[[RJ%2ARKg00ihRLAiA=4UW4R=%2B\L^4KRKP0f8RL#3,0>RA#211ABg00iKRAP9f:RM#3,0>#2f;#3,0>RN/1BP0f=,0>RO#211OBPAf9ROf?,0>#2f@RP,0>/1Bp-0RQg02FiRR#MRS%LRRR1Q34%c3RT%b3RU1R3;R;1^31RV'?,;U%]6RWPU1?V;,;UPWPUP5P6P6P7P8E\C@C@1[U7R7P2P9g00A=R6g00A]R5'K1Y29=765dAX314CWR5b7b;b<X03W811211114P8[[^03^8QP2PAfA#3,0>f<RAPPO4b6WBWAP4P2O2n2001000000120000000W3W1P4P2O2n2001000000121000000b9b:b1b5W@%VDRDePD1U??RD#LRP%MDRQf6RV=BEVf7RX'5,=21OVE/5XRY'4X2PP6g00IJRZ%vER[P6PP1<1G/S2%tER\10>VR];sGR^APVVF=>D\R_n0100000020000%nER`1AVF'NRa%hERbPV%gERc%fERd%eEReG:/5X/4YX>6P6PZP[P6PPP2P^P_n0100000020000PaPbPVPcPdPeG:/5X/4YX>6PPP?P?PHAH>EHCG=IDQP[A>D2\PaPbPVPcPdPeG:/5X/4YX2PPPPQP[P?P?PFAH>VFCG=IDQ=>D\1N`2PbPVPcPdPeG:/5X/4YX2P1OE@/5VRP,K:1AEHRYPCPJP=PKP010>XR0#2110B%3X,0>10>L'8P810>O#210>M/1BPSPRP31Q39P4%d3CjPTPU1R3<R<,?;,;UPWP3P;g02GUP<CF,;UC@P7P5b7b;b<X03X=311241849[^03^=3P210>APNPOO3b6W3W1P4P2O2n2001000000120000000b9b:R49kEHROE9APEEHPEPEPHP2P8P9ElE91<1IR1/SZ%m1E910>ER>/<IR1A761Z18G][18I>1<]G=76Z[1`>IP4C_E9AB@EE/5VR@/4Pe1=Q@/4PePYPOE9%DVRO#3,AEABOEE/5V'=/4PROePOeApEEV/4PebEbDW5WCbFW?XG:o"). Qed.

(* [comment removed for export] *)
Lemma brk_model_keep_vm : forall md req, brk_model req (vm_brk (m_vmmaps md)) md = md.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "g02H<o"). Qed.

(* [comment removed for export] *)
Lemma grant_ok_vm_unpack : forall h a n,
  grant_ok_vm h a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + n <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true
  /\ vm_budget_ok h n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01Hh11nh21mh32H0h42H1h52H2h62H3h72b1h82b2h92H4h:2H5h;1ah<1hp;1p;3p;2p;4g00N@j1ATg00Nej1YTg00OCj1STg00j`j3NTg00G7R0j27Tg00M>j2QTg00TPj21Tg00V2j2VTg00?bj2:Tg004Ej2>Tg00U:j1=Tg007cj25Tg00_Bj2FTg00@cj38Tg00ZKj2PTg0066j2JTg008?j2CTg00=Wj2MTg005Yj2ITg00;Uj2OTg00?Gj4ETg00KKj2DTg00__j2KTg00X5j1LTg00Xoj1TTg00`?j3UTg00Yej2XTg00[Ej3WTg00A=R1f0R2g00A]R338p=0f1R4/D2=813p=<A8123,74p=RA8143/72p=Bg00bNR3,K2p=4g00cFR5/J2p=21F45/D2p=Hf2R6/>4%=2'Ip=6f5R7f4R8#Lf3R9#T3U1X427W6p=31D64/D2p=G1K23/F5p=9g00CeR3?825p=@1C52p=?1742,76p=;g00Bng00Rf#A#A#A#A#A#A#YR:#SR;AN642#0P01<42%06R<%04R='7[R>1R=21<64R=[1B9<\=1Q42P4n2001000000120000000X81X71R=P>^81^71R1P211:9R>#4%2>'HA6>681V;;R;P8P8P9P:P6E33GR>1:86R<P4O3%0<,B>P011:8R>#9%2>A6>973GP;P7P7P8P:P9E3'<1:79#011:7R>#4#@%?>1>>8f6R>#='5P;P>P>P7P:P8E3#01:>8#03;3;P211:>R<#9%2<f7R?96<73GP;P?P?P>P:P7E3'<f8R7/:>#0P=P1P2f9R>,1:R?#9%2?f:R<96?73GR?P;P<P<P>P:P7E3R7P6O3%07,B?P011:<R?#4%2?'Hf;R796?>'<P;P7P7P<P:P>E3#011:7R>#4#@%?>1>><f<R>#='5P;P>P>P7P:P<E3#01:><#03;3;P211:>R<#4%2<'Hf=R?96<7'<P;f>R<P<P?P:P>E3#0P=P1P2f?R>,1:R?#4%2?'HR@f@RA96?<R?P6O3%0?,B@P011:AR@#9%2@'<fAR?96@>#011:?R@#4#@%?@1>@AfBR@#='5P;P@P@P?P:PAE3#01:@A#03;3;P211:@RA#9%2A'<fC,1:fD76@#0P=P1P2fE,1:R1#9R=%21R1P6O3%01,B=P0fFR=,1:R1#9#0%21#0fGR1,1:RA#4#@%?A1>A=fHRA#='5P;PAPAP1P:P=E3#01:A=#03;3;P211:A#9#0fI,1:#2#0P01F42#0A8364[R=A83421F64#0R1[A8396\11P42P4n2001000000120000000X23X13P=^23^13P2fK,1:#4R=P5P6O3%@=P01J42#01C64[R=1C421J64#0R1[1C96\11M42P4n2001000000120000000X23X13P=^23^13P2P5fM,1:R5P9O3%?5P01I42#01564[R015421I64#0R5[1596\51O42P4n2001000000120000000X23X13P0^23^13P2fOR0,1:fN'>R5fPR9#=R=P7O3155=11:9R=#4#@%?=R51>=0fQR=#='5R7P;P=P=P9P:P0E3#0R:1:=0#0R='7R0'7R9'7P8P5P9P6P7P0P2P:P=P@PACECECECEb6b0b5b0b4b0W5W4P4P2O2n2001000000121000000b0b3W6W0P4P2O2n2001000000121000000b0b3W9W0P4P2O2n2001000000121000000b0b3W:W0P4P2O2n2001000000121000000b0b3W0X13W;W<o"). Qed.

Lemma grant_ok_na_vm_unpack : forall h a n,
  grant_ok_na_vm h a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + n <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01Hh11nh21mh32H0h42H1h52H2h62H3h72b1h82b2h92H4h:1ah;1hp;1p;3p;2p;4g00N@j1@Tg00Nej1OTg00OCj1MTg00`\j3HTg00KKj25Tg00G7R0j22Tg00M>j2LTg00TPj21Tg004Ej23Tg00U:j14Tg005Yj2:Tg00V2j2NTg00X5j1?Tg00Xoj1=Tg00`?j3>Tg00Yej2;Tg00[Ej3<Tg008?j29Tg007cj28Tg00_Bj2FTg00@cj3ATg00ZKj2KTg0066j2DTg00=Wj2ITg00;Uj2JTg00?Gj4ETg00__j2GTg00A=R1f0R2g00A]3Ap=0g00bNR3,G2g00cFR4'Fp=61D42p=71G23p=Cg00CeR3?A24p=Bg00Bng00Rf#@#@#@#@#@#@#OR5#MR6f2R7f1R8;H2#0P01582#0%07R9%08R:'2[R;%02,2:1578#0R:[f3R<#0/29\:1L82P8n2001000000120000000X81X71R:P;^81^71R1P2115<R;#6%7;'513;7f4R;#4':'5R91N66R6%?;%=;3>1;577<<R=P8O3%09%0='2P0115;R=#6%7='513=<f5R=#4':'5#0%?=%==5>61;5<7<;#0115=R9#C#B1949139;f6R9#4'8%?9%=95>61;5;7<=#0'2'2'2P21159R>#6%7>'513>=f7R>#4':'5#0f8R=#?%==5>61;597<>#0P:P1P2f9R>,15R9#6%79'5R?139=f:R9#4':R=P7O3%0?%0='2P01159R=#6%7='5#013=>f;R=#4':#0115=R>#C#B194>13>9f<R>#4'8%?>%=>5>61;597<=#0'2'2'2P2115>R9#6%79'5#0f=,15/3>f>#4':#0P:P1P2f?,15R1#6R:%71R1P7O3%0:%01'2P0f@R1,15R:#6#0%7:#0fAR:,15R>#C#B194>13>1fBR>#4'8%?>%=>5>61;517<:#0'2'2'2P2115>#6#0fC,15#7#0P01F82#0AA378[R:AA3821F78#0R1[AA3<7\11K82P8n2001000000120000000X23X13P:^23^13P2fE,15#CR:P4P7O3%B:P01D82#01978[R:19821D78#0R1[19<7\11I82P8n2001000000120000000X23X13P:^23^13P2P4fG,15R:P<O3194:P01:82#01878[R018821:78#0R:[18<7\:1J82P8n2001000000120000000X23X13P0^23^13P2fIR0,15fH'3R:fJR<#4R1P=O318:1115<R1#C#B1941R41310fKR1#4'8R:%?1%=15>61;507<<#0R<'2R0'2P;P4P0P7P:P<P2P>CECECEb6b0b5b0b4b0W5W4P8P2O2n2001000000121000000b0b3W6W0P8P2O2n2001000000121000000b0b3W9W0P8P2O2n2001000000121000000b0b3W0X13W:W;o"). Qed.

(* [comment removed for export] *)
Lemma grant_ok_vm_top : forall h a n,
  grant_ok_vm h a n = true -> (bv_unsigned a + n <= alloc_top h)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01Hh12H1h22H2h32H0h42H3h52H4h61ah71hh81np;1p;3p;4p;2p;5g00N@j18Tg00Nej1HTg00OCj1?Tg00j`j3=Tg02I?j4CTg00TPj23Tg00__j2<Tg00@cj39Tg008?j2:Tg004Ej22Tg00U:j14Tg007cj25Tg00V2j2FTg00G7j27Tg02JFj5;Tg00X5j1@Tg00Xoj1ATg00`?j3BTg00Yej2>Tg00[Ej3DTg00?bj2ETg00A=R0f0R1g00A]R239p=Gf5R3f4R4#@f3R5#A3Bf2R6f1R7/>13D=902p=11E71=902p=01771,76p=6g00Bng00Rf#8#8#8#8#8#8#HR2#?R0g00CeR8A=671#GP5P6P7P1CC1326R9g00bNR:'<g00cFR;5981:;91297%45'51F00R0P5P5P6P2P7E1105736361325R7/<:=98;R81:;71276%44'5R7P0P4P4P5P2P6E11046'736P71324R7,:;1275%43'5P0P3P3P4P2P5E11035'7361323R7,:;R;1274f6R7#4'5R6P0P7P7P3P2P4E1107436P61327/23f7R6#4'5P0P6P6P7P2P3E11063361326/27f8R3#4'5R4P0P3P3P6P2P7E11037'7P4P0f9R7P7P3P2P6E11076'7P0f:R0P0P7P2P3E1R610031327/23%40'5f;/07P5W5X26P1D;W4X14P1D;W2X0;P1D;W1X38P1D;b0W0W8W6W7o"). Qed.

Lemma grant_ok_na_vm_top : forall h a n,
  grant_ok_na_vm h a n = true -> (bv_unsigned a + n <= alloc_top h)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01Hh12H1h22H0h32H2h42H3h51ah61hh71np;1p;3p;4p;2p;5g00N@j1;Tg00Nej1DTg00OCj1ATg00`\j3@Tg02Jcj4BTg00TPj2:Tg00__j2?Tg00@cj3=Tg008?j2<Tg004Ej27Tg00U:j18Tg007cj29Tg00V2j2CTg00X5j16Tg00Xoj15Tg00`?j32Tg00Yej24Tg00[Ej33Tg00G7j20Tg02JFj5>Tg00A=f0R0g00A]3=p=1g00Bng00Rf#;#;#;#;#;#;#DR1#AR2g00CeR3f2R4f1R5;@0#1f3R6P4P5P0CB1:14R7g00bNR8'?g00cFR95=31<971775%86'91C22R2%66%56321415734#1'0'0'01:16R7/?8==39R31<971774f4R7#8'9R8%67%575221414736#1'0'0P81:17R8,<91786f5R8#8'9%68%585221416737#1'0'01:18R6,<9R91767f6R6#8'9R4%66%565221417738#1'0P41:16/78f7R4#8'9%64%545221418736#1'01:14/76f8R8#8'9R7%68%585221416734#1P7f9R6#6%565221414738#1P5W4X17P0D>W3X09P0D>W1X23P0D>b0W0W7W5W6o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma vm_mmap_reserved : forall a n h, vm_reserved (vm_mmap a n h) = vm_reserved h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej16Tg00OCj12Tg00V2j21Tg014Mj15Tg00X5j14Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g00Bn1100#5f0#4'3W1X20W0o"). Qed.
Lemma vm_mmap_limit : forall a n h, vm_limit (vm_mmap a n h) = vm_limit h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg004bj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bng00Cef0#1'3W1X20W0o"). Qed.
Lemma vm_mmap_init_sp : forall a n h, vm_init_sp (vm_mmap a n h) = vm_init_sp h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01XIj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_mmap_start_brk : forall a n h, vm_start_brk (vm_mmap a n h) = vm_start_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01VSj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_mmap_mmap_base : forall a n h, vm_mmap_base (vm_mmap a n h) = vm_mmap_base h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01WNj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_mmap_alloc_top : forall a n h, alloc_top (vm_mmap a n h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg00U:j11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bng00Cef0#1'3W1X20W0o"). Qed.
Lemma vm_mmap_brk : forall a n h, vm_brk (vm_mmap a n h) = vm_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01JXj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_mmap_init_sp_ok : forall a n h, init_sp_ok h -> init_sp_ok (vm_mmap a n h).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1g00N@j10Tg00Nej13Tg00OCj12Tg02Kmj11Tg00Rf#0#0#0#0#0#0#3#2R0g00Bnf0R1#1P1UW1X20W0o"). Qed.
Lemma vm_noacc_reserved : forall a n h, vm_reserved (vm_noacc a n h) = vm_reserved h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej16Tg00OCj12Tg00V2j21Tg014Mj15Tg00X5j14Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g00Bn1100#5f0#4'3W1X20W0o"). Qed.
Lemma vm_noacc_limit : forall a n h, vm_limit (vm_noacc a n h) = vm_limit h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg004bj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bng00Cef0#1'3W1X20W0o"). Qed.
Lemma vm_noacc_init_sp : forall a n h, vm_init_sp (vm_noacc a n h) = vm_init_sp h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01XIj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_noacc_start_brk : forall a n h, vm_start_brk (vm_noacc a n h) = vm_start_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01VSj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_noacc_mmap_base : forall a n h, vm_mmap_base (vm_noacc a n h) = vm_mmap_base h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01WNj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_noacc_alloc_top : forall a n h, alloc_top (vm_noacc a n h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg00U:j11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bng00Cef0#1'3W1X20W0o"). Qed.
Lemma vm_noacc_brk : forall a n h, vm_brk (vm_noacc a n h) = vm_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01JXj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_noacc_init_sp_ok : forall a n h, init_sp_ok h -> init_sp_ok (vm_noacc a n h).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1g00N@j10Tg00Nej13Tg00OCj12Tg02Kmj11Tg00Rf#0#0#0#0#0#0#3#2R0g00Bnf0R1#1P1UW1X20W0o"). Qed.
Lemma vm_munmap_reserved : forall a n h, vm_reserved (vm_munmap a n h) = vm_reserved h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej16Tg00OCj12Tg00V2j21Tg014Mj15Tg00X5j14Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g00Bn1100#5f0#4'3W1X20W0o"). Qed.
Lemma vm_munmap_limit : forall a n h, vm_limit (vm_munmap a n h) = vm_limit h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg004bj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bng00Cef0#1'3W1X20W0o"). Qed.
Lemma vm_munmap_init_sp : forall a n h, vm_init_sp (vm_munmap a n h) = vm_init_sp h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01XIj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_munmap_start_brk : forall a n h, vm_start_brk (vm_munmap a n h) = vm_start_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01VSj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_munmap_mmap_base : forall a n h, vm_mmap_base (vm_munmap a n h) = vm_mmap_base h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01WNj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_munmap_alloc_top : forall a n h, alloc_top (vm_munmap a n h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg00U:j11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bng00Cef0#1'3W1X20W0o"). Qed.
Lemma vm_munmap_brk : forall a n h, vm_brk (vm_munmap a n h) = vm_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01JXj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_munmap_init_sp_ok : forall a n h, init_sp_ok h -> init_sp_ok (vm_munmap a n h).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1g00N@j10Tg00Nej13Tg00OCj12Tg02Kmj11Tg00Rf#0#0#0#0#0#0#3#2R0g00Bnf0R1#1P1UW1X20W0o"). Qed.
Lemma vm_fixed_ok_reserved : forall a n h, vm_reserved (vm_fixed_ok a n h) = vm_reserved h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej16Tg00OCj12Tg00V2j21Tg014Mj15Tg00X5j14Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g00Bn1100#5f0#4'3W1X20W0o"). Qed.
Lemma vm_fixed_ok_limit : forall a n h, vm_limit (vm_fixed_ok a n h) = vm_limit h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg004bj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bng00Cef0#1'3W1X20W0o"). Qed.
Lemma vm_fixed_ok_init_sp : forall a n h, vm_init_sp (vm_fixed_ok a n h) = vm_init_sp h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01XIj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_fixed_ok_start_brk : forall a n h, vm_start_brk (vm_fixed_ok a n h) = vm_start_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01VSj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_fixed_ok_mmap_base : forall a n h, vm_mmap_base (vm_fixed_ok a n h) = vm_mmap_base h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01WNj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_fixed_ok_alloc_top : forall a n h, alloc_top (vm_fixed_ok a n h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg00U:j11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bng00Cef0#1'3W1X20W0o"). Qed.
Lemma vm_fixed_ok_brk : forall a n h, vm_brk (vm_fixed_ok a n h) = vm_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01JXj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_fixed_ok_init_sp_ok : forall a n h, init_sp_ok h -> init_sp_ok (vm_fixed_ok a n h).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1g00N@j10Tg00Nej13Tg00OCj12Tg02Kmj11Tg00Rf#0#0#0#0#0#0#3#2R0g00Bnf0R1#1P1UW1X20W0o"). Qed.
Lemma vm_fixed_destroy_reserved : forall a n h, vm_reserved (vm_fixed_destroy a n h) = vm_reserved h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej16Tg00OCj12Tg00V2j21Tg014Mj15Tg00X5j14Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g00Bn1100#5f0#4'3W1X20W0o"). Qed.
Lemma vm_fixed_destroy_limit : forall a n h, vm_limit (vm_fixed_destroy a n h) = vm_limit h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg004bj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bng00Cef0#1'3W1X20W0o"). Qed.
Lemma vm_fixed_destroy_init_sp : forall a n h, vm_init_sp (vm_fixed_destroy a n h) = vm_init_sp h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01XIj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_fixed_destroy_start_brk : forall a n h, vm_start_brk (vm_fixed_destroy a n h) = vm_start_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01VSj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_fixed_destroy_mmap_base : forall a n h, vm_mmap_base (vm_fixed_destroy a n h) = vm_mmap_base h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01WNj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_fixed_destroy_alloc_top : forall a n h, alloc_top (vm_fixed_destroy a n h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg00U:j11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bng00Cef0#1'3W1X20W0o"). Qed.
Lemma vm_fixed_destroy_brk : forall a n h, vm_brk (vm_fixed_destroy a n h) = vm_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01JXj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_fixed_destroy_init_sp_ok : forall a n h, init_sp_ok h -> init_sp_ok (vm_fixed_destroy a n h).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1g00N@j10Tg00Nej13Tg00OCj12Tg02Kmj11Tg00Rf#0#0#0#0#0#0#3#2R0g00Bnf0R1#1P1UW1X20W0o"). Qed.
Lemma vm_unprotect_reserved : forall a n h, vm_reserved (vm_unprotect a n h) = vm_reserved h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej16Tg00OCj12Tg00V2j21Tg014Mj15Tg00X5j14Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g00Bn1100#5f0#4'3W1X20W0o"). Qed.
Lemma vm_unprotect_limit : forall a n h, vm_limit (vm_unprotect a n h) = vm_limit h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg004bj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bng00Cef0#1'3W1X20W0o"). Qed.
Lemma vm_unprotect_init_sp : forall a n h, vm_init_sp (vm_unprotect a n h) = vm_init_sp h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01XIj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_unprotect_start_brk : forall a n h, vm_start_brk (vm_unprotect a n h) = vm_start_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01VSj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_unprotect_mmap_base : forall a n h, vm_mmap_base (vm_unprotect a n h) = vm_mmap_base h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01WNj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_unprotect_alloc_top : forall a n h, alloc_top (vm_unprotect a n h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg00U:j11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bng00Cef0#1'3W1X20W0o"). Qed.
Lemma vm_unprotect_brk : forall a n h, vm_brk (vm_unprotect a n h) = vm_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01JXj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W1X20W0o"). Qed.
Lemma vm_unprotect_init_sp_ok : forall a n h, init_sp_ok h -> init_sp_ok (vm_unprotect a n h).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1g00N@j10Tg00Nej13Tg00OCj12Tg02Kmj11Tg00Rf#0#0#0#0#0#0#3#2R0g00Bnf0R1#1P1UW1X20W0o"). Qed.
Lemma vm_brk_grow_reserved : forall req h, vm_reserved (vm_brk_grow req h) = vm_reserved h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh13reqp;1p;2g00N@j10Tg00Nej16Tg00OCj12Tg00V2j21Tg014Mj15Tg00X5j14Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g00Bn1100#5f0#4'3W0W1o"). Qed.
Lemma vm_brk_grow_limit : forall req h, vm_limit (vm_brk_grow req h) = vm_limit h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh13reqp;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg004bj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2g00Bng00Cef0#1'3W0W1o"). Qed.
Lemma vm_brk_grow_init_sp : forall req h, vm_init_sp (vm_brk_grow req h) = vm_init_sp h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh13reqp;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01XIj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W0W1o"). Qed.
Lemma vm_brk_grow_start_brk : forall req h, vm_start_brk (vm_brk_grow req h) = vm_start_brk h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh13reqp;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01VSj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W0W1o"). Qed.
Lemma vm_brk_grow_mmap_base : forall req h, vm_mmap_base (vm_brk_grow req h) = vm_mmap_base h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh13reqp;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg01WNj11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2R0g00Bnf0#1,30W0W1o"). Qed.
Lemma vm_brk_grow_alloc_top : forall req h, alloc_top (vm_brk_grow req h) = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh13reqp;1p;2g00N@j10Tg00Nej14Tg00OCj12Tg00U:j11Tg00Kij23Tg00Rf#0#0#0#0#0#0#4#2g00Bng00Cef0#1'3W0W1o"). Qed.
Lemma vm_brk_grow_init_sp_ok : forall req h, init_sp_ok h -> init_sp_ok (vm_brk_grow req h).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh13reqp;1g00N@j10Tg00Nej13Tg00OCj12Tg02Kmj11Tg00Rf#0#0#0#0#0#0#3#2g00Bnf0R0#1P0UW0W1o"). Qed.
Lemma vm_brk_grow_brk : forall req h, vm_brk (vm_brk_grow req h) = req.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh13reqp;1p;2g00N@j10Tg00Nej13Tg00OCj12Tg00Kij21Tg00Rf#0#0#0#0#0#0#3#2R0g00Bnf1,10W0W1o"). Qed.
Lemma vm_mmap_maps : forall a n h, vm_maps (vm_mmap a n h) = (a, n) :: vm_maps h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2p;4p;3g00N@j10Tg00Nej18Tg00OCj12Tg00V2j21Tg014Mj17Tg02=Nj46Tg00Xoj13Tg02=nj34Tg00Kij25Tg00Rf#0#0#0#0#0#0#8#2R0g00Bn1100R1#7P0P0f2f1C6f0#3541'5W1X20W0o"). Qed.
Lemma vm_mmap_noaccess : forall a n h, vm_noaccess (vm_mmap a n h) = vm_noaccess h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej16Tg00OCj12Tg00V2j21Tg014Mj15Tg01T]j14Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g00Bn1100#5f0#4'3W1X20W0o"). Qed.
Lemma vm_noacc_maps : forall a n h, vm_maps (vm_noacc a n h) = (a, n) :: vm_maps h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2p;4p;3g00N@j10Tg00Nej18Tg00OCj12Tg00V2j21Tg014Mj17Tg02=Nj46Tg00Xoj13Tg02=nj34Tg00Kij25Tg00Rf#0#0#0#0#0#0#8#2R0g00Bn1100R1#7P0P0f2f1C6f0#3541'5W1X20W0o"). Qed.
Lemma vm_noacc_noaccess : forall a n h, vm_noaccess (vm_noacc a n h) = (a, n) :: vm_noaccess h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2p;4p;3g00N@j10Tg00Nej18Tg00OCj12Tg00V2j21Tg014Mj17Tg02=Nj46Tg01T]j13Tg02=nj34Tg00Kij25Tg00Rf#0#0#0#0#0#0#8#2R0g00Bn1100R1#7P0P0f2f1C6f0#3541'5W1X20W0o"). Qed.
Lemma vm_munmap_maps : forall a n h, vm_maps (vm_munmap a n h) = map_remove (vm_maps h) a.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej17Tg00OCj12Tg00V2j21Tg014Mj16Tg00Xoj15Tg02Llj23Tg00Kij24Tg00Rf#0#0#0#0#0#0#7#2R0g00Bn1100#6f0#5f2'3'4W1X20W0o"). Qed.
Lemma vm_munmap_noaccess : forall a n h,
  vm_noaccess (vm_munmap a n h) = maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2p;3g00N@j10Tg00Nej19Tg00OCj13Tg00V2j22Tg014Mj18Tg01T]j17Tg00TPj21Tg004Ej24Tg01UWj35Tg00Kij26Tg00Rf#0#0#0#0#0#0#9R0#3R1g00Bn1211#8f0#7f2,10R2f1,10,4235'6W1X21W0o"). Qed.
Lemma vm_fixed_ok_maps : forall a n h, vm_maps (vm_fixed_ok a n h) = vm_maps h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej16Tg00OCj12Tg00V2j21Tg014Mj15Tg00Xoj14Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g00Bn1100#5f0#4'3W1X20W0o"). Qed.
Lemma vm_fixed_ok_noaccess : forall a n h,
  vm_noaccess (vm_fixed_ok a n h) = (a, n) :: maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2p;4p;3g00N@j10Tg00Nej1;Tg00OCj13Tg00V2j22Tg014Mj1:Tg02=Nj49Tg01T]j14Tg00TPj21Tg004Ej25Tg01UWj36Tg02=nj37Tg00Kij28Tg00Rf#0#0#0#0#0#0#;R0#3R1g00Bn1211R2#:P1P1f2R3f1R4C9f0#41103R31104,5336572'8W1X21W0o"). Qed.
Lemma vm_fixed_destroy_maps : forall a n h,
  vm_maps (vm_fixed_destroy a n h) = maps_subtract (vm_maps h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2p;3g00N@j10Tg00Nej19Tg00OCj13Tg00V2j22Tg014Mj18Tg00Xoj17Tg00TPj21Tg004Ej24Tg01UWj35Tg00Kij26Tg00Rf#0#0#0#0#0#0#9R0#3R1g00Bn1211#8f0#7f2,10R2f1,10,4235'6W1X21W0o"). Qed.
Lemma vm_fixed_destroy_noaccess : forall a n h,
  vm_noaccess (vm_fixed_destroy a n h) = maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2p;3g00N@j10Tg00Nej19Tg00OCj13Tg00V2j22Tg014Mj18Tg01T]j17Tg00TPj21Tg004Ej24Tg01UWj35Tg00Kij26Tg00Rf#0#0#0#0#0#0#9R0#3R1g00Bn1211#8f0#7f2,10R2f1,10,4235'6W1X21W0o"). Qed.
Lemma vm_unprotect_maps : forall a n h, vm_maps (vm_unprotect a n h) = vm_maps h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2g00N@j10Tg00Nej16Tg00OCj12Tg00V2j21Tg014Mj15Tg00Xoj14Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g00Bn1100#5f0#4'3W1X20W0o"). Qed.
Lemma vm_unprotect_noaccess : forall a n h,
  vm_noaccess (vm_unprotect a n h) = maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01ah11hh21np;1p;2p;3g00N@j10Tg00Nej19Tg00OCj13Tg00V2j22Tg014Mj18Tg01T]j17Tg00TPj21Tg004Ej24Tg01UWj35Tg00Kij26Tg00Rf#0#0#0#0#0#0#9R0#3R1g00Bn1211#8f0#7f2,10R2f1,10,4235'6W1X21W0o"). Qed.
Lemma vm_brk_grow_maps : forall req h, vm_maps (vm_brk_grow req h) = (vm_brk h, (req - vm_brk h)%bv) :: vm_maps h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh13reqp;1p;2p;3p;4g00N@j10Tg00Nej1:Tg00OCj12Tg00V2j21Tg014Mj19Tg01JXj18Tg01Lhj33Tg02=Nj44Tg00Xoj15Tg02=nj36Tg00Kij27Tg00Rf#0#0#0#0#0#0#:R0#2R1g00Bn1111R2#9P1P1f0R1#8R3f1=303C4%51562'7W0W1o"). Qed.
Lemma vm_brk_grow_noaccess : forall req h, vm_noaccess (vm_brk_grow req h) = vm_noaccess h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01hh13reqp;1p;2g00N@j10Tg00Nej16Tg00OCj12Tg00V2j21Tg014Mj15Tg01T]j14Tg00Kij23Tg00Rf#0#0#0#0#0#0#6#2R0g00Bn1100#5f0#4'3W0W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition init_sp_win (h : VmMaps) : Prop :=
  (sp_window_lo <= bv_unsigned (vm_init_sp h) <= sp_window_hi)%Z.

Lemma init_sp_win_ok : forall h, init_sp_win h -> init_sp_ok h.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01Hh12H0h22_Hh31hp;1p;2g02Mej16Tg00N@j10Tg00Nej14Tg01XIj12Tg00TPj23Tg007cj21Tg02Kmj15Tg00Bnf0R0#6g00G7g02NeR1g00Rf#0#0#0#0#0#0#4R2f1R3#2'3R4'1g02O`R5,14f2#5P0f3#2,32,11f4#2,32/15P3W2W0P3P0O2n2001000000120000000W1W3o"). Qed.

Lemma init_sp_win_init_model : forall reserved brk0 mbase sp lim inp,
  valid_sp sp -> init_sp_win (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01Hh13Hhih23Hloh32_Hh44brk0h53inph63limh75mbaseh88reservedh92spp;1p;2p;6p;4p;3g00N@j12Tg00Nej1ATg00OCj1;Tg00V2j29Tg014Mj1@Tg02P[j1<Tg00TPj21Tg007cj20Tg01noj1:Tg00__j24Tg00G7R0j26Tg02QPj65Tg011[j18Tg02Mej17Tg01XIj1?Tg00?Gj4=Tg00@cj3>Tg00CeR1f0R2g00cF3>p=3g00Rf#2#2#2#2R3#2#2#AR4#;R5/95#@g02RIf2R6#<P0g02NeR7f3R8,14R9'0g02O`R:,09%:3R3,49#3'6f7R9f6R;f5R<f4P8P6E5#8#7P2114<,07114;R6/0:1463#3'6P01149R0/0:1403#3f;R0f:R6f9R8f8P9P;E5#8#7P21148/0:1146/43#3f>f=f<P0P6P8E5#8R8#?,14R4,07R7104:R4P<f1R<C=1674e%78eW3W1P<P2O2n2001000000120000000W0W2P<P2O2n2001000000121000000W0W5X61X95X75X45W8o"). Qed.

Lemma init_sp_win_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_win h -> init_sp_win h'.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h01Eh11Hh21bh31hh42h'p;1p;3p;2p;6g00N@j10Tg00Nej19Tg00OCj13Tg01XIj11Tg00@cj38Tg02Mej17Tg00TPj24Tg007cj22Tg00G7j25Tg00Hlj66Tg00BnR0g00Rf#0#0#0#0#0#0#9R1#3R2f0R3#1f1R4#138f2R5#7R6P2f3#1g02Ne1413R1'2g02O`,21'5X22P3%15P4E6P6eW1W0X40W3o"). Qed.

(* [comment removed for export] *)
Lemma alloc_top_win : forall h,
  init_sp_win h -> (alloc_ceiling <= alloc_top h <= sp_window_hi - stack_max_size)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h04__x1h11Hh23Hhih33Hloh47__arithh54__ffh68__varmaph75__with81hp;1p;2p;3p;7p;4p;8g02Mej1WTg00N@j10Tg00Nej1GTg01XIj1<Tg00TPj2;Tg007cj21Tg00U:j1ATg01LKj2=Tg00G7R0j2>Tg015ej1FTg014Mj1ETg0216j2DTg021Tj1VTg0222j1UTg022]j2TTg01noj14Tg023@j26Tg013kj1JTg02SCj13Tg02Shj3?Tg02TKj3@Tg02Tnj7HTg024Gj2KTg00Kij2LTg024ij2MTg00@cj3NTg025Uj3OTg0264j4PTg02URj2CTg02?Jj4QTg02C[j7RTg02D?j8STf0R1#0#0p=7%01#0#0#0p=8%01#0#0#0#0#0#0#0p=2g00CeR2f1R3g02GUP1CQp=:P3g02EJR4g02EiR5P5g02FIR6P1g00dBFRp=9%31#3p=I%31#3#3#3p=5f3R7P4P5P5P6f2R8P3P1GSp=Bg00Bn%W1P0g02NeR0g00RfR9#0#7R:#0#7R;#GR<%<3';R='1g02O`R>,1=g02UoR=%A8R?'1g02W1,=>R@,1?'>P1%<7,;<,10f4#<,;</1>g02FiR>#F%E>1D23%V2%U2R>1T29R0%8;R;#0#8#2#2#2#2#4R7,62R?':,9>%J5RAP>%I9#5#5#5R9#3#0#7#8#2#2#2#4RB,62/:0,9>PAP>P4P5P5P6%09#5#5#0#7#8#2#2#4R9,62%4:R:,62%4;R;,62R55?2=?25R59@20R0':,9>A@2?5,:0,9>FHCBCB1K>6P1P8g00A=R>g00A]R6'L1M18=N>6dg00cF=O23CPb5b6b7X02111711B31C:;/C;R;,=8R:,191=7;,1:'>[[^02P1f6#<,;<P3P8O3b4f5#AR8,1=118@'>eW2W3P3P1O2n2001000000121000000W1W8o"). Qed.

Lemma alloc_top_win_vals : forall h,
  init_sp_win h -> (0x7fff7f800000 <= alloc_top h <= 0x7fffff800000)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h04__x1h11Hh22H0h37__arithh44__ffh58__varmaph65__with71hp;1p;2p;3p;8p;4p;7g02Mej1UTg02Wnj2TTg00U:j1<Tg007cj22Tg01LKj2@Tg00G7j27Tg015ej1STg014Mj1MTg0216j2GTg021Tj1ETg0222j1DTg00N@j10Tg01noj16Tg023@j25Tg022]j2RTg02Shj3>Tg02TKj3LTg013kj1FTg02SCj13Tg02D?j8HTg024Gj2ITg00Kij2JTg024ij2KTg00@cj3CTg025Uj3NTg0264j4OTg02URj2?Tg02?Jj4PTg02C[j7QTg02Tnj7ATf0R0#3#3p=B%30#3#3#3p=4%00#0p=9%00#0#0#0p=8%00#0#0#0#0#0#0#0p=1g00CeR1f1R2g02GUP0CPp=:P2g02EJR3g02EiR4P4g02FIR5P0g00dBFQp=;f2R6P3P4P4P5P2P0FAp==g00Bn%U01T20g02Uo%<2R7'2g02O`g02W1'@,27'7g02FiR7#S%M71G12%E1%D1R7P3P4P4P5g00RfR3#B#4#4#4R8#0#4#4#0#9#8#1#1#6R9,511R13R:':,;7R;%03#9R3#0#9#8R<#0#8#1#1#1#1#6R=,51%63R3,51%6<R<,51R>5>1=>1>5L1,::,;75=7%F4%38#4#4#0#9#8#1#1#6R8,51,::,;79=7;GH1I75P0P6g00A=R7g00A]R5'J1K06=C75dg00cF=N12COb4b5b6X0112901?3</?<,@=,20'712921228'7[^01P0f3#<P2O2b3%<6R6,291268'7eb2W1W7o"). Qed.

(* [comment removed for export] *)
Lemma alloc_top_lt_errno : forall h, (alloc_top h + stack_max_size < 2 ^ 64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_VmLedger ()) [] "h02Hah14__x1h24__x2h31Hh47__arithh54__ffh66__sat0h76__sat1h88__varmaph95__with:1hp;1p;2p;3p;4p;7p;8g02Y0j1OTg00U:j14Tg004Ej22Tg008?j21Tg00N@j10Tg01noj16Tg01ojj2?Tg007cj23Tg01oMj2<Tg020Rj3;Tg015ej17Tg014Mj19Tg0216j2:Tg02>Nj1NTg02>lj4MTg021Tj1LTg0222j1DTg022]j25Tg02Ymj3CTg023@j2@Tg00Nej1ATg02ZPj3BTg02?Jj4>Tg02C[j7=Tg013kj1ETg02D?j8FTg024Gj2GTg00Kij2HTg024ij2ITg00@cj3JTg025Uj3KTg0264j48Tg00Bnf0R0#O%40g02W1R1'2g02[3'1g00RfR2#0R3#6R4%03#0#0#0#0R5#6R6'?g00cFR7/1413761<46R8,17[[1374R9g00ihR:f1R;9;46UW01378\:^09g00CeR9g02FiR:#7%9:P9f2R:,:9P;%N9CM%L9%D9R6g02EJR<g02EiR=P=g02FIR>P6P<P=P=P>P9159215935C9g02Dc1@94%A55B9C>g00dBF=R5%E=P5GF1G6>P0P:g00A=R>g00A]R6'H1I0:=J>6dAK97;C8b5b8b9X19W2120;/1812;:/18[^19^29P0P1f4#4f3O3b4b6b7%4;/21/18eb3W:o"). Qed.
