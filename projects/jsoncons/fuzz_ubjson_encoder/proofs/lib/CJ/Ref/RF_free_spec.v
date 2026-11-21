(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the auxv as a list of pairs; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/CJ/Ref/RF_free_spec.v, 106 lines within its lines 34-217. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free F_free_spec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMalloc_iface RF_ntf RF_free_K RF_free.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require MallocFacts_inv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require MallocFacts_inv3.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_free_spec () := "C35stdpp4base6LookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad1MC13~~~I35stdpp9countable9Countable00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree4mrunC13~~~C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree<rimplT_reachC13~~~C35stdpp4gmap;gmap_lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree7leaf_ofC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl6followC13~~~C35stdpp4base4fmapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog4bptrC13~~~C46Stdlib5Lists4List2hdI46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;Permutation>Permutation_inI35stdpp4gmap4gmap00C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto8GFormula08C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4cptrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree8rauxv_okC13~~~K47Corelib4Init9Datatypes4list01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree9auxv_listC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr4u64sC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP:secret_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree<rpres_exceptC13~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTreeErpres_except_rw_cellsC13~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTreeErpres_except_bytes_atC13~~~K47Corelib4Init5Logic3and01K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~I47Corelib4Init5Logic2ex00C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init5Logic2ex01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~K47Corelib7Numbers7BinNums1Z01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep:RAUXV_CELLC13~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree3memC13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks5blockC13~~~C47Corelib4Init5Logic6eq_indI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmrep_globalsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_shadowC13~~~I47Corelib4Init9Datatypes4prod00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~K47Corelib4Init9Datatypes6option01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5lr_loC13~~~I47Corelib4Init5Logic2or00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C35stdpp4base6lookupC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RMallocKit_B8rfree_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_free7DROPPEDC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref6RF_ntf;rfree_fp_ltC13~~~C56Stdlib6ZArith6BinInt1Z6moduloC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;ranges_freeC13~~~I47Corelib7Numbers7BinNums1N00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<ref_reservedC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~I47Corelib4Init5Logic5False00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_shadowC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRepBrreserved_disjointC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8lr_lo_geC13~~~K46Stdlib9micromega5Tauto8GFormula07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rgroup_concC13~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z3subC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9cell_readC13~~~K46Stdlib9micromega5Tauto8GFormula06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RCTXC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval00C13~~~K46Stdlib9micromega=RingMicromega3Op201C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface=ralloc_staticC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RF_free_spec;rfp_not_imgC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_free4lbrmC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks8blk_addrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks8blk_sizeC13~~~C35stdpp4base8DecisionC45stdpp;list_basics4list;list_filterC35stdpp4base6filterC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8F_free_K=In_filter_iffC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks8blk_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8aptr_eqbC13~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B9blk_clear00C13~~~C46Stdlib5Lists4List=Forall_forallC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B7ci_bclrC13~~~C47Corelib4Init5Logic5proj1K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;lr_lo_groupC13~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib9LiaTuning9zify_doneC13~~~K46Stdlib9micromega7EnvRing5PExpr05C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic7f_equalC56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr04C57Corelib7BinNums6IntDef1Z3subC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic9False_indC46Stdlib5Lists4List2InC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2IBC13~~~K47Corelib4Init5Logic4True01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface<rclient_addrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<Malloc_iface8in_blockC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RF_free_spec<rfp_not_highC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RF_free_spec=rfp_not_imageC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RF_free_spec=rfp_not_blockC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface:rheap_presC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK46Stdlib9micromega7EnvRing5PExpr07c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RF_free_spec?rfp_not_img_allC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface9rimg_presC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep6RERRNOC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RF_free_spec<rfp_not_deepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface:rdeep_presC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RF_free_spec?rauxv_ok_pres_BC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;F_free_spec>NoDup_map_permC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface5RHEAPC13~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5stripC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface:rfree_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog4ps_mC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog6ps_brkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks8brk_linkC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks;AREACH_from00C13~~~C46Stdlib7Sorting;Permutation?Permutation_symC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent@MallocFacts_inv3Aareach_cinv_proofC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B4CINV00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B6blk_ok00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B7ci_blksC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_slotsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B5hostsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent?MallocFacts_invCareach_hdr_ok_proofC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl6hdr_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog8raw_freeC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref7RF_free9rfree_endC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref7RF_free@rlibc_free_implTC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog5set_mC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate03C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B8ci_nodupC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;F_free_spec>lb_remove_lbrmC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<Malloc_iface9lb_removeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog5ps_faC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog5ps_soC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RF_free_spec=rauxv_ok_freeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;F_free_spec<In_lbrm_permC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RF_free_spec?rheap_pres_freeC13~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RF_free_spec?rdeep_pres_freeC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref<RF_free_spec>rimg_pres_freeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;F_free_spec9lbrm_permC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~C35stdpp4base7is_SomeC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B9ci_gmetasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B9go_regionC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_last_idxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B9sstart_ofC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8m_maplenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9conc_aaddC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks;AREACH_from04C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree@rraw_free_bridgeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad9implM_evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface:rfree_stmtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocHINV9HINV_fromC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad5implMC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B9hdr_knownC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_strideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B9slot_freeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4freeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_brkC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog6PState00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4UNITC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface;RFREE_STACKC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RATPC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface9RFREE_SYMC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree8pans_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree8pupd_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rfree_entryC13~~~K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate01C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate02C13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Lemma rauxv_ok_pres_B : forall C m m' B,
  rauxv_ok m B -> rpres_except C m m' ->
  (forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
  rauxv_ok m' B.
Proof.
  intros C m m' B (av & vs & rnd & C1 & A1 & A2 & H & HL) HP HB HC.
  exists av, vs, rnd. split; [|split; [|split; [|exact (conj H HL)]]].
  - eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

(* [comment removed for export] *)
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 831388 <= a < 831392) m m'.

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 831388 <= a < 831392.

(* [comment removed for export] *)
Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof.
  intros Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). pose_ceil.
  intros [FP|[DR|ER]].
  - pose proof (rfree_fp_lt st m lo sp a MR ltac:(pose_ceil; lia) LS FP). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
  - lia.
Qed.

Lemma rfp_not_img a : 0xb2000 <= a < 0xec000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (831388 <= a < 831392) -> ~ FPT a.
Proof.
  intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). pose_ceil.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + exact (N1 X).
    + destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
    + destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
      destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
    + destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - exact (N2 ER).
Qed.

Lemma rfp_not_image a : 0xb2000 <= a < 0xec000 -> ~ ralloc_static a -> ~ FPT a.
Proof.
  intros Ha NS. apply rfp_not_img; [exact Ha| |]; intros X; apply NS; unfold ralloc_static, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP in *; lia.
Qed.

Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof.
  intros Hb' Hab. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). pose_ceil.
  pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
  destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
  destruct (UNK a Hab) as [h UNKa].
  destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF). pose proof (rreserved_disjoint _ _ RGF) as (?&?&?&?). pose_ceil.
  pose proof (lr_lo_group rg Krg) as LRG.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + unfold RCTX in X. lia.
    + destruct X as (rid & r & Hr & NK & Hin).
      assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
      destruct (DJ _ _ _ _ Hr Hrg NE); lia.
    + destruct X as (b & gh & Hb & Hin). destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
      * specialize (HD b gh Hb E). unfold IB in HD. lia.
      * destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
        pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
    + destruct X as (rid & r & v & Hr & Kr & Hin & HC). destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
      * rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
      * pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - destruct DR as (rid & r & Hr & Hr' & Kr & Hin).
    destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
    assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
    pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - lia.
Qed.

Lemma rheap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> rheap_pres LB' sp m m'.
Proof.
  intros HLB a Ha CA. apply PE; [exact Ha|].
  destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
  - apply rfp_not_high. exact CA.
  - apply rfp_not_image; assumption.
  - apply (rfp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
Qed.

Lemma rfp_not_img_all a : 0x10000 <= a < 0xec000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (831388 <= a < 831392) -> ~ FPT a.
Proof.
  intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). pose_ceil.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + exact (N1 X).
    + destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
    + destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
      destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
    + destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - exact (N2 ER).
Qed.

Lemma rimg_pres_free : rimg_pres m m'.
Proof.
  intros a Ha N1 N2. refine (proj1 (PE a _ _)); [lia| apply rfp_not_img_all; [exact Ha| exact N1| unfold RERRNO in N2; exact N2]].
Qed.

Lemma rfp_not_deep a : alloc_ceiling <= a < lo -> ~ FPT a.
Proof.
  intros Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). pose_ceil.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + unfold RCTX in X. lia.
    + destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
    + destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). pose_ceil. lia.
    + destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
  - lia.
Qed.

Lemma rdeep_pres_free : sp < 2^64 -> rdeep_pres lo m m'.
Proof.
  intros Hsp a Ha. refine (proj1 (PE a _ _)); [pose_ceil; lia| apply rfp_not_deep; exact Ha].
Qed.

Lemma rauxv_ok_free B : rauxv_ok m B -> sp <= B -> rauxv_ok m' B.
Proof.
  intros AV HB. eapply rauxv_ok_pres_B; [exact AV | exact PE | |].
  - intros a Ha. apply rfp_not_high. lia.
  - intros a Ha. apply rfp_not_img; unfold RAUXV_CELL, RLIBC, RCTX in *; lia.
Qed.
End FP.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rfree_spec_proof : rfree_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
         HP Hin AV HB ST LO SLO ERR MI TP A0.
  destruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]).
  assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
  destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  cbn [blk_addr blk_slot fst snd] in OA.
  pose proof (MallocFacts_inv.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.

  eapply (implM_evt rsegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs))).
  { unfold RFREE_SYM. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  eapply (rraw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
            (fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
                               /\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
  - exact Hst.
  - exact HOK.
  - apply rimplT_reach.
    apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
      [unfold RFREE_STACK in SLO; lia | exact ERR | exact A0].
  - intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
    destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR).
    pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
    assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_STACK in SLO; lia).
    unfold rfree_post. do 16 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
    split; [exact (rauxv_ok_free st st' lo (bv_unsigned sp) m m' MR LO SLO' PE B AV HB)|].
    split. { apply (rheap_pres_free st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO SLO' BLKR SHR PE).
             intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
    split. { pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
             exact (rdeep_pres_free st st' lo (bv_unsigned sp) m m' MR SLO' PE ltac:(lia)). }
    split. { exact (rimg_pres_free st st' lo (bv_unsigned sp) m m' MR LO PE). }
    split; [reflexivity|]. split; [reflexivity|].
    exists st', (lbrm LB0 (p, A, n)). split; [rewrite ELB; apply lbrm_perm; exact PERM|].
    split; [reflexivity|]. split; [exact MR'|]. split.
    +   unfold brk_link. cbn [ps_brk set_m]. rewrite EB. unfold brk_link in BL.
      destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
      rewrite ?HB0 in BL. unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
    + destruct LEAF as (ans & o' & FO).
      eapply (areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | exact FO].
      cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
      cbn [fst]. rewrite <- FB. destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _). rewrite Hr. eexists; reflexivity.
Qed.
End CEIL_WRAP_1.

