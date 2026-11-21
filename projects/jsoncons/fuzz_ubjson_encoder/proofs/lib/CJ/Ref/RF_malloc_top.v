(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the auxv as a list of pairs. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocBlocks MallocHINV Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp F_malloc_enf F_malloc_join F_malloc_small F_malloc_entry F_malloc_core F_malloc_top.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_A RMalloc_fp RF_enframe RF_malloc_enf RAllocSlot_iface RF_malloc_entry RF_malloc_join RF_malloc_small RF_malloc_core RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require MallocFacts_inv2.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_malloc_top () := "I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5strel00C13~~~C47Corelib4Init5Logic8eq_ind_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~C47Corelib4Init5Logic6eq_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5sbindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad:implM_bindC13~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl4prunC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree6rimplTC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RF_malloc_topDrmembed_strel_followC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree4mrunC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad5mbindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc1MC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3retC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4bindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog6membedC13~~~C47Corelib4Init9Datatypes3sndC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad5implMC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad9implM_retC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree?rimpl_bind_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad:implM_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4implC13~~~C35stdpp4base;RelDecisionC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTreeCrimplM_membed_sbindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5erunsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree;eruns_sbindC13~~~C35stdpp4gmap;gmap_lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<enframe_fullC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5epostC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree?impl_epost_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl6followC13~~~C35stdpp4base4fmapC35stdpp4base6LookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C46Stdlib5Lists4List8nil_consC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree9strel_indC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog4bptrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad9implM_evtC13~~~I35stdpp4gmap4gmap00C46Stdlib9micromega5Tauto5eKindI46Stdlib9micromega5Tauto8GFormula00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4cptrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad1MC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad4mretC13~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5stripC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog4ps_mC13~~~I47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mallocC13~~~I47Corelib4Init9Datatypes4list00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree7ptr_relC13~~~K47Corelib4Init9Datatypes6option02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog5set_mC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad4mgetC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cmallocC13~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad9implM_getC13~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl4MRELC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl>malloc_controlC13~~~K47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad9implM_updC13~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog:raw_mallocC13~~~K47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog9fresh_offC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad4mupdC13~~~C47Corelib4Init9Datatypes3fstI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree3memC13~~~I47Corelib7Numbers7BinNums1Z00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog6PState00C13~~~I47Corelib4Init9Datatypes4unit00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~I47Corelib7Numbers7BinNums1N00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree8pans_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree8pupd_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree>pans_mem_rangeC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4UNITC13~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks5blockC13~~~C46Stdlib5Lists4List2hdI46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;Permutation>Permutation_inK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmrep_globalsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<rmrep_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMalloc_fp:rmalloc_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~K47Corelib7Numbers7BinNums1Z02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C47Corelib4Init5Logic3notC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5lr_loC13~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMalloc_fpCrreserved_disjoint2C13~~~C47Corelib4Init5Logic9False_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree9ralloc_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp<new_reg_addrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp>free_slot_addrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp<grp_hdr_addrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree:fresh_addrC13~~~I47Corelib4Init5Logic2or00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8lr_lo_geC13~~~C47Corelib4Init5Logic5proj2C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C47Corelib4Init5Logic5proj1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;live_rangesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;ranges_freeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree<rfresh_imageC13~~~C35stdpp4base6lookupC56Stdlib6ZArith6BinInt1Z6moduloC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_A9sstart_ofC13~~~C56Stdlib6ZArith6BinInt1Z3subC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_strideC13~~~C56Stdlib6ZArith6BinInt1Z7testbitC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RCTXC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<ref_reservedC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2IBC13~~~K47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableK47Corelib4Init9Datatypes3nat01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_malloc_top;follow_steqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_malloc_top<follow_sbindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_malloc_top8mrun_fstC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_A8MFACTS_g00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp4mrel00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree<rpres_exceptC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface<rclient_addrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface=ralloc_staticC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<Malloc_iface8in_blockC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_malloc_join@rmalloc_fp_casesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_malloc_join@rmalloc_fp_imageC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks8blk_addrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks8blk_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RMalloc_ifaceP=rblock_insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks8blk_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_next_ridC13~~~C56Stdlib6NArith6BinNat1N2leC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp@round_up_pg_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep;lr_lo_groupC13~~~C56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_A=mf_free_clearC13~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_A<mf_hdr_clearC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTreeAfresh_live_regionC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface:rheap_presC13~~~C46Stdlib5Lists4List2InC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_slotsC13~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init5Logic4True01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9cell_readC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RMalloc_ifacePBrregion_addr_factsC13~~~C56Stdlib6ZArith6BinInt1Z6to_natK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9wr_at_subC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRepBrwr_at_bytes_existC13~~~C47Corelib4Init9Datatypes6lengthC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_freeArw_cells_of_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep<conc_region'C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C46Stdlib9micromega;ZifyClasses5mkappI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface5RHEAPC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree8rauxv_okC13~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTree?rauxv_ok_weakenC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RF_malloc_top@rmalloc_post_fitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog6ps_brkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks8brk_linkC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks;AREACH_from00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent@MallocFacts_inv2Bareach_facts_proofC13~~~C46Stdlib7Sorting;Permutation?Permutation_symC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree;brk_link_psC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocHINV?brk_link_ps_iffC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RF_malloc_top5rmidQC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_malloc_core6rcoreQC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl4CRELC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6s_tickC13~~~C56Stdlib6NArith6BinNat1N4succC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8set_tickC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl@malloc_core_ctrlC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl>strip_set_tickC13~~~C56Stdlib6NArith6BinNat1N2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_malloc_coreBrmalloc_core_implTC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8ticks_okC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp9expo_condC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog5ps_faC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog5ps_soC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7slot_ofC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2pwC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp9unk_agreeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>c_mmap_counterC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp7slot_ok00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_last_idxC13~~~C56Stdlib6ZArith6BinInt1Z3divC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_freeableC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8m_maplenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_sizeclassC13~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=add_le_mono_rC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lC56Stdlib6ZArith6BinInt1Z7mul_1_rC56Stdlib6ZArith6BinInt1Z?mul_add_distr_lC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTreeArpres_except_reflC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RF_malloc_enf:renf_implTC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5havocC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RF_malloc_enf9renf_postC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_malloc_topAmrun_enframe_fullC13~~~C56Stdlib6ZArith6BinInt1Z4landC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:enframe_atC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RF_malloc_top=rimplT_silentC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_malloc_enf8enf_leafC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl@strip_enframe_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl;strip_havocC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_malloc_top=strip_eq_projC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5s_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_metasC13~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl4pselC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec:MallocCtrl;strip_stripC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks;AREACH_from02C13~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RF_malloc_top;ruser_chunkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface<rmalloc_postC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RF_malloc_top9rslot_fitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface<rblock_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface=raddr_exposedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog8ptr_addrC13~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib9LiaTuning9zify_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTreeErpres_except_rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_join9mrel_sameC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp:mrel_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTreeArpres_except_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref;RMallocTreeBrpres_except_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMalloc_fp?rmalloc_fp_monoC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RF_malloc_top@rheap_pres_of_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface:rdeep_presC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface9rimg_presC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref>RF_malloc_joinBrauxv_ok_malloc_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_ifaceArheap_pres_weakenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RF_malloc_topDrmalloc_fp_image_allC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_malloc_top:mod16_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep>round_up_pg_geC13~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib7Sorting;Permutation;Permutation02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_brkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog9reservedZC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog7ps_initC13~~~C35stdpp4gmap:gmap_emptyC35stdpp4base5emptyC47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8fold_offC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_monoC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks;AREACH_from03C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocHINV9HINV_fromC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;malloc_coreC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent@F_malloc_enframe3rdvC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<F_malloc_enf8enf_off0C13~~~K46Stdlib9micromega7EnvRing5PExpr05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK46Stdlib9micromega5Tauto8GFormula07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8lay_noneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8full_layC13~~~C56Stdlib6ZArith4Znat3N2Z8inj_succC56Stdlib6ZArith4Znat3N2Z6inj_ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface=RMALLOC_STACKC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep4RATPC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface;RMALLOC_SYMC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep=rmalloc_entryC13~~~K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep6RMLOCKC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4mctx00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep6RERRNOC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>MMAP_THRESHOLDC13~~~K47Corelib7Numbers7BinNums1N01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RF_malloc_top@rmalloc_stmt_fitC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RF_malloc_topFrmalloc_spec_fit_proofC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface<rmalloc_stmtC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmembed_strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 ->
  forall s (Q1 : R1 -> PState -> machine_state -> Prop) ms,
  implM rsegs (membed t1) s Q1 ms ->
  implM rsegs (membed t2) s
        (fun r2 s' ms' => exists r1 ans, follow t1 ans = Some r1 /\ follow t2 ans = Some r2 /\ RR r1 r2 /\ Q1 r1 s' ms') ms.
Proof.
  induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 ms H.
  - cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1.
    exists r1, []. cbn. auto.
  - cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
    assert (UNR : forall A B (f : exc A -> itree node (exc B)) Qx msx,
              impl rsegs (at_node rsegs) (ITree.bind _ (Ret Unr) f) Qx msx = impl rsegs (at_node rsegs) (f Unr) Qx msx) by reflexivity.
    destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
    5:{ cbn [ev_step] in *. unfold munr in *. cbn [ITree.bind] in *. exact H. }
    5:{ cbn [ev_step] in *. unfold munr in *. cbn [ITree.bind] in *. exact H. }
    all: eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         eapply impl_epost_mono; [eapply IH; exact H1|];
         intros [r2' s2] ms2; cbn; intros (r1' & ans & F1 & F2 & HR & HQ);
         exists r1', (z :: ans); cbn; auto.
Qed.

Lemma rraw_malloc_bridge2 : forall st s n (o : mem) Q1 Q ms,
  strip st = ps_m s ->
  rimplT o (malloc st n) s Q1 ms ->
  (forall st' (p : optr) s' ms' (r : option bptr) ans o' cst c,
     Q1 (st', p) s' ms' -> ptr_rel p r ->
     follow (mrun o (malloc st n)) ans = Some (o', (st', p)) ->
     follow (cmalloc (strip st) n) ans = Some (cst, c) ->
     cst = strip st' ->
     r = match c with Some slot => Some (slot, fresh_off cst slot n) | None => None end ->
     Q r (set_m (strip st') s') ms') ->
  implM rsegs (raw_malloc n) s Q ms.
Proof.
  intros st s n o Q1 Q ms Hst H HQ. unfold raw_malloc.
  eapply (implM_bind rsegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0 s1 ms1 (-> & -> & ->). cbv beta.
  eapply (implM_bind rsegs _ _ _ (fun r s' ms' => exists st' p ans o', Q1 (st', p) s' ms' /\ MREL (o', (st', p)) r
             /\ follow (mrun o (malloc st n)) ans = Some (o', (st', p)) /\ follow (cmalloc (strip st) n) ans = Some r)).
  { rewrite <- Hst. unfold rimplT in H.
    eapply implM_mono.
    - eapply (rmembed_strel_follow MREL (mrun o (malloc st n)) (cmalloc (strip st) n)); [| exact H].
      unfold mrun. apply malloc_control. apply pans_mem_range.
    - intros [cs c] s' ms' ([o1 [st' p]] & ans & F1 & F2 & HR & H1). cbn in H1.
      exists st', p, ans, o1. auto. }
  intros [cs c] s' ms' (st' & p & ans & o' & H1 & HR & F1 & F2). cbv beta iota.
  eapply (implM_bind rsegs _ _ _ (fun _ s2 ms2 => s2 = set_m cs s' /\ ms2 = ms')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done.
  unfold MREL in HR. cbn in HR. destruct HR as [Hs Hp]. subst cs.
  eapply (HQ st' p s' ms' _ ans o' (strip st') c H1); [| exact F1| exact F2| reflexivity| reflexivity].
  destruct p as [pf|], c as [c|]; cbn in Hp |- *; try exact Hp.
Qed.

(* [comment removed for export] *)
Lemma rimplT_silent {R} o (t : Malloc.M R) o' (x : R) s Q ms :
  mrun o t = SRet (o', x) -> rimplT o t s Q ms -> evt rsegs (Q x s) ms.
Proof. intros E H. unfold rimplT in H. rewrite E in H. cbn [membed] in H. unfold implM, mret in H. cbn in H. exact H. Qed.

(* [comment removed for export] *)
Lemma rmalloc_fp_image_all st st2 lo sp m0 m2 a :
  rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a -> alloc_ceiling <= lo ->
  0x10000 <= a < 0xec000 -> RCTX <= a < RCTX + 928 \/ 0xcaf9c <= a < 0xcafa0.
Proof.
  intros (WF & _) (WF2 & _) H CLO HA. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
  pose_ceil.
  assert (IMG : forall P : Prop, (forall rid r, (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)
                 /\ (forall rid r, (s_regions st2) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)).
  { intros P. split; intros rid r Hr Ha.
    - destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia.
    - destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia. }
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. rewrite unsigned_lit in H by lia. lia.
  - left. exact H.
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - exfalso. pose proof WF as (RS & _). pose proof (rfresh_image st a (conj FC FR) RS). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rheap_pres_of_fp st st' LB lo sp m m' :
  RMFACTS st LB -> rmrep st m -> rmrep st' m' -> mrel st st' ->
  rpres_except (rmalloc_fp st st' lo sp) m m' -> alloc_ceiling <= lo -> lo <= sp ->
  rheap_pres LB sp m m'.
Proof.
  intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [exact Ha|]. intros Hfp.
  destruct Hc as [Hsp | [[Himg Hns] | (blk & Hin & Hblk)]].
  - destruct (rmalloc_fp_cases st st' lo sp m m' a MR MR' Hfp); pose_ceil; lia.
  - destruct (rmalloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg); apply Hns; unfold ralloc_static, RERRNO, RATP, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *; lia.
  - destruct (rblock_inside st LB m blk MF MR Hin) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
    pose_ceil.
    pose proof MR' as (WF' & _). pose proof WF' as (_ & WR' & DISJ' & _).
    pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
    destruct REL as [RREG _ _]. destruct (RREG _ _ Hr) as (r1 & Hr1 & K1 & B1 & L1).
    pose proof (round_up_pg_mono _ _ L1) as RL1.
    pose proof (lr_lo_group r1 ltac:(rewrite K1; exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
    destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
    + lia.
    + rewrite unsigned_lit in H by lia. lia.
    + unfold RCTX in H. lia.
    +
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
      destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    +
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
      pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    +
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB) as [_ HB].
        destruct (HB blk Hin (eq_sym E)) as (r'' & Hr'' & DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
        rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    +
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    +
      exfalso. pose proof (fresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ruser_chunk st' m' (p : aptr) r n :
  rmrep st' m' -> (s_regions st') !! (fst p) = Some r -> r_kind r = RKGroup ->
  16 <= snd p -> snd p + n <= round_up_pg (r_len r) -> 0 <= n ->
  exists junk, rw_cells rsegs m' (conc st' p) [CB (Z.to_nat n) junk].
Proof.
  intros MR Hr Hk P0 PN N0.
  pose proof MR as (WF & _ & _ & _ & _ & SH). destruct (SH (fst p) r Hr Hk) as [HW _].
  pose proof (rregion_addr_facts st' m' (fst p) r MR Hr) as (R4 & _ & RC & RI). pose_ceil.
  rewrite (conc_region' st' p r Hr).
  assert (W : wr_at rsegs m' (r_base r + snd p) n) by (eapply wr_at_sub; [exact HW| lia| lia]).
  destruct (rwr_at_bytes_exist m' (r_base r + snd p) n W N0 ltac:(lia)) as (bs & L & B).
  exists bs. apply rw_cells_of_bytes; cbn; [| rewrite app_nil_r; exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W].
  split; [exact L| exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rslot_fit (cs : mstate) (c : cptr) (n : Z) : Prop :=
  forall g i, (s_slots cs) !! c = Some (g, i) -> get_stride (get_meta_rec cs g) - IB - n < 2^31.

Definition rmalloc_post_fit (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) (ms' : machine_state) : Prop :=
  rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m r s' ms'
  /\ match r with Some p => rslot_fit (ps_m s') (fst p) n | None => True end.

Definition rmalloc_stmt_fit : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^40 ->
  implM rsegs (raw_malloc n) s
        (rmalloc_post_fit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs)).

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

(* [comment removed for export] *)
Definition rmidQ (o : mem) (st : mstate) (LB : list block) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
  exists st2 r ans o1,
    fst res = strip st2
    /\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
    /\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
    /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
    /\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

Theorem rmalloc_spec_fit_proof : rmalloc_stmt_fit.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| pose_ceil; lia]).
  destruct HEAP as (st & LB0 & HPERM & Hst & MR & [BLK AR]). rename LB into LBc. rename LB0 into LB.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.

  eapply (implM_evt rsegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                   F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs))).
  { unfold RMALLOC_SYM. step. apply evt_done. reflexivity. }
  intros ms' ->.
  unfold raw_malloc.
  eapply (implM_bind rsegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0' s1' ms1 (-> & -> & ->). cbv beta.
  eapply (implM_bind rsegs _ _ _ (rmidQ m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
  { rewrite <- Hst. unfold cmalloc.
    eapply (rimplM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
              x = (strip st2, r)
              /\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
              /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
              /\ rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
    - eapply implM_mono.
      + eapply (rmembed_strel_follow CREL).
        * pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
          unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
        * unfold rimplT in |- *.
          pose proof (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                        m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
          unfold rimplT in X. exact X.
      + intros [cst2 r'] s' ms'' ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ). unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
        exists st2, r, ans, o1. split; [reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ].
    - intros [cst2 r'] s' ms'' (st2 & r & ans & o1 & E & F1 & F2 & CQ). inversion E; subst. clear E.
      apply implM_ret. apply evt_done. unfold rmidQ. exists st2, r, ans, o1. cbn [fst snd].
      split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ]. }
  intros [cs c] s' ms'' MQ. cbv beta iota.
  destruct MQ as (st2 & r & ans & o1 & Ecs & Ec & F1 & F2 & CQ). cbn [fst snd] in Ecs, Ec. subst cs c.
  pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.
  eapply (implM_bind rsegs _ _ _ (fun _ sx msx => sx = set_m (strip st2) s' /\ msx = ms'')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] sx msx [-> ->]. apply implM_ret.

  assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
                                   | Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
               follow (cmalloc (strip st) n) ans = Some y).
  { intros y Hy. unfold cmalloc. eapply follow_sbind; [exact F2| exact Hy]. }
  destruct r as [[g idx]|].
  -
    cbn [rcoreQ] in CQ.
    destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
                    MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & MREL & BL2 & PSM & PSF & PSO).
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    pose proof (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    pose_ceil. unfold RMALLOC_STACK in LO.
    pose proof (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                  MR2 TK2 UA2 MI2 ST2 ltac:(pose_ceil; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                  ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO) as ENF.
    pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
    pose proof (rimplT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
    eapply evt_mono; [exact EV|]. clear EV.
    intros msf [_ EP]. unfold renf_post in EP.
    destruct EP as (st' & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & LEAF).
    destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    pose proof (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    set (A := conc st' p) in *.

    assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
    { unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
    pose proof (FC (strip st2, Some (slot_of st2 g idx)) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.
    pose proof (areach_malloc_some st LB n m m ans st' p (strip st2) (slot_of st2 g idx) AR ltac:(lia) FF FC1) as AR'.
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    fold A in UCH.
    unfold rmalloc_post_fit. split.
    2:{
        intros g' i' Hs'. cbn [ps_m set_m fst] in Hs' |- *.
        change (s_slots (strip st2)) with (s_slots st2) in Hs'.
        unfold slot_of, slot_start' in Hs'. rewrite Hmem in Hs'. cbn [default from_option id] in Hs'. unfold aadd in Hs'. cbn [fst snd] in Hs'.
        replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + stride * idx) in Hs' by (subst stride; unfold UNIT; lia).
        rewrite SSL in Hs'. inversion Hs'; subst g' i'.
        change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). fold stride. unfold IB. lia. }
    unfold rmalloc_post. do 15 eexists. exists m', errv1.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
             - lia.
             - lia. }
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split. { intros a Ha. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
             apply (proj1 (PEf a ltac:(pose_ceil; lia) ltac:(intros X; destruct (rmalloc_fp_cases st st' lo (bv_unsigned sp) m m' a MR MR' X); pose_ceil; lia))). }
    split. { intros a Ha N1 N2. unfold RERRNO in N2.
             apply (proj1 (PEf a ltac:(lia) ltac:(intros X; destruct (rmalloc_fp_image_all st st' lo (bv_unsigned sp) m m' a MR MR' X CLO Ha); [apply N1| apply N2]; assumption))). }
    split; [exact PSF|]. split; [exact PSO|].
    exists A, ujunk.
    split; [reflexivity|].
    split. { pose_ceil. unfold rblock_range. rewrite EA.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
    split. { exists st'. eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact SE|]. split; [exact MR'|]. split.
             - apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2.
             - exact AR'. }
    split; [exact UCH|].

    intros AE. unfold ptr_addr. cbn [ps_m set_m fst snd].
    assert (X0 : rdv pans_mem m st2 (fst b, snd b + (16 + stride * idx) + -3) = 0).
    { apply EXPO. destruct AE as [AE|AE]; [left; exact AE| right].
      pose proof (f_equal s_regions Hst) as E0. rewrite AE in E0. cbn in E0. exact E0. }
    unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
    match goal with |- context [conc (strip st2) ?q] => change (conc (strip st2) q) with (conc st2 q) end.
    rewrite (conc_region' st2 (fst b, snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) rg Hr). cbn [snd].
    unfold fresh_off. cbn [s_slots strip].
    replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + stride * idx) by (subst stride; unfold UNIT; lia).
    rewrite SSL. change (c_mmap_counter (s_ctx (strip st2))) with (c_mmap_counter (ctx st2)).
    rewrite EA, Eoff. unfold enf_off0. rewrite X0. cbn [Z.eqb]. subst stride. unfold IB, UNIT.
    change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). lia.
  -
    cbn [rcoreQ] in CQ.
    destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
                    MR2 & TK2 & MI2 & ST2 & ERR2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO).
    apply evt_done. unfold rmalloc_post_fit. split; [| exact Logic.I]. unfold rmalloc_post. do 15 eexists. exists m1, errv1.
    pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split. { intros a Ha. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
             apply (proj1 (PE2 a ltac:(pose_ceil; lia) ltac:(intros X; destruct (rmalloc_fp_cases st st2 lo (bv_unsigned sp) m m1 a MR MR2 X); pose_ceil; lia))). }
    split. { intros a Ha N1 N2. unfold RERRNO in N2.
             apply (proj1 (PE2 a ltac:(lia) ltac:(intros X; destruct (rmalloc_fp_image_all st st2 lo (bv_unsigned sp) m m1 a MR MR2 X CLO Ha); [apply N1| apply N2]; assumption))). }
    split; [exact PSF|]. split; [exact PSO|].
    split; [reflexivity|].
    exists st2, LB. split; [exact HPERM|]. split; [reflexivity|]. split; [exact MR2|].
    split.
    + apply (proj1 (brk_link_ps_iff st2 _)). cbn. exact BL2.
    + eapply (areach_malloc_none st LB n m m ans st2 AR ltac:(lia)).
      unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. reflexivity.
Qed.

Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA N.
  eapply implM_mono; [exact (rmalloc_spec_fit_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                F fc m s LB n lo B errv HEAP AUXB SB ST CLO LO ERR MI TP HA N)|].
  intros r s' ms' [H _]. exact H.
Qed.
End TOPLEVEL.
End CEIL_WRAP_1.


