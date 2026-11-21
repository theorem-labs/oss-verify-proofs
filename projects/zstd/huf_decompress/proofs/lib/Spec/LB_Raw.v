(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (33 recorded proofs replaced by written proofs (zcount_map, LRX_eq, n63X_eq and 30 more); QI_fds takes the premise that the kernel build (m_kernel) is unchanged, which KL's vDSO-pair field now reads; QI_after_node supplies it from nstep_kernel). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep KLink KEv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_TF2 MI_WFree2 MI_WGroup MI_WSlot MI_WMalloc MI_WEnframe2 MI_Cnt MI_Sim MI_Contracts
  LB_Logic LB_Kernel LB_KCount LB_Embed LB_Tables LB_Inv LB_Sum LB_Bound LB_Tree LB_StmtA LB_WFree LB_WSlot.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_Raw () := "C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib4Spec6LB_Inv6zcountC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstI59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2hdC59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum<zsum_map_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec5STree;eruns_sbindC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc<enframe_fullC1?~~~~~~~~~~~~~~~C35stdpp4base4fmapC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum:zcount_extC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7map_mapC59OSSVerify5KrLib4Spec6LB_Sum;zcount_consC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C47Corelib7Classes?RelationClasses9ReflexiveC59OSSVerify5KrLib4Spec6LB_Sum=zsum_map_permC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationGPermutation_EquivalenceC46Stdlib7Sorting;Permutation>Permutation_inC59OSSVerify5KrLib4Spec6LB_Sum;zcount_permC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C46Stdlib7Sorting;Permutation?Permutation_mapC35stdpp4base?NoDup_ListNoDupI46Stdlib5Lists4List5NoDup00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list02I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps6membedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw:zcount_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum?zsum_map_nonnegC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw2xsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw2bsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw3LRXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv2LRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw4n63XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3n63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw4R63XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3R63C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim6lafterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim7followkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4prunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<MI_Contracts<cpath_followC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_SimCptree_follow_lafterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim<follow_sbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim<lafter_sbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe4assnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim=strel_followkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Tree<fqtree_ftreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic6mspecLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Tree5fbnd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic;mspecL_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim<strel_lafterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic:mspecL_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim;steq_followC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Embed5qtreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim=ptree_followkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree:ftree_prunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Embed7membedLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim8prun_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree<strel_followC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Tree=qtree_of_fullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Tree:fbnd8_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Tree>qtree_of_full8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl6followC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic:mspecL_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic@mspecL_pointwiseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic:mspecL_seqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw5ROOMXC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec8LB_StmtA4ROOMC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw6LRX_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw7n63X_eqC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6LB_Sum9zsum_consC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec8LB_StmtA4bigbC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C59OSSVerify5KrLib4Spec6MI_Cnt@round_up_pg_specC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6MI_Inv4INVLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6LB_Inv4SINV00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6LB_Inv2AQ00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3PHIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw7R63X_eqC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_orphC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec8LB_WSlot=state_bytes_BC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2x0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw7LBUDGETC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw2QIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Kernel2LIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_KCount2LNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Bound:live_boundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State=vm_live_bytesC59OSSVerify5KrLib4Spec8LB_Bound4ORPHC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5KLink2KL00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic4liveC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C47Corelib7Classes?RelationClassesFEquivalence_TransitiveC46Stdlib7Sorting;Permutation?Permutation_symC47Corelib7Classes?RelationClasses<transitivityK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC59OSSVerify5KrLib4Spec5KLink4vmwfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC59OSSVerify5KrLib4Spec5KLink3ehiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink4wentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink8brk_disjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC59OSSVerify5KrLib4Spec5KLink3eloC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec5KLink4wcovC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv6ld_brkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topK59OSSVerify5KrLib4Spec5KLink2KL01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Kernel2gmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Kernel2BBC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC59OSSVerify5KrLib4Spec9LB_KCount4lcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_KCount8LN_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrLib4Spec5KLink3wwZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv9brk_phase00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib4Spec5KLink7kl_minvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink7kl_haltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw7QI_minvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes>minv_preservedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw6QI_fdsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib4Spec6PState9set_so_psC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw8QI_otherC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState9set_fa_psC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum;zsum_map_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7bighostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables4cmaxC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula02C59OSSVerify5KrLib4Spec9LB_Tables<tab_basic_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables2S_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables8std_spanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7std_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4CAP0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;div_le_monoC59OSSVerify5KrLib4Spec6LB_Inv3CAPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec6LB_Inv6guestsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec9LB_Tables:In_classesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw8CAP_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=add_le_mono_rC59OSSVerify5KrLib4Spec6LB_Inv4NCAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7classesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4PQOKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4gcntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv7ncarvedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw9NCAP_monoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6LB_Inv2AQ01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw8AQ_monoPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6MI_Inv8is_nodupC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C46Stdlib7Sorting;PermutationAPermutation_NoDupC59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext8ce_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext6MR_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_foldC59OSSVerify5KrLib4Spec6LB_Inv4zlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv=is_metakind_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6MI_Ext6ce_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext:ce_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv6apagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Ext8ce_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv7slotclsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4stdgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3MISC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6LB_Inv3nscC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6x_idleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClassesCPreOrder_TransitiveC56Stdlib6ZArith6BinInt1Z:eq_le_inclC59OSSVerify5KrLib4Spec6MI_Ext9ce_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8flat_mapK59OSSVerify5KrLib4Spec6LB_Inv4SINV01C1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listC59OSSVerify5KrLib4Spec9LB_Tables:std_nestedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6extras00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_preorderK47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6MI_Inv9bl_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec6MI_Kit=aptr_eqb_specC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes7reflect00C46Stdlib7Sorting;Permutation@Permutation_reflC46Stdlib5Lists4List:in_map_iffK46Stdlib7Sorting;Permutation;Permutation02K46Stdlib7Sorting;Permutation;Permutation03K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7vm_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw2GTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink8frame_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WFree7free_fqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Tree6fqtreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree5ptreeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv5cpath00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<MI_Contracts5pans0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<MI_Contracts5pupd0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<MI_Contracts;pans0_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic:mspecL_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5cfreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib4Spec6LB_Raw9R63X_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw;bigb_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4FRELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7ir_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl<s_atop_stripC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib4Spec6LB_Raw5QI_GBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5set_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim8free_simC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw9free_simQC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw@INVL_nodup_slotsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw>bl_remove_permC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationDPermutation_cons_invC59OSSVerify5KrLib4Spec8LB_Logic;mspecL_upd'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps8raw_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Sim;INVL_hdr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl<free_controlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7atop_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw;frame_ok_GTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;malloc_coreC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw7mallocKC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6MI_Ext7ctrl_eq01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib4Spec:MI_WMalloc=INVL_set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WGroup6TKS_ofC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec6MI_TF2<TF0_tick_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw@ctrl_eq_set_tickC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw9SINV_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_WFree7AQ_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_StmtA:CORE_POSTQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_TreeBfbnd8_enframe_fullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6mallocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw=malloc_unfoldC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat3N2Z8inj_succC56Stdlib6ZArith4Znat3N2Z6inj_leC56Stdlib6ZArith4Znat3N2Z6inj_ltC59OSSVerify5KrLib4Spec8LB_StmtA4NREQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4pselC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree4steq00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7cmallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WMalloc9CORE_POSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WMalloc>malloc_core_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8MI_WSlot2GPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_TF23TF2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl>strip_set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl@malloc_core_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4CRELC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5strel00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7slot_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl;strip_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl=slot_of_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<MI_WEnframe2:enframe_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9MI_WFree25xpendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree5ftreeC1?~~~~~~~~~~~~~~~C35stdpp4gmap:gmap_emptyC35stdpp4base5emptyK59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8lay_noneC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw8ROOMX_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4MRELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MI_WMalloc;malloc_INVLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw<malloc_fbnd8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Raw;malloc_simQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>size_overflowsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv@cmalloc_overflowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC59OSSVerify5KrLib6Malloc8ProgDeps:raw_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps9fresh_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl>malloc_controlC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bs (k : blk) : cptr * Z := (bslot k, bsize k).
Definition xs (xb : bptr * Z) : cptr * Z := (fst (fst xb), snd xb).

(* [comment removed for export] *)
Definition LRX (X : list (bptr * Z)) (c : Z) : Z := zcount (fun xb => negb (MMAP_THRESHOLD <=? snd xb) && (size_to_class (snd xb) =? c)) X.
Definition n63X (X : list (bptr * Z)) : Z := zcount (fun xb => MMAP_THRESHOLD <=? snd xb) X.
Definition R63X (X : list (bptr * Z)) : Z := zsum (map (fun xb => if MMAP_THRESHOLD <=? snd xb then round_up_pg (snd xb + IB + UNIT) else 0) X).
Definition ROOMX (X : list (bptr * Z)) (P : Z -> Z) (n : Z) : Prop :=
  (n < MMAP_THRESHOLD -> LRX X (size_to_class n) + 1 <= P (size_to_class n))
  /\ (MMAP_THRESHOLD <= n -> n63X X + 1 <= P 63).

Lemma zcount_map {A B} (f : A -> B) (p : B -> bool) l : zcount p (map f l) = zcount (fun x => p (f x)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite !zcount_cons, IH. reflexivity. Qed.

Lemma LRX_eq X BL c : Permutation (map xs X) (map bs BL) -> LRX X c = LR BL c.
Proof.
  intros HP. unfold LRX, LR, isbig.
  transitivity (zcount (fun q : cptr * Z => negb (MMAP_THRESHOLD <=? snd q) && (size_to_class (snd q) =? c)) (map xs X)); [rewrite zcount_map; reflexivity|].
  rewrite (zcount_perm _ _ _ HP), zcount_map. reflexivity.
Qed.
Lemma n63X_eq X BL : Permutation (map xs X) (map bs BL) -> n63X X = n63 BL.
Proof.
  intros HP. unfold n63X, n63, isbig.
  transitivity (zcount (fun q : cptr * Z => MMAP_THRESHOLD <=? snd q) (map xs X)); [rewrite zcount_map; reflexivity|].
  rewrite (zcount_perm _ _ _ HP), zcount_map. reflexivity.
Qed.
Lemma R63X_eq X BL : Permutation (map xs X) (map bs BL) -> R63X X = R63 BL.
Proof.
  intros HP. unfold R63X, R63, isbig.
  transitivity (zsum (map (fun q : cptr * Z => if MMAP_THRESHOLD <=? snd q then round_up_pg (snd q + IB + UNIT) else 0) (map xs X))); [rewrite map_map; reflexivity|].
  rewrite (zsum_map_perm _ _ _ HP), map_map. reflexivity.
Qed.
Lemma ROOMX_eq X BL P n : Permutation (map xs X) (map bs BL) -> ROOMX X P n -> ROOM BL P n.
Proof. intros HP [R1 R2]. split; [rewrite <- (LRX_eq X BL _ HP); exact R1| rewrite <- (n63X_eq X BL HP); exact R2]. Qed.

Lemma R63X_cons p n X : R63X ((p, n) :: X) = bigb n + R63X X.
Proof. unfold R63X, bigb. cbn [map snd]. rewrite zsum_cons. reflexivity. Qed.
Lemma R63X_nonneg X : 0 <= R63X X.
Proof.
  unfold R63X. apply zsum_map_nonneg. intros xb _. destruct (Z.leb_spec MMAP_THRESHOLD (snd xb)); [| lia].
  pose proof (round_up_pg_spec (snd xb + IB + UNIT)). unfold MMAP_THRESHOLD, IB, UNIT in *. lia.
Qed.
Lemma bigb_nonneg n : 0 <= bigb n.
Proof. unfold bigb. destruct (Z.leb_spec MMAP_THRESHOLD n); [| lia]. pose proof (round_up_pg_spec (n + IB + UNIT)). unfold MMAP_THRESHOLD, IB, UNIT in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LBUDGET : Z := 2^31 - 2^26.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition QI (X : list (bptr * Z)) (P : Z -> Z) : assn PState := fun s mo =>
  (exists st L BL LS, strip st = ps_m s /\ INVL x0 st L BL LS /\ SINV x0 st BL /\ AQ st BL P
      /\ KL L (ps_brk s) mo /\ LI L mo /\ LN L mo /\ Permutation (map xs X) (map bs BL))
  /\ PHI P + R63X X <= LBUDGET.
(* [comment removed for export] *)

Lemma QI_GB st L BL LS P X : INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P ->
  Permutation (map xs X) (map bs BL) -> PHI P + R63X X <= LBUDGET -> gm L + BB L <= LBUDGET.
Proof.
  intros INV SI HAQ HP HB. rewrite (R63X_eq _ _ HP) in HB.
  exact (state_bytes_B x0 st L BL LS P LBUDGET INV eq_refl eq_refl SI HAQ ltac:(unfold PGSZ; lia)).
Qed.

Lemma QI_live X P s mo : QI X P s mo -> live mo <= LBUDGET.
Proof.
  intros [(st & L & BL & LS & _ & INV & SI & HAQ & HK & HL & HN & HP) HB].
  pose proof (live_bound x0 st L BL LS P INV SI HAQ (ps_brk s) mo eq_refl HK HL) as LB.
  unfold ORPH in LB. cbn [x_orph x0] in LB. rewrite <- (R63X_eq X BL HP) in LB. unfold live, PGSZ in *. lia.
Qed.

Lemma QI_perm X Y P s mo : Permutation X Y -> QI X P s mo -> QI Y P s mo.
Proof.
  intros HXY [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HN & HP) HB]. split.
  - exists st, L, BL, LS. repeat (split; [assumption|]). etransitivity; [| exact HP]. apply Permutation_map. apply Permutation_sym. exact HXY.
  - rewrite <- (zsum_map_perm _ _ _ HXY) || idtac. unfold R63X in *. rewrite (zsum_map_perm _ _ _ (Permutation_sym HXY)). exact HB.
Qed.

Lemma QI_fds X P s mo mo' : QI X P s mo -> m_vmmaps mo' = m_vmmaps mo -> m_kernel mo' = m_kernel mo -> minv mo' -> m_halted mo' = None -> QI X P s mo'.
Proof.
  intros [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HN & HP) HB] Hvm Hkb Hmi Hh. split; [| exact HB].
  exists st, L, BL, LS. repeat (split; [assumption|]). split; [| split; [| split; [| exact HP]]].
  - destruct HK; constructor; try (rewrite Hvm); try (rewrite Hkb); auto.
  - unfold LI in *. rewrite Hvm. exact HL.
  - apply (LN_frame L L mo); try (rewrite Hvm); auto.
Qed.

Lemma QI_minv X P s mo : QI X P s mo -> minv mo /\ m_halted mo = None.
Proof. intros [(st & L & BL & LS & _ & _ & _ & _ & HK & _) _]. split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]. Qed.

Lemma QI_after_node X P s mo n rsp mo' evs :
  QI X P s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> QI X P s mo'.
Proof.
  intros HQ Hst Hvm. destruct (QI_minv _ _ _ _ HQ) as [Hmi Hh]. pose proof (nstep_kernel _ _ _ _ _ Hst) as Hkb.
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hst) as [Hh' Hmi']. eapply QI_fds; eauto.
Qed.

(* [comment removed for export] *)
Lemma QI_other X P s s' mo : QI X P s mo -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> QI X P s' mo.
Proof.
  intros [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HN & HP) HB] Hm Hb. split; [| exact HB].
  exists st, L, BL, LS. rewrite Hm, Hb. repeat (split; [assumption|]). exact HP.
Qed.
Lemma QI_set_so X P s mo v : QI X P s mo -> QI X P (set_so_ps v s) mo.
Proof. intros H. eapply QI_other; [exact H| reflexivity| reflexivity]. Qed.
Lemma QI_set_fa X P s mo v : QI X P s mo -> QI X P (set_fa_ps v s) mo.
Proof. intros H. eapply QI_other; [exact H| reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma zsum_map_le' {A} (f g : A -> Z) l : (forall x, In x l -> f x <= g x) -> zsum (map f l) <= zsum (map g l).
Proof. apply zsum_map_le. Qed.

Lemma CAP_mono P P' c : (forall c, P c <= P' c) -> CAP P c <= CAP P' c.
Proof.
  intros HP. unfold CAP, HOSTSTD.
  assert (zsum (map (fun c' => if bighost c' =? c then (CAP0 P c' + 32) / cmax c' else 0) guests)
          <= zsum (map (fun c' => if bighost c' =? c then (CAP0 P' c' + 32) / cmax c' else 0) guests)); [| assert (C0 : CAP0 P c <= CAP0 P' c) by (unfold CAP0; specialize (HP c); lia); lia].
  apply zsum_map_le. intros c' Hc'. destruct (bighost c' =? c); [| lia].
  assert (G : 0 <= c' < 48) by (unfold guests in Hc'; cbn in Hc'; lia).
  pose proof (tab_basic_ok c' G) as (_ & CM & _). apply Z.div_le_mono; [lia|]. assert (C0 : CAP0 P c' <= CAP0 P' c') by (unfold CAP0; specialize (HP c'); lia). lia.
Qed.
Lemma NCAP_mono P P' : (forall c, P c <= P' c) -> NCAP P <= NCAP P'.
Proof.
  intros HP. unfold NCAP, NG.
  assert (zsum (map (fun c => (CAP P c + 32) / cmax c + 160) classes) <= zsum (map (fun c => (CAP P' c + 32) / cmax c + 160) classes)); [| specialize (HP 63); lia].
  apply zsum_map_le. intros c Hc. apply In_classes in Hc. pose proof (tab_basic_ok c Hc) as (_ & CM & _).
  pose proof (CAP_mono P P' c HP). apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
Qed.
(* [comment removed for export] *)
Lemma AQ_monoP st BL P P' : (forall c, P c <= P' c) -> PQOK P' -> AQ st BL P -> AQ st BL P'.
Proof.
  intros HP PQ A. destruct A as [A1 A2 A3 A4 A5 A6]. constructor.
  - intros c Hc. specialize (A1 c Hc). specialize (HP c). lia.
  - intros c Hc. pose proof (CAP_mono P P' c HP). specialize (A2 c Hc). lia.
  - specialize (HP 63). lia.
  - pose proof (NCAP_mono P P' HP). lia.
  - intros c. specialize (A5 c). specialize (HP c). lia.
  - exact PQ.
Qed.
Lemma QI_monoP X P P' s mo : (forall c, P c <= P' c) -> PQOK P' -> PHI P' + R63X X <= LBUDGET -> QI X P s mo -> QI X P' s mo.
Proof.
  intros HP PQ HB [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HN & HPm) _]. split; [| exact HB].
  exists st, L, BL, LS. repeat (split; [assumption|]). split; [exact (AQ_monoP st BL P P' HP PQ HAQ)|]. auto.
Qed.

Lemma QI_nodup X P s mo : QI X P s mo -> List.NoDup (map (fun xb => fst (fst xb)) X).
Proof.
  intros [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HN & HP) _].
  pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) as ND.
  assert (ND' : List.NoDup (map bslot BL)) by (apply NoDup_ListNoDup; exact ND).
  assert (E1 : map (fun xb : bptr * Z => fst (fst xb)) X = map fst (map xs X)) by (rewrite map_map; reflexivity).
  assert (E2 : map bslot BL = map fst (map bs BL)) by (rewrite map_map; reflexivity).
  rewrite E1. rewrite E2 in ND'. eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact HP| exact ND'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma SINV_ctrl X st st1 BL : ctrl_eq st st1 -> SINV X st BL -> SINV X st1 BL.
Proof.
  intros CE S.
  assert (MR1 : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; exact (ce_metas _ _ CE)).
  assert (NC : ncarved st1 = ncarved st) by (unfold ncarved; rewrite (ce_metas _ _ CE); reflexivity).
  assert (AP : apages st1 = apages st).
  { unfold apages, regions_l, frontier. rewrite (ce_regions _ _ CE), (ce_ctx _ _ CE). reflexivity. }
  assert (SCL : forall s, slotcls st1 s = slotcls st s) by (intros s; unfold slotcls, cls; rewrite (ce_slots _ _ CE); destruct (s_slots st !! s) as [[? ?]|]; [rewrite MR1|]; reflexivity).
  assert (STD : forall x, stdg st1 x = stdg st x) by (intros x; unfold stdg, cls; rewrite !MR1; reflexivity).
  destruct S as [qb_cls qb_mis qg_map qg_std qg_small qg_63 qg_host qm_leak qm_pages qm_brk qm_len qm_dist qm_shift].
  constructor; rewrite ?(ce_slots _ _ CE), ?(ce_groups _ _ CE), ?(ce_metas _ _ CE), ?(ce_regions _ _ CE), ?(ce_ctx _ _ CE), ?NC, ?AP; auto.
  - intros k Hk. destruct (qb_cls k Hk) as (m0 & i0 & H0 & H1 & H2). exists m0, i0. rewrite !MR1. auto.
  - intros c'. etransitivity; [| apply (qb_mis c')]. apply Z.eq_le_incl. unfold MIS. apply zcount_ext. intros k _. rewrite SCL. reflexivity.
  - intros b m' ai Hg. rewrite !MR1. intros A1 A2. exact (qg_map _ _ _ Hg A1 A2).
  - intros b m' ai Hg. rewrite STD, !MR1. intros SG. destruct (qg_std _ _ _ Hg SG) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3].
    intros Z0. destruct (Q2 Z0) as (p' & i' & Hs' & E'). exists p', i'. rewrite (MR1 p'). auto.
  - intros c' Hc'. replace (nsc st1 c') with (nsc st c'); [apply qg_small; exact Hc'|].
    unfold nsc, gmetas, groups_l, cls. rewrite (ce_groups _ _ CE). apply zsum_map_ext. intros mb _. rewrite STD, MR1. reflexivity.
  - intros b m' ai Hg. rewrite !MR1. intros C63. exact (qg_63 _ _ _ Hg C63).
  - intros b m' ai p' i' Hg. rewrite !MR1. intros Z0 Hs'. exact (qg_host _ _ _ _ _ Hg Z0 Hs').
Qed.

Lemma bl_remove_perm k BL : In k BL -> List.NoDup (map bslot BL) ->
  Permutation (map bs BL) (bs k :: map bs (bl_remove (bslot k) BL)).
Proof.
  induction BL as [|k' BL IH]; intros Hin ND; [destruct Hin|]. cbn [map bl_remove].
  inversion ND as [|x l NI ND']; subst.
  destruct (aptr_eqb_spec (bslot k') (bslot k)) as [E|NE].
  - destruct Hin as [->|Hin]; [apply Permutation_refl|].
    exfalso. apply NI. rewrite E. apply in_map_iff. exists k. auto.
  - destruct Hin as [->|Hin]; [congruence|]. cbn [map]. etransitivity; [apply perm_skip; apply IH; assumption| apply perm_swap].
Qed.

Lemma INVL_nodup_slots X st L BL LS : INVL X st L BL LS -> List.NoDup (map bslot BL).
Proof. intros INV. apply NoDup_ListNoDup. exact (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.

Definition GT : PState -> Model -> Prop := fun _ _ => True.
Lemma frame_ok_GT : frame_ok GT.
Proof. intros s s' mo mo' _ _ _ _. exact I. Qed.

Section RAWQ.
Hypothesis MQ : malloc_core_fq_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma free_simQ st L BL LS P c off n (o : unit) ans o' st' :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> In ((c, off), n) BL ->
  follow (prun pans0 pupd0 o (free st (Some (aadd c (UNIT * off))))) ans = Some (o', st') ->
  SINV x0 st' (bl_remove c BL) /\ AQ st' (bl_remove c BL) P.
Proof.
  intros INV SI HAQ Hk Hf.
  pose proof (free_fq st L BL LS P c off n (PHI P + R63 BL) INV SI HAQ Hk ltac:(unfold PGSZ; lia)) as FQ.
  pose proof (ftree_prun pans0 pupd0 pans0_range _ L _ o (@fqtree_ftree _ _ _ _ _ FQ)) as PT.
  destruct (ptree_follow_lafter _ L _ ans PT Hf) as [_ (LS' & _ & S' & A')]. split; assumption.
Qed.

Theorem raw_free_L X P p n :
  mspecL LBUDGET (QI ((p, n) :: X) P) (raw_free p) (fun _ => QI X P).
Proof.
  unfold raw_free.
  eapply mspecL_bind; [apply mspecL_get|]. intros s0.
  apply mspecL_pointwise. intros s1 mo1 [-> [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HN & HP) HB]].
  assert (Hin : In (fst p, n) (map bs BL)) by (eapply Permutation_in; [exact HP| left; reflexivity]).
  apply in_map_iff in Hin as ([[c off] n'] & Ebs & Hk). unfold bs in Ebs. cbn in Ebs.
  assert (Ec : c = fst p) by congruence. assert (En : n' = n) by congruence. subst n'.
  rewrite R63X_cons in HB. pose proof (bigb_nonneg n) as BBn.
  pose proof (R63X_eq _ _ HP) as R63E. rewrite R63X_cons in R63E.
  (* [comment removed for export] *)
  assert (QT : qtree LBUDGET L (cfree (ps_m s1) (Some (fst p))) (fun _ _ => True)).
  { rewrite <- E, <- Ec.
    eapply (qtree_of_full pans0 pupd0 pans0_range (RR := FREL)).
    - exact (free_fq st L BL LS P c off n LBUDGET INV SI HAQ Hk ltac:(unfold PGSZ; lia)).
    - exact (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)).
    - intros; exact I. }
  eapply mspecL_bind.
  { replace (s_atop (ps_m s1)) with (ld_atop L) by (rewrite <- E, s_atop_strip; exact (proj1 (proj2 (ir_resv _ _ _ (proj1 INV))))).
    eapply mspecL_pre; [apply (membedL LBUDGET (cfree (ps_m s1) (Some (fst p))) (fun _ _ => True) GT L s1 frame_ok_GT QT ltac:(unfold LBUDGET; lia))|].
    intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK|]. split; [exact HL|]. split; [exact HN|].
    split; [| exact I]. exact (QI_GB st L BL LS P ((p, n) :: X) INV SI HAQ HP ltac:(rewrite R63X_cons; lia)). }
  intros stc'. cbn beta iota.
  apply mspecL_pointwise. intros s2 mo2 (L' & CP & _ & HK' & HL' & HN' & _ & _ & Hm & Hfa & Hso).
  apply mspecL_upd'. intros s mo [-> ->].
  (* [comment removed for export] *)
  destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL2).
  rewrite <- E, <- Ec in Hf, HL2.
  pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
  rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
  unfold FREL in SF. cbn in SF.
  destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (_ & _ & LIVE' & LS' & INV').
  destruct (free_simQ st L BL LS P c off n tt ans o' st' INV SI HAQ Hk FF) as [SI' HAQ'].
  rewrite HL2 in INV'.
  split; [| lia].
  exists st', L', (bl_remove c BL), LS'. cbn [ps_m ps_brk set_m].
  split; [exact SF|]. split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|].
  split; [exact HK'|]. split; [exact HL'|]. split; [exact HN'|].
  pose proof (bl_remove_perm ((c, off), n) BL Hk (INVL_nodup_slots _ _ _ _ _ INV)) as BP. cbn [bs bslot bsize fst snd] in BP.
  apply (Permutation_cons_inv (l:=map xs X) (a:=bs ((c, off), n))). etransitivity; [| exact BP]. etransitivity; [| exact HP]. cbn [map xs fst snd]. unfold bs. cbn [bslot bsize fst snd]. rewrite Ec. apply Permutation_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mallocK (n : Z) (x : mstate * option (aptr * Z)) : M (mstate * optr) :=
  let '(st1, r) := x in
  match r with
  | None => ret (st1, @None aptr)
  | Some (g, idx) => enframe_full st1 g idx n (c_mmap_counter (ctx st1)) (fun st2 p => ret (havoc p n st2, Some p))
  end.

Lemma malloc_unfold st n : malloc st n = sbind (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n) (mallocK n).
Proof. reflexivity. Qed.

Lemma ctrl_eq_set_tick st t : ctrl_eq st (set_tick t st).
Proof. constructor; reflexivity. Qed.

(* [comment removed for export] *)
Lemma malloc_fbnd8 st L BL LS P n B :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> n <= NREQ -> ROOM BL P n ->
  PHI P + R63 BL + bigb n <= B + 3 * PGSZ -> fbnd8 B L (malloc st n).
Proof.
  intros INV SI HAQ Hn HNR HR HB. rewrite malloc_unfold.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  assert (SI0 : SINV x0 st0 BL) by (apply (SINV_ctrl x0 st st0); [apply ctrl_eq_set_tick| exact SI]).
  assert (HAQ0 : AQ st0 BL P) by (apply (AQ_ctrl st st0); [apply ctrl_eq_set_tick| exact HAQ]).
  eapply fbnd8_bind; [exact (MQ st0 L BL LS P n B INV0 TF0' SI0 HAQ0 Hn HNR HR HB)|].
  intros L1 [st1 [[g idx]|]] _; cbn [mallocK].
  - apply fbnd8_enframe_full. intros st' p. exact I.
  - exact I.
Qed.

(* [comment removed for export] *)
Lemma malloc_simQ st L BL LS P n B (o : unit) ans o' st' r :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> n <= NREQ -> ROOM BL P n ->
  PHI P + R63 BL + bigb n <= B + 3 * PGSZ ->
  follow (prun pans0 pupd0 o (malloc st n)) ans = Some (o', (st', r)) ->
  let t := cmalloc (strip st) n in
  let L' := lafter L t ans in
  exists rc, follow t ans = Some (strip st', rc) /\
    match r, rc with
    | None, None => (exists LS', INVL x0 st' L' BL LS') /\ SINV x0 st' BL /\ AQ st' BL P
    | Some pf, Some c => exists off LS', pf = aadd c (UNIT * off)
                         /\ INVL x0 st' L' (((c, off), n) :: BL) LS' /\ SINV x0 st' (((c, off), n) :: BL) /\ AQ st' (((c, off), n) :: BL) P
    | _, _ => False
    end.
Proof.
  intros INV SI HAQ Hn HNR HR HB Hf. cbn zeta.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  assert (SI0 : SINV x0 st0 BL) by (apply (SINV_ctrl x0 st st0); [apply ctrl_eq_set_tick| exact SI]).
  assert (HAQ0 : AQ st0 BL P) by (apply (AQ_ctrl st st0); [apply ctrl_eq_set_tick| exact HAQ]).
  assert (E1 : steq (prun pans0 pupd0 o (malloc st n)) (sbind (prun pans0 pupd0 o (malloc_core full_lay st0 n)) (fun x => prun pans0 pupd0 (fst x) (mallocK n (snd x))))).
  { unfold malloc, prun. apply eruns_sbind. }
  rewrite (steq_follow ans E1) in Hf. rewrite follow_sbind in Hf.
  destruct (followk (prun pans0 pupd0 o (malloc_core full_lay st0 n)) ans) as [[[o1 [st1 rg]] rest]|] eqn:FK; [| discriminate].
  (* [comment removed for export] *)
  pose proof (ftree_prun pans0 pupd0 pans0_range (malloc_core full_lay st0 n) L _ o (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)) as PTC.
  pose proof (ptree_followk _ L _ ans PTC FK) as CP. cbn [snd fst] in CP.
  pose proof (ftree_prun pans0 pupd0 pans0_range (malloc_core full_lay st0 n) L _ o (@fqtree_ftree _ _ _ _ _ (MQ st0 L BL LS P n B INV0 TF0' SI0 HAQ0 Hn HNR HR HB))) as PTQ.
  pose proof (ptree_followk _ L _ ans PTQ FK) as CQ. unfold CORE_POSTQ in CQ. cbn [snd fst] in CQ.
  set (L1 := lafter L (prun pans0 pupd0 o (malloc_core full_lay st0 n)) ans) in *.
  destruct CP as (LIVE1 & GP1 & CP).
  (* [comment removed for export] *)
  pose proof (malloc_core_ctrl pans0 pupd0 n o st0 (strip st) ltac:(unfold st0; rewrite strip_set_tick; reflexivity)) as RELC.
  destruct (strel_followk RELC ans FK) as ([cst1 rg'] & FK2 & [CR1 CR2]). cbn in CR1, CR2. subst rg'.
  assert (FT : follow (cmalloc (strip st) n) ans
               = Some (strip cst1, match rg with Some (g, idx) => Some (slot_of cst1 g idx) | None => None end)).
  { unfold cmalloc. rewrite follow_sbind, FK2. reflexivity. }
  assert (LT : lafter L (cmalloc (strip st) n) ans = L1).
  { unfold cmalloc. rewrite (lafter_sbind _ _ L ans FK2). cbn [lafter]. unfold L1. symmetry. apply (strel_lafter RELC). }
  rewrite LT.
  assert (SS1 : strip cst1 = strip st1) by (rewrite <- CR1; apply strip_strip).
  destruct rg as [[g idx]|].
  - destruct CP as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32).
    set (c0 := (fst bg, sstart (MR st1 g) idx)) in *.
    specialize (CQ bg). fold c0 in CQ.
    assert (Ec0 : slot_of cst1 g idx = c0).
    { rewrite <- CR1, slot_of_strip. unfold slot_of. exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ idx Hg). }
    rewrite Ec0 in FT.
    pose proof (enframe_ft (xpend x0 (Some c0)) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32 (c_mmap_counter (ctx st1))
      (fun _ res => exists off, snd res = Some (aadd c0 (UNIT * off))
                      /\ INVL x0 (fst res) L1 (((c0, off), n) :: BL) LS1 /\ strip (fst res) = strip st1 /\ ctrl_eq st1 (fst res))) as EF.
    cbn [fst snd] in EF.
    specialize (EF ltac:(intros off st2 Ho Hf2 INV2 CE TK; exists off; split; [reflexivity|]; split; [exact INV2|];
                         split; [destruct CE as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10]; unfold strip; rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9, C10; reflexivity| exact CE])).
    pose proof (ftree_prun pans0 pupd0 pans0_range _ L1 _ o1 EF) as PTE.
    cbn [mallocK fst snd] in Hf.
    destruct (ptree_follow_lafter _ L1 _ rest PTE Hf) as [_ (off & Er & INV2 & SS2 & CE2)]. cbn [fst snd] in Er, INV2, SS2, CE2. subst r.
    exists (Some c0). split; [rewrite FT, SS1, SS2; reflexivity|].
    exists off, LS1. split; [reflexivity|]. split; [exact INV2|].
    destruct (CQ off Hg) as [S1 A1].
    split; [exact (SINV_ctrl x0 st1 st' _ CE2 S1)| exact (AQ_ctrl st1 st' _ P CE2 A1)].
  - destruct CP as (LS1 & INV1). cbn [mallocK fst snd] in Hf. rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf. subst o' st' r.
    exists None. split; [rewrite FT, SS1; reflexivity|].
    split; [exists LS1; exact INV1|]. exact CQ.
Qed.

Theorem raw_malloc_L X P n : 0 <= n ->
  mspecL LBUDGET (fun s mo => QI X P s mo /\ ROOMX X P n /\ n <= NREQ /\ PHI P + R63X X + bigb n <= LBUDGET) (raw_malloc n)
         (fun r s mo => match r with
                        | Some p => QI ((p, n) :: X) P s mo /\ n < 2 ^ 63
                        | None => QI X P s mo
                        end).
Proof.
  intros Hn. unfold raw_malloc.
  eapply mspecL_bind; [apply mspecL_get|]. intros s0.
  apply mspecL_pointwise. intros s1 mo1 [-> ([(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HN & HP) HB0] & HRX & HNR & HB)].
  pose proof (R63X_eq _ _ HP) as R63E. pose proof (ROOMX_eq X BL P n HP HRX) as HR.
  assert (HBB : PHI P + R63 BL + bigb n <= LBUDGET + 3 * PGSZ) by (unfold PGSZ; lia).
  (* [comment removed for export] *)
  assert (QT : qtree LBUDGET L (cmalloc (ps_m s1) n) (fun _ _ => True)).
  { rewrite <- E.
    eapply (qtree_of_full8 pans0 pupd0 pans0_range (RR := MREL)).
    - exact (malloc_INVL st L BL LS n INV Hn).
    - exact (malloc_fbnd8 st L BL LS P n LBUDGET INV SI HAQ Hn HNR HR HBB).
    - exact (malloc_control pans0 pupd0 pans0_range st n tt).
    - intros; exact I. }
  eapply mspecL_bind.
  { replace (s_atop (ps_m s1)) with (ld_atop L) by (rewrite <- E, s_atop_strip; exact (proj1 (proj2 (ir_resv _ _ _ (proj1 INV))))).
    eapply mspecL_pre; [apply (membedL LBUDGET (cmalloc (ps_m s1) n) (fun _ _ => True) GT L s1 frame_ok_GT QT ltac:(unfold LBUDGET; lia))|].
    intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK|]. split; [exact HL|]. split; [exact HN|].
    split; [| exact I]. exact (QI_GB st L BL LS P X INV SI HAQ HP HB0). }
  intros [stc' rc]. cbn beta iota.
  apply mspecL_pointwise. intros s2 mo2 (L' & CP & _ & HK' & HL' & HN' & _ & _ & Hm & Hfa & Hso).
  eapply mspecL_seq with (R := fun s mo => s = set_m stc' s2 /\ mo = mo2).
  { apply mspecL_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspecL_ret. intros s mo [-> ->].
  (* [comment removed for export] *)
  destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL2). rewrite <- E in Hf, HL2.
  pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
  destruct (malloc_simQ st L BL LS P n LBUDGET tt ans o' st' rf INV SI HAQ Hn HNR HR HBB FF) as (rc2 & Hf2 & RES).
  rewrite Hf in Hf2. assert (Est : stc' = strip st') by congruence. assert (Erc : rc = rc2) by congruence. subst rc2.
  rewrite HL2 in RES.
  destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
  - destruct RES as (off & LS' & Epf & INV' & SI' & HAQ'). split.
    + split; [| rewrite R63X_cons; lia].
      exists st', L', (((c, off), n) :: BL), LS'. cbn [ps_m ps_brk set_m].
      split; [symmetry; exact Est|]. split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|].
      split; [exact HK'|]. split; [exact HL'|]. split; [exact HN'|].
      cbn [map xs bs fst snd]. unfold bs at 1. cbn [bslot bsize fst snd]. apply perm_skip. exact HP.
    + destruct (size_overflows n) eqn:Eov.
      * exfalso. rewrite (cmalloc_overflow _ _ Eov) in CP. inversion CP.
      * unfold size_overflows in Eov. apply Z.leb_gt in Eov. lia.
  - destruct RES as (INV' & SI' & HAQ'). split; [| lia].
    destruct INV' as [LS' INV'].
    exists st', L', BL, LS'. cbn [ps_m ps_brk set_m].
    split; [symmetry; exact Est|]. split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|].
    split; [exact HK'|]. split; [exact HL'|]. split; [exact HN'| exact HP].
Qed.
End RAWQ.
