(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem ITree Nodes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore ModelX NodesA.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import BackingAlgebra MainExport MainFactsBoth BothEntry.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Stdio AsanCtrl AsanCtrlProps SizeHist AsanProgDeps
  AsanInv AsanBudget AsanOK RSim RSimProg Prog ProgA EquivPA.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ITreeA.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanHandoff () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrI46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;PermutationGPermutation_EquivalenceC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapK35stdpp8fin_maps6FinMap01I35stdpp4gmap4gmap00I35stdpp8fin_maps6FinMap00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List8map_consC35stdpp4base4FMapC35stdpp8fin_mapsAmap_to_list_emptyC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_foldK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission2AS:MainExport7ivs_sepI5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4seps00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4wsepC46Stdlib5Lists4List<In_nth_errorI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes3nat02C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4seps02C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init9Datatypes3fstC45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init9Datatypes3sndI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4seps01I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic3and00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC5ARocqVerifyHarness?AgentSubmission2AS:MainExport7ivs_sumK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3appK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega3Op201C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission2AS:MainExport:ledger_denK5ARocqVerifyHarness?AgentSubmission2AS:MainExport6lentry01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC47Corelib4Init5Logic9False_indK5ARocqVerifyHarness?AgentSubmission2AS:MainExport6lentry02C5ARocqVerifyHarness?AgentSubmission2AS:MainExport2zvI5ARocqVerifyHarness?AgentSubmission2AS:MainExport6lentry00I5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp00I6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP5mkind00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8pfact_okC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationI5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact00C5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth?asan_pure_factsC47Corelib5Lists7ListDef3mapC35stdpp4base5emptyC35stdpp8fin_maps;map_to_listC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl5ainitC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv;live_chunksK5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01I47Corelib7Numbers7BinNums1N00I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6aclass00I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6abatch00C47Corelib4Init9Datatypes2idC35stdpp4base6lookupC35stdpp8fin_maps<lookup_emptyC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl5a_clsC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7get_clsC35stdpp6option;from_optionC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7aclass0C5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv8qbatchesC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv7qchunksc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoffAlive_chunks_ainitC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv:all_chunksC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4secsc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff@all_chunks_ainitC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv2CHC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv7cls_invC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv8chunk_wfC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl<a_qloc_bytesC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_qlocC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4bsumC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=a_qglob_bytesC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7a_qglobC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nsecC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4zlenC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nresC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nextC56Stdlib6NArith6BinNat1N2ltC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_ptr_arrayC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv;live_budgetC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl@c_allocated_userC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=c_mapped_userC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrlCc_mapped_free_arrayC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;c_num_freedC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7c_countC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl9max_countC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=size_of_classC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4cntPC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv6nbatchC56Stdlib6ZArith6BinInt1Z3eqbK46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z7mul_0_rC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7a_cinitC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:max_cachedc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff=get_cls_ainitK47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4LMAXC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv8secbytesC56Stdlib6ZArith6BinInt1Z3powK46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv:is_prim_ofC46Stdlib5Lists4List6filterc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff8CH_ainitC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4AINVK46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>K_CHUNKS_BLOCKC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv8batch_wfC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_FREEARR_OFFC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:K_USER_MAPC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_FREEARR_MAXC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_FREEARR_MAPC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_BATCH_CLASSC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4SMAXC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv7LSBYTESI47Corelib4Init9Datatypes:comparison00K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact01C56Stdlib5Arith8PeanoNat3Nat3eqbC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC56Stdlib6ZArith6BinInt1Z6eqb_eqK5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact02K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact03K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact04C5ARocqVerifyHarness?AgentSubmission2AS:MainExport8zexp_eqbC5ARocqVerifyHarness?AgentSubmission2AS:MainExport;zexp_eqb_eqc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff9pfact_eqbC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List>existsb_existsc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<pfact_eqb_eqC47Corelib4Init5Logic5proj1C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff4uns2C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List?Forall_cons_iffK47Corelib5Lists7ListDef6Forall02c5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff;Forall_uns2C46Stdlib5Lists4List:length_mapc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff?live_bytes_uns2c5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff=reserved_evalC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv6RES_HIC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4LEN0C5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv5RTOT0C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool=negb_true_iffC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC46Stdlib4Bool4Bool;andb_true_rc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff:pfact_findK47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp01K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp02K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp04K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp05K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp03C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv7PRIM_SZC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv6PTR_SZC5ARocqVerifyHarness?AgentSubmission2AS:MainExport5two64C5ARocqVerifyHarness?AgentSubmission2AS>BackingAlgebra5iv_wfC5ARocqVerifyHarness?AgentSubmission2AS>BackingAlgebra6ivs_wfI5ARocqVerifyHarness?AgentSubmission2AS9BothEntry7amodelL00c5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff?placement_factsC5ARocqVerifyHarness?AgentSubmission4LibA6ModelX2MXC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC5ARocqVerifyHarness?AgentSubmission2AS:MainExport>lentry_kind_okC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC5ARocqVerifyHarness?AgentSubmission2AS:MainExport6in_ivsC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC5ARocqVerifyHarness?AgentSubmission4LibA8AcctCore=nonlazy_bytesC5ARocqVerifyHarness?AgentSubmission2AS:MainExport9ivz_bytesC5ARocqVerifyHarness?AgentSubmission2AS:MainExport6ivz_wfC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedI46Stdlib5Lists4List5NoDup00C4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8aallowedc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff7atop_ofC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv8entry_okC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv7atop_okC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv;noacc_clearc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff7resv_ofC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv2PmC5ARocqVerifyHarness?AgentSubmission2AS>BackingAlgebra9sum_countC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv<commit_bytesC46Stdlib5Lists4List;Forall_implc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff@ivs_wf_of_boundsc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<a_space_beg0c5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<a_ptr_array0c5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<ivs_sep_sepsC4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission4Spec7AsanInvDregion_free_of_bytesC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv5STARTC47Corelib7Classes?RelationClassesEEquivalence_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityC46Stdlib5Lists4List9app_nil_rc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff=ledger_den_Inc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoffAledger_den_lengthC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4wentC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4rcovc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoffCregion_free_of_hullc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff;ivs_sum_appc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff>ivs_sum_nonnegc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoffBlive_bytes_ivs_sumC46Stdlib5Lists4List:Forall_appC46Stdlib5Lists4List:in_map_iffc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff5iv_ofC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List;in_flat_mapC46Stdlib5Lists4List:in_app_iffC46Stdlib5Lists4List7map_appC5ARocqVerifyHarness?AgentSubmission2AS8AsanCeil:init_sp_okC5ARocqVerifyHarness?AgentSubmission4LibA6ModelX?same_but_mat_MXC5ARocqVerifyHarness?AgentSubmission4LibA8AcctCoreDsame_but_mat_nonlazyC5ARocqVerifyHarness?AgentSubmission4LibA6ModelX;m_vmmaps_MXC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInvAnonlazy_sum_countC56Stdlib6ZArith6BinInt1Z7add_0_rc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoffBcommit_bytes_ainitC5ARocqVerifyHarness?AgentSubmission4LibA6ModelX<m_vm_lazy_MXC5ARocqVerifyHarness?AgentSubmission4LibA6ModelXDm_vm_materialized_MXC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv3AMIC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8allow_ofC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv7LIMIT34C5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth;asan_ledgerC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry7AIMG_LOC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry7AIMG_HIC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry6ASHOFFC5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth8asan_visC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv6EAGER0K6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP5mkind01C5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4TOT0I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C5ARocqVerifyHarness?AgentSubmission2AS9BothEntry7V_VMBRKC5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth:asan_totszC5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth:asan_eagerC5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth;asan_abytesI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00c5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff>reserved_factsK6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP5mkind02C5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv5LS_LOC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv5LS_SZC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv5HS_LOC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv5HS_SZK6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP5mkind04C5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv5KHIGHC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv6GAP_LOC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv6GAP_SZI5ARocqVerifyHarness?AgentSubmission2AS9BothEntry6amodel00C5ARocqVerifyHarness?AgentSubmission2AS9BothEntry>amodel_amodelLc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff:AMI_init_LC4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv5LIMITC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv@LIMIT34_le_LIMITC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv8LIMIT_eqC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4minvK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC5ARocqVerifyHarness?AgentSubmission4Spec7EquivPA8init_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEK47Corelib4Init9Datatypes:comparison02C56Stdlib6ZArith6BinInt1Z7div_modC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff@space_beg0_factsC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps8aps_initC5ARocqVerifyHarness?AgentSubmission4Spec6AsanOK2AIC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps6aps_soC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry:amL_haltedC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry7amL_fdsC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry6amL_fsC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry7amL_topC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry7amL_uspC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv3INVC5ARocqVerifyHarness?AgentSubmission4Spec6AsanOK:live_pairsC5ARocqVerifyHarness?AgentSubmission4LibA6ModelX5stripC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv5FAINVC56Stdlib6ZArith6BinInt1Z4of_NC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv2VCC5ARocqVerifyHarness?AgentSubmission4Spec6AsanOK3VCBc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff9AINV_initC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4LibA6ModelX;m_fds_stripC5ARocqVerifyHarness?AgentSubmission4LibA6ModelX;m_tid_stripc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff9minv_fds3C5ARocqVerifyHarness?AgentSubmission4LibA6ModelX8strip_MXC5ARocqVerifyHarness?AgentSubmission4LibA6ModelX;m_halted_MXC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv6vc_clsK5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS01C5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps8aps_resvC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps8aps_atopC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mC5ARocqVerifyHarness?AgentSubmission4LibA6ModelX8m_fds_MXC5ARocqVerifyHarness?AgentSubmission4LibA6ModelX7m_fs_MXI5ARocqVerifyHarness?AgentSubmission4Spec5Stdio9stdout_st00C5ARocqVerifyHarness?AgentSubmission4Spec5Stdio;stdout_initC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7Q_CACHEC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl5Q_MAXC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv4NOPSC5ARocqVerifyHarness?AgentSubmission4Spec7AsanInv7CLASSESc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff9AI_init_LC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff7AI_initC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA4aptrC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA4a_soI6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc00C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC5ARocqVerifyHarness?AgentSubmission4Spec4Prog6argv_ZC5ARocqVerifyHarness?AgentSubmission4Spec5ProgA:progA_treeC5ARocqVerifyHarness?AgentSubmission4Spec4RSim5tglobC5ARocqVerifyHarness?AgentSubmission4Spec4RSim=tglob_trivialC5ARocqVerifyHarness?AgentSubmission4Spec7EquivPA5AHANDC5ARocqVerifyHarness?AgentSubmission4Spec7EquivPA2AIC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps:AAllocAsanC5ARocqVerifyHarness?AgentSubmission4LibA6NodesA6nstepAC5ARocqVerifyHarness?AgentSubmission4Spec6AsanOK4PhiAC5ARocqVerifyHarness?AgentSubmission4LibA6NodesA5minvAC5ARocqVerifyHarness?AgentSubmission4Spec6AsanOK<AAllocAsanOKC5ARocqVerifyHarness?AgentSubmission4Spec8RSimProg8MAIN_OPSI4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I5ARocqVerifyHarness?AgentSubmission3Lib5Nodes4node00K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff:AHAND_initC5ARocqVerifyHarness?AgentSubmission4Spec7EquivPA8equiv_PAI4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C5ARocqVerifyHarness?AgentSubmission5Plain4PImg5psegsC5ARocqVerifyHarness?AgentSubmission5Plain4PImg9p_init_pcC5ARocqVerifyHarness?AgentSubmission5Plain4PImg7p_phdrsC5ARocqVerifyHarness?AgentSubmission4Spec7EquivPA>equiv_PA_toP_LI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00C5ARocqVerifyHarness?AgentSubmission4Spec7EquivPA<equiv_PA_toPc5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<AHAND_init_L".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition a_space_beg0 (V : nat -> Z) : Z := 4096 * V 208%nat - 4096 * V 209%nat + 65536.
Definition a_ptr_array0 (V : nat -> Z) : Z := 4096 * V 226%nat.
(* [comment removed for export] *)
Definition atop_of (sp : word) : Z := bv_unsigned sp - 8388608.
(* [comment removed for export] *)
Definition a_usp0 (V : nat -> Z) : Z := 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ivs_sep_seps : forall l, ivs_sep l -> seps l.
Proof.
  induction l as [|p l IH]; intros H; [constructor|]. constructor.
  - apply Forall_forall. intros q Hq. apply In_nth_error in Hq as [j Hj].
    destruct (H 0%nat (Datatypes.S j) p q ltac:(lia) eq_refl Hj) as [A|B]; unfold wsep; [left; exact A| right; exact B].
  - apply IH. intros i j p' q' Hij Hi Hj. apply (H (Datatypes.S i) (Datatypes.S j) p' q'); [lia| exact Hi| exact Hj].
Qed.

Lemma live_bytes_ivs_sum : forall l, live_bytes l = ivs_sum l.
Proof. induction l as [|[a n] l IH]; [reflexivity|]. cbn [ivs_sum snd]. rewrite <- IH. reflexivity. Qed.

Lemma ivs_sum_app : forall l1 l2, ivs_sum (l1 ++ l2) = ivs_sum l1 + ivs_sum l2.
Proof. induction l1 as [|e l1 IH]; intros; cbn [ivs_sum app]; [lia|]. rewrite IH. lia. Qed.

Lemma ivs_sum_nonneg : forall l, 0 <= ivs_sum l.
Proof. induction l as [|e l IH]; cbn [ivs_sum]; [lia|]. pose proof (bv_unsigned_in_range _ (snd e)). lia. Qed.

Lemma ledger_den_In : forall V l maps, ledger_den V l maps ->
  forall b n k, In (LMap b n k) l -> In (wa (zv V b), wa n) maps.
Proof.
  induction l as [|[b n k|n] l IH]; intros maps HD b' n' k' Hin; cbn [ledger_den] in HD.
  - contradiction.
  - destruct HD as (maps' & -> & HD'). destruct Hin as [E|Hin].
    + injection E as -> -> ->. left. reflexivity.
    + right. eapply IH; eauto.
  - destruct Hin as [E|Hin]; [discriminate|].
    destruct HD as [HD'|(iv & maps' & -> & _ & HD')]; [eapply IH; eauto| right; eapply IH; eauto].
Qed.

Lemma ledger_den_length : forall V l maps, ledger_den V l maps -> (length maps <= length l)%nat.
Proof.
  induction l as [|[b n k|n] l IH]; intros maps HD; cbn [ledger_den] in HD.
  - subst maps. cbn. lia.
  - destruct HD as (maps' & -> & HD'). cbn. pose proof (IH _ HD'). lia.
  - destruct HD as [HD'|(iv & maps' & -> & _ & HD')]; cbn; pose proof (IH _ HD'); lia.
Qed.

(* [comment removed for export] *)
Lemma pfact_In : forall V f, Forall (pfact_ok V) asan_pure_facts -> In f asan_pure_facts -> pfact_ok V f.
Proof. intros V f H Hin. rewrite Forall_forall in H. apply H, Hin. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_chunks_ainit : forall sb pa, live_chunks (ainit sb pa) = [].
Proof. intros. unfold live_chunks, ainit. cbn [a_live]. rewrite map_to_list_empty. reflexivity. Qed.

Lemma get_cls_ainit : forall sb pa c, get_cls (ainit sb pa) c = aclass0.
Proof. intros. unfold get_cls, ainit. cbn [a_cls]. rewrite lookup_empty. reflexivity. Qed.

Lemma all_chunks_ainit : forall sb pa, all_chunks [] [] (ainit sb pa) = [].
Proof. intros. unfold all_chunks. rewrite live_chunks_ainit. reflexivity. Qed.

Lemma CH_ainit : forall sb pa, CH [] [] (ainit sb pa) = [].
Proof. intros. unfold CH. rewrite all_chunks_ainit. reflexivity. Qed.

Lemma commit_bytes_ainit : forall sb pa, commit_bytes (ainit sb pa) = 0.
Proof. intros. reflexivity. Qed.

Lemma AINV_init : forall ATOP sb pa, sb mod 65536 = 0 -> 0 < sb -> pa mod 4096 = 0 -> 0 < pa -> AINV ATOP [] [] (ainit sb pa).
Proof.
  intros ATOP sb pa H1 H2 H3 H4. unfold AINV.
  rewrite all_chunks_ainit, CH_ainit. change (qbatches [] (ainit sb pa)) with (@nil abatch).
  split.
  { intros c Hc. unfold cls_inv. rewrite get_cls_ainit, all_chunks_ainit. change (qbatches [] (ainit sb pa)) with (@nil abatch).
    unfold max_count, ainit. cbn [a_cinit c_allocated_user c_mapped_user c_mapped_free_array c_num_freed c_count aclass0 cntP zlen List.filter length Z.of_nat].
    unfold nbatch. unfold K_FREEARR_OFF, K_USER_MAP, K_FREEARR_MAX, K_FREEARR_MAP. cbn [zlen length Z.of_nat].
    destruct (c =? K_BATCH_CLASS); rewrite Z.mul_0_r; repeat split; cbn; try lia; reflexivity. }
  split; [constructor|]. split; [constructor|].
  unfold ainit. cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array bsum zlen length Z.of_nat].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; reflexivity|].
  split; [intros id ch Hl; rewrite lookup_empty in Hl; discriminate|].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  change (live_budget (ainit sb pa)). unfold live_budget. rewrite live_chunks_ainit. unfold AsanInv.cntP, AsanInv.zlen. cbn [secs secbytes flat_map List.filter length Z.of_nat].
  split; [| split; [unfold SMAX, HB; cbn; lia| unfold LSBYTES, HB; lia]].
  intros c Hc. rewrite Z.mul_0_r. unfold LMAX, HB. destruct (c =? 1); [lia|]. destruct (c =? 2); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | PDisjS a1 n1 a2 n2, PDisjS a1' n1' a2' n2' => zexp_eqb a1 a1' && zexp_eqb n1 n1' && zexp_eqb a2 a2' && zexp_eqb n2 n2'
  | _, _ => false
  end.

Lemma pfact_eqb_eq : forall f g, pfact_eqb f g = true -> f = g.
Proof.
  intros [n lo hi|e lo hi|a1 n1 a2 n2|a1 n1 a2 n2] [n' lo' hi'|e' lo' hi'|a1' n1' a2' n2'|a1' n1' a2' n2'] H; cbn in H; try discriminate.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply zexp_eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply zexp_eqb_eq in H1. apply Z.eqb_eq in H2. apply zexp_eqb_eq in H3. apply Z.eqb_eq in H4. subst. reflexivity.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply zexp_eqb_eq in H1. apply zexp_eqb_eq in H2. apply zexp_eqb_eq in H3. apply zexp_eqb_eq in H4. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pfact_find : forall V f, Forall (pfact_ok V) asan_pure_facts -> existsb (pfact_eqb f) asan_pure_facts = true -> pfact_ok V f.
Proof.
  intros V f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

Definition uns2 (p : word * word) : Z * Z := (bv_unsigned (fst p), bv_unsigned (snd p)).
Lemma reserved_eval : map uns2 (segments_reserved bsegs) = [(65536, 131072); (196608, 528384); (724992, 8192); (733184, 5619712)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition resv_entries (V : nat -> Z) : list (word * word) :=
  flat_map (fun e => match e with LMap b n _ => [(wa (zv V b), wa n)] | LFog _ => [] end) asan_ledger
  ++ segments_reserved bsegs.
Definition iv_of (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (fst e) + bv_unsigned (snd e)).
Definition resv_of (V : nat -> Z) : list (Z * Z) := map iv_of (resv_entries V).
Lemma live_bytes_uns2 : forall l, live_bytes l = fold_right (fun q acc => snd q + acc) 0 (map uns2 l).
Proof. induction l as [|[a n] l IH]; [reflexivity|]. cbn [map fold_right uns2 fst snd]. rewrite <- IH. reflexivity. Qed.
Lemma Forall_uns2 : forall (P : Z * Z -> Prop) l, Forall P (map uns2 l) -> Forall (fun e => P (uns2 e)) l.
Proof. induction l as [|e l IH]; intros H; [constructor|]. cbn [map] in H. apply Forall_cons_iff in H as [H1 H2]. constructor; auto. Qed.
Lemma reserved_facts :
  Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= RES_HI) (segments_reserved bsegs)
  /\ zlen (segments_reserved bsegs) <= LEN0 /\ live_bytes (segments_reserved bsegs) <= RTOT0
  /\ Forall (fun e => 65536 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 6352896) (segments_reserved bsegs).
Proof.
  pose proof reserved_eval as E. split; [|split; [|split]].
  - apply (Forall_uns2 (fun q => fst q + snd q <= RES_HI)). rewrite E. unfold RES_HI. repeat constructor; cbn; lia.
  - unfold AsanInv.zlen. rewrite <- (length_map uns2), E. unfold LEN0. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - rewrite live_bytes_uns2, E. unfold RTOT0. cbn -[Z.le Z.pow]. lia.
  - apply (Forall_uns2 (fun q => 65536 <= fst q /\ fst q + snd q <= 6352896)). rewrite E. repeat constructor; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_of_hull : forall l (g G : Z), 0 <= g -> 0 <= G -> g + G < 2^64 ->
  Forall (fun e => 65536 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 6352896) l ->
  (g + G <= 65536 \/ 6352896 <= g) ->
  region_free l (Z_to_bv 64 g) (Z_to_bv 64 G) = true.
Proof.
  induction l as [|[a sz] l IH]; intros g G Hg HG Hhi HF HD; [reflexivity|].
  apply Forall_cons_iff in HF as [H1 HF]. cbn [fst snd] in H1.
  cbn [region_free]. rewrite (IH g G Hg HG Hhi HF HD), andb_true_r.
  unfold iv_overlap. rewrite !unsigned_lit by lia.
  apply negb_true_iff. apply andb_false_iff.
  destruct HD as [HD|HD]; [right| left]; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
Lemma placement_facts : forall V, Forall (pfact_ok V) asan_pure_facts ->
  4295491576 <= V 208%nat <= 34326181871 /\ 0 <= V 209%nat <= 15 /\ 1551 <= V 226%nat <= 34359734272
  /\ (4096 * V 208%nat) mod 65536 = 4096 * V 209%nat
  /\ (0 <= V 6%nat <= 255 /\ 0 <= V 10%nat <= 7 /\ 4294901760 <= V 0%nat <= 4294967295)
  /\ 4096 * V 208%nat + PRIM_SZ <= 32768 * V 0%nat + 4096 * V 10%nat - 8388608
  /\ 4096 * V 226%nat + PTR_SZ <= 32768 * V 0%nat + 4096 * V 10%nat - 8388608.
Proof.
  intros V HP.
  pose proof (pfact_find V (PVar 208 4295491576 34326181871) HP ltac:(vm_compute; reflexivity)) as H1; cbn in H1.
  pose proof (pfact_find V (PVar 209 0 15) HP ltac:(vm_compute; reflexivity)) as H2; cbn in H2.
  pose proof (pfact_find V (PVar 226 1551 34359734272) HP ltac:(vm_compute; reflexivity)) as H3; cbn in H3.
  pose proof (pfact_find V (PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0) HP
                ltac:(vm_compute; reflexivity)) as H4.
  cbn -[Z.mul Z.add Z.land Z.modulo Z.le] in H4.
  pose proof (pfact_find V (PVar 6 0 255) HP ltac:(vm_compute; reflexivity)) as H6; cbn in H6.
  pose proof (pfact_find V (PVar 10 0 7) HP ltac:(vm_compute; reflexivity)) as H10; cbn in H10.
  pose proof (pfact_find V (PVar 0 4294901760 4294967295) HP ltac:(vm_compute; reflexivity)) as H0; cbn in H0.
  pose proof (pfact_find V (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) HP
                ltac:(vm_compute; reflexivity)) as D1. cbn -[Z.mul Z.add Z.le] in D1.
  pose proof (pfact_find V (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) HP
                ltac:(vm_compute; reflexivity)) as D2. cbn -[Z.mul Z.add Z.le] in D2.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split.
  { change 65535 with (Z.ones 16) in H4. rewrite Z.land_ones in H4 by lia. change (2^16) with 65536 in H4.
    pose proof (Z.mod_pos_bound (4096 * V 208%nat) 65536 ltac:(lia)) as B.
    set (u := (4096 * V 208%nat) mod 65536) in *.
    assert (Hv : (-4096 * V 209%nat + u) mod two64 = 0) by lia.
    apply Z.mod_divide in Hv; [| unfold two64; lia]. destruct Hv as [k Hk]. unfold two64 in Hk. lia. }
  split; [lia|]. unfold PRIM_SZ, PTR_SZ. lia.
Qed.

Lemma ivs_wf_of_bounds : forall l K, K <= 2^64 ->
  Forall (fun iv : word * word => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= K) l -> ivs_wf l.
Proof. intros l K HK H q Hq. rewrite Forall_forall in H. unfold iv_wf, B, BackingAlgebra.S. pose proof (H q Hq). lia. Qed.

(* [comment removed for export] *)
Lemma AMI_init_L : forall lim V sp fs mo, LIMIT34 <= lim ->
  amodelL lim V sp fs mo -> Forall (pfact_ok V) asan_pure_facts ->
  AMI (resv_of V) (atop_of sp) [] (ainit (a_space_beg0 V) (a_ptr_array0 V)) (MX mo []).
Proof.
  intros lim V sp fs mo HLIM HM HP. destruct (placement_facts V HP) as (F208 & F209 & F226 & FR & _ & _ & _).
  destruct HM as [Hh Hfds Hfs Hres Hlim Hbrk Hsbrk Htop Husp Hmaps Hkinds Hsep Hbnd Hlzb Hnawf Hnasub Hnapos Htot Hnl Hab Hbud Halw Hnd Hmat].
  unfold AMI. rewrite m_vm_materialized_MX, m_vmmaps_MX, m_vm_lazy_MX. change (Pm (MX mo [])) with (Pm mo).
  destruct reserved_facts as (R1 & R2 & R3 & R4).
  set (ATOP := atop_of sp). assert (EA : ATOP = bv_unsigned sp - 8388608) by reflexivity. clearbody ATOP.
  assert (W1 : ivs_wf (vm_maps (m_vmmaps mo))).
  { apply (ivs_wf_of_bounds _ ATOP ltac:(lia)). eapply Forall_impl; [|exact Hbnd]. cbv beta. intros iv (_ & _ & _ & _ & _ & H). lia. }
  assert (W2 : ivs_wf (vm_noaccess (m_vmmaps mo))) by (apply (ivs_wf_of_bounds _ (2^64) ltac:(lia)); exact Hnawf).
  assert (W3 : ivs_wf (m_vm_lazy mo)).
  { apply (ivs_wf_of_bounds _ ATOP ltac:(lia)). eapply Forall_impl; [|exact Hlzb]. cbv beta. intros iv [_ H]. lia. }
  assert (END : forall b n, In (b, n) (vm_maps (m_vmmaps mo)) -> bv_unsigned b + bv_unsigned n <= ATOP
                             /\ (bv_unsigned b + bv_unsigned n <= 65536 \/ 6352896 <= bv_unsigned b)).
  { intros b n Hin. rewrite Forall_forall in Hbnd. destruct (Hbnd _ Hin) as (_ & _ & _ & _ & A5 & A6). cbn [fst snd] in A5, A6.
    unfold BothEntry.AIMG_LO, BothEntry.AIMG_HI in A5. lia. }
  split; [reflexivity|].
  split; [rewrite Hlim; exact HLIM|].
  rewrite Hres. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  split. { eapply Forall_impl; [|exact Hbnd]. cbv beta. intros iv (A1 & A2 & A3 & A4 & A5 & A6). unfold entry_ok. repeat split; try assumption. lia. }
  split; [exact W2|]. split; [exact W3|]. split; [apply ivs_sep_seps; exact Hsep|].
  split. { split; [unfold atop_ok, ACEIL, AsanInv.ATOP_MAX; lia|]. unfold alloc_top, stack_max_size. rewrite Htop. lia. }
  split.
  { unfold noacc_clear.
    assert (KO : forall b n, In (LMap (ZLit b) n AsanPlan.AP.KRWLAZY) asan_ledger -> forall iv x, In iv (vm_noaccess (m_vmmaps mo)) ->
                 b <= x < b + n -> 0 <= x < 2^64 -> ~ (bv_unsigned (fst iv) <= x < bv_unsigned (fst iv) + bv_unsigned (snd iv))).
    { intros b n Hin iv x Hiv Hx Hr Hc. rewrite Forall_forall in Hkinds. pose proof (Hkinds _ Hin) as K. cbn [lentry_kind_ok zv] in K.
      assert (U : bv_unsigned (wa x) = x) by (apply wa_unsigned; lia).
      destruct (K (wa x) ltac:(rewrite U; lia)) as [NA _]. apply NA. rewrite U. exists iv. split; assumption. }
    split; apply region_free_of_bytes; try (unfold LS_LO, LS_SZ, HS_LO, HS_SZ; lia); try exact Hnapos.
    - intros iv x Hiv Hx. apply (KO 0x7fff7000 0x10000000); [cbn [In asan_ledger]; tauto | exact Hiv | unfold LS_LO, LS_SZ in Hx; lia | unfold LS_LO, LS_SZ in Hx; lia].
    - intros iv x Hiv Hx. apply (KO 0x2008fff7000 0xdfff0001000); [cbn [In asan_ledger]; tauto | exact Hiv | unfold HS_LO, HS_SZ in Hx; lia | unfold HS_LO, HS_SZ in Hx; lia]. }
  exists (vm_maps (m_vmmaps mo)). split; [rewrite app_nil_r; reflexivity|]. split.
  -
    cbn [ledger_den asan_ledger] in Hmaps.
    pose proof (ledger_den_In V asan_ledger _ Hmaps) as HIN. pose proof (ledger_den_length V asan_ledger _ Hmaps) as HLEN.
    unfold START, ainit. cbn [a_space_beg a_ptr_array].
    assert (INL : forall b n k, In (LMap b n k) asan_ledger -> In (went (zv V b, n)) (vm_maps (m_vmmaps mo))).
    { intros b n k H. exact (HIN b n k H). }
    Ltac inled := cbn [In asan_ledger]; repeat (try (left; reflexivity); right).
    assert (INP : In (went (4096 * V 208%nat, PRIM_SZ)) (vm_maps (m_vmmaps mo))).
    { apply (INL (ZMul (ZLit 4096) (ZV 208)) _ AsanPlan.AP.KRW); inled. }
    assert (INQ : In (went (4096 * V 226%nat, PTR_SZ)) (vm_maps (m_vmmaps mo))).
    { apply (INL (ZMul (ZLit 4096) (ZV 226)) _ AsanPlan.AP.KNONELAZY); inled. }
    pose proof (END _ _ INP) as [EP _]. pose proof (END _ _ INQ) as [EQ HQ]. cbn [fst snd] in EP, EQ, HQ.
    rewrite !unsigned_lit in EP by (unfold PRIM_SZ; lia). rewrite !unsigned_lit in EQ by (unfold PTR_SZ; lia).
    rewrite !unsigned_lit in HQ by (unfold PTR_SZ; lia).
    split.
    { exists (4096 * V 208%nat). split; [exact INP|]. unfold a_space_beg0, PRIM_SZ, KHIGH in *. lia. }
    split; [exact INQ|].
    split; [unfold a_ptr_array0; lia|].
    split. { unfold a_ptr_array0. apply region_free_of_hull; [lia| unfold PTR_SZ; lia| unfold PTR_SZ in *; lia| exact R4| exact HQ]. }
    split; [apply (INL (ZLit LS_LO) _ AsanPlan.AP.KRWLAZY); inled|].
    split; [apply (INL (ZLit GAP_LO) _ AsanPlan.AP.KNONELAZY); inled|].
    split; [apply (INL (ZLit HS_LO) _ AsanPlan.AP.KRWLAZY); inled|].
    split; [unfold AsanInv.zlen, LEN0; cbn [length asan_ledger] in HLEN; lia|].
    split. { rewrite live_bytes_ivs_sum. rewrite ivs_sum_app in Htot. pose proof (ivs_sum_nonneg (vm_reserved (m_vmmaps mo))).
             unfold TOT0. unfold asan_totsz in Htot. lia. }
    unfold resv_of, resv_entries. rewrite map_app. apply Forall_app. split.
    + apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (e & <- & He). apply in_flat_map in He as (le & Hle & He).
      destruct le as [b n k|n]; [|destruct He]. destruct He as [<-|[]].
      exists (wa (zv V b), wa n). split; [apply in_app_iff; right; exact (INL b n k Hle)|]. unfold iv_of. cbn [fst snd]. lia.
    + apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (e & <- & He).
      exists e. split; [apply in_app_iff; left; exact He|]. unfold iv_of. cbn [fst snd]. lia.
  - rewrite commit_bytes_ainit, Z.add_0_r.
    assert (W4 : AsanCeil.init_sp_ok (m_vmmaps mo)) by (unfold AsanCeil.init_sp_ok, sp_window_lo; rewrite Htop; lia).
    rewrite <- (nonlazy_sum_count (MX mo []) eq_refl ltac:(split; [exact W1| split; [exact W2| split; [exact W3| rewrite m_vmmaps_MX; exact W4]]])).
    rewrite (same_but_mat_nonlazy mo (MX mo []) (same_but_mat_MX mo [])). unfold EAGER0. unfold asan_eager in Hnl. lia.
Qed.

Lemma AMI_init : forall V sp fs mo,
  amodel V sp fs mo -> Forall (pfact_ok V) asan_pure_facts ->
  AMI (resv_of V) (atop_of sp) [] (ainit (a_space_beg0 V) (a_ptr_array0 V)) (MX mo []).
Proof.
  intros V sp fs mo HM HP. apply (AMI_init_L target_alloc_limit V sp fs mo); [| apply amodel_amodelL; exact HM| exact HP].
  rewrite <- LIMIT_eq. apply LIMIT34_le_LIMIT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma minv_fds3 : forall mo,
  m_fds mo = init_fds -> m_tid mo = Some (Z_to_bv 64 1) -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps mo)) <= sp_window_hi -> minv mo.
Proof.
  intros mo Hf Ht Hl Hm Hsp. unfold minv. rewrite Hf, Ht, Hl, Hm. unfold init_fds. cbn [fd_lookup].
  repeat split; try reflexivity; try (intros; discriminate); try lia.
  - intros k c H.
    destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. vm_compute. reflexivity. }
    discriminate.
  - intros k p off H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k e H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 2) k); [inversion H; exact I|discriminate].
  - match goal with H : Some _ = Some _ |- _ => injection H as <- end. vm_compute. reflexivity.
  - match goal with H : Some _ = Some _ |- _ => injection H as <- end. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma space_beg0_facts : forall V, Forall (pfact_ok V) asan_pure_facts ->
  a_space_beg0 V mod 65536 = 0 /\ 0 < a_space_beg0 V /\ a_ptr_array0 V mod 4096 = 0 /\ 0 < a_ptr_array0 V.
Proof.
  intros V HP. destruct (placement_facts V HP) as (F208 & F209 & F226 & FR & _). unfold a_space_beg0, a_ptr_array0.
  pose proof (Z.div_mod (4096 * V 208%nat) 65536 ltac:(lia)) as E. rewrite FR in E.
  split; [| split; [lia| split; [rewrite Z.mul_comm; apply Z_mod_mult| lia]]].
  replace (4096 * V 208%nat - 4096 * V 209%nat + 65536) with ((4096 * V 208%nat / 65536 + 1) * 65536) by lia.
  apply Z_mod_mult.
Qed.

Theorem AI_init_L : forall lim V sp fs mo, LIMIT34 <= lim ->
  amodelL lim V sp fs mo -> Forall (pfact_ok V) asan_pure_facts ->
  AsanOK.AI [] (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) (MX mo [])
  /\ aps_so (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) = stdout_init
  /\ m_fds (MX mo []) = init_fds /\ m_fs (MX mo []) = fs /\ m_halted (MX mo []) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanHandoff ()) [] "h01oh17__arithh24__ffh38__varmaph45__with54__p1h64__x1h71Hh81lh94__x2h:4__x3h;1ch<4HAMIh=4HLIMh>2HMh?2HPh@2HchA4HfdshB3HfshC2HhhD5Htop'hE5Husp'hF2S1hG2S2hH2S3hI2S4hJ1VhK6__sat5hL6__sat6hM6__sat7hN6__sat8hO1ahP3acchQ1bhR1fhS2fshT2kchU3limhV1mhW2mohX2sphY1zp%0p%1p&0p&1p;1p;2p;5p;3p;4p;8p;6p;7p;<p;=g00<gj1;Tg00=Lk10DTg00=jk10cTg00J\j2<Tg031gk516Tg018Nk10uTg00B?k30qTg04\Yk20iTg03Pnj1?Tg00HFj1@Tg03R0j1=Tg00b@R0j29Tg00>Mj2cTg00A?j1HTg03KYj1^Tg03Glj1XTg04]_j4kTg033gj2WTg04^^j3jTg04_Qj1iTg00>mj1OTg035Qj1NTg00F;j3>Tg037=j1VTg00DYk105Tg034Zj1[Tg00NPj1xTg04J9k80]Tg01?]j2eTg03n0j5uTg04`Nk60VTg04aJk60UTg02YEj2sTg036Ek101Tg00faj4rTg00A_j3~Tg04bCk61CTg04c;k61ATg0380k10OTg03<Hk10NTg04d4k61<Tg00g^j1{Tg00YYj2RTg04dmk60ITg04ebk10JTg005Zj3mk10hTg01U6k10MTg01Wdk10CTg04f]k10HTg04T7k10PTg04gSk10GTg01\Fj1zTg04hJj1lTg04hhk10FTg0172k20rTg00Gfj15Tg04i\k20ETg028ak40pTg01ROk30oTg04jPk70nTg027ck20mTg003:j61Tg01kYj4aTg00Y<k30lTg00ZCk30kTg04kOk10jTg01<Rj4wTg006Ek10gTg03WCk30fTg03X;k40eTg009Bk40Bk30>Tg00<Pk40dk309Tg00<8k40Ak30;Tg01<nk20@Tg01=Ak50?Tg01=^k30=Tg007:k30<k41?Tg007Sk30:Tg01>5k307Tg01>Lk308Tg008Ok306Tg00;Um<0bTg01>dk10aTg00TTk10`Tg00KVk10_Tg00L4k10^Tg00L_k203Tg00OUk20\Tg00I]j2`Tg00P7k20[Tg00Pck30ZTg00QBk40YTg04lLk10XTg04mHk10WTg00K8j2tTg00MBj2|Tg04nDk60TTg04oCk20RTg050<k20STg01HHk11DTg01d1j1oTg01b7j1dTg023Qj2YTg025:j2}Tg01^Yj2fTg022`k21BTg00U2j4qTg00Mek40QTg00Hdj23Tg01IVk11>Tg01JNk21=Tg0518j1]Tg00Foj17Tg01cTj2GTg021`k219Tg01c7j2pTg029Wj3nTg022=k314Tg01k6k311Tg001ck610Tg02QTk50{Tg01[Mk10|Tg0520k40zTg052lk112Tg053kk113Tg054jk10yTg055fk20xTg056_k217Tg00IAk20wTg01ARm<18Tg00X4k70KTg00lDk60vTg00lhk71:Tg00XXk81;Tg01KHj5yTg00O2j3LTg01Hdk60tTg01I8m=0sTf0R1#;#;p=b%;1#;#;#;p=vg00[?R2f1R3/f1g00]BR43>p=B20w41p=Cf2R51931'9p=Dg057WS00g058RR67>1p=hg0045R7?>31p=U%{1#{p=K%;1#;#;#;#;#;#;#;p=Z1<53/91p=Af5R8f4R9P4P4g01BMf3R:P5g01BmR;P3P4P1P4N<18p>0420321p=FP5g00]`R<g00^?R=P=g00^_R>P2P3g00cGP1H0Qg00_?R?K0Kp=E1<41p=:P3P<P=P=P>P1J0vp>02P5P<P=P=P>P3P1K1:p=\P:P<P=P=P>P5P3P1L1;p=Tf6R@P8P9P:P5P3P1CaCap=_g01FRRAPAP3g01KcRBP1Dyp>00g02?2,31p=J1<31,95p=gP3P<P=P=P>P1P?K0Kp>1@AL231p=SP2PAP:P5P3P1J0tp=4P2P1P3P5P:P9P8P@f7R?g01E[R<f8RCPAf9RDN=0sp=6PAPAP3PBP1Dy#]p>0L1314p=IPAPAP5PBP3Dy#]/31p=813:5,39/33/<1p=21331,35p=P1331,35,3:p=M1331,35,3:,39p=0AL2319L25p>15AL2319L259L2:9L29p=Q%]3/31p>0~1353/<1p>0}g00Z`P2[g00`FRE#;RF#;RG#;RH#;RI#bRJ$0DRK$0cRLg048cRMg040X/<9P8P9P:P5P3I16g01:S&0u8g01;M40q20i@1%?@RN%;JRJ#;#vRO#vRP#@RQ'B%CN%=@RN%@ORO'B%CN'93DP0%??RN/BQ%CN%=?RN/BO%CN3Dg004cRN/c2RR#HRS%?C%=C%^C%X?CkRC%HLRT,W8RU3j%iC#hg049YRC,cLRV#ORW%NUg04VWRX3>%VU/U@&05LRY%[U%xLRU3>3D3DP1%?D/BQf:RZ#?#C%=ZR[/BO%C[3DP0f;R[#?#C%=[R\/BO%C\'9f<R\#?%=\%^\%X[CkR\1WDTRD5jS%i\#h%ND=>WX%VD/UZ%[D=>YU3D3DP1f=RD#?#Cf>RZ#=R\/BO%C\'9P0f?R0#=R\/BO%C\f@R\#?%=\%^\%X0CkR]1WDTR^5jS%i]#h%N^=>WX%V^/UZ%[^=>YU3D3DP1fAR^#=/BOfBR]#=#CfDR_fCR`P]P^P\P0PZPDL0]%^`%X]1c22RZ#HRa%?`%=`'e1W\TDufERbP_P`P]P^P0J0V%[^=>YUfFRcPbP_P`P]P\J0U%N]PLPC1sK4R\&01\CrPLPC%@ER\,sKRd&01dCrPLPC%@FRF,sKRC&01CCr%HV5~V5~V5~V5>WfGRVPcPbP_P`P^J1C%V`/U_fHR^PVPcPbP_P]J1A&0O_$0N=>LcfIR_P^PVPcPbP`J1<%KER`#KRb#{#K#K#K#K#K#;#b#v#Z#Z#Z#@R]1RKVRC%bPRP#bRd#ZRe#;#b#Z#Z#@Rf%@IRI,BC5AC3A%?_RC%=_Rg%^_Rh%X^RiCkRj1WcTRk5jSS01%ij#hS02%NkS03=>WXS04%VkS05/UVS06%[kS07=>YURj'9S08'9S09'9PhPig01CiRl#HRmg01GM#HRn1eCgRoPkJ0IRp&0Jo9mRSRq&0MoRrg059MS0:'<Rs&0CoRtg05:GS0;'<Ru&0HkS0<$0PRv/9jRw'9Rx'9Ry'9Rz'9&0GoR{%zo#lR|g05;?S0='<R}&0Fo20rRS#5R~-0E|'<S0>'9R|'9PpPzPiPmPnPoH0pPhPiB0omnoRzPoPkDuPiPCPgP0P[P?P@K0n%OZRZPafJRa#^%X_P1%?a%=a'e1WVTDuX8ZP8Pz20mCgE1CaPqPy1cNlRy#ORz%HyRZPyPRPNP2B0lNl1B0kNl1$0jCrXTyRVP1Cw9mRSX8z%ORRz&0hRR@&0gR:0fz@PyPRPVPZCwH0ePNPlg01CKRZg01DdR@g01E=RzPlH0BR[PZP@PzPlH0dR0PZP@PzPlH0A-0@[RpI0?PNB0>Z@zB0=Z@zB0<Z@zB0;Z@zB0:Z@zB07Z@zB08Z@zB09Z@zP@B06Z@zPlN<0bE1PyPRPVPNPlP[P0PCPgP2P<g01F4RgPAH0BRCP2P<PgPAH0A+0@R0PpPnPnJ04R[$0aI0?Cw9mRSePqePsPxg00b[Rx#HRq%OxRx&0`2Rl&0_2RN&0^2RV20324Ry%@dRd#F3E20\V>R>P1P5g00cnRzg00dNR@'`20[15=>z@dB0Z243H0YR@b2b3b4%:dP1b11<rdePsePuPwPqPxPlPN%@eRe#F9EVyP>P@b2b3b4%:eP1b11<teePuePvPjPM&0HcRv&0P1XVMPvPW%NcS0?A>W1XX8WS0@P:%Nv&0XcE1&0Wc1cLLRv#O%Hv'`%OL/`TPLP^g04WQRv1RK1RXg04XLRM,<X3AXQLp-0RLPqPx1t23PNPV%F]RX1|2ERE5EVRu%Ff9EVERe202V:5\V5\V%x=R=A\VueCTP>P@b2b3b4X62W5AA1f39A]11<3f9A]3[^62^5LP11RK_R_/BIP_P3O3b11RK^R_1<_M5Ave&0Oc$0NP3E1J0TQ0<20RcTE1PY%[cA>Y1UX0YP9Q0720ScTE1S07CaF_F_P{P|%@bRb,<19A\1&05AR|%xARY&1DARU0001Rv#oR_#:%dvRM%@HRe'Y#J7g_%:M'9X0|1RKaRa/}I%:a%:IfLRa,RK/fI#:[[%=aRa/}O%:a%:OfNRa#=/fO#:[[21B4e1<44RO%:eRM1Y4eR_#:[[%?aRa/}Q%:a%:QfPRa#?/fQ#:[[PqPxP2P2P21t2:P:PlCqP:PlCqP3P2PlP:1t25CqCqPNPVPVAEVyyRQP=PV%FeRu9EVyP=AEVyECTCTP=PV1|2H9EVX202V85\VP=PVP2Pyg00__1|2`H0Q-1@VP=%@PRP#FR=,SE9EVy9\VQ=\VQCTCTCTP>P@b2b3b4X62X92X:2X5L%:5\M\OAA]:9%C:13:P#:,9O/9O[[[^62^92^:2^5LP1fO,RKRK1BKI7AfPK%=aP_P5P?PDO7b1bKbLbMbN%J_#:,9O/9Oe200UYRO#oRD#:%dOR?/Ye#J7gD%:?'9ePCP2P<PgPAH1?RAP3P0C4B0>2<gR?B0=2<gRDB0<2<gRaB0;2<gRKB0:2<gRfB072<gRIB082<gRLB092<gR]B062<gRgP3M:6E1PCPAP3fKR<#?R9%=<R<P0PpPnPnJ04$1>C4-00URp#oRM#:%dpRQ/Ye#J7gM%:Q'9e1e9<01=3R<#oR9#:%d<R</Ye#J7g9%:<'9eW@X;2P{eP}Q0>PqPxPlPN%@JRJ#F9EVyP>P@b2b3b4%:JP1b1%z[#lS0</<JeP}eP|PY%]vRvPCPAg00\cR}#7RJ#7R{#5S0AP0C4S0B-0LUPCPA%7{R{#5S0CP0C4S0DPCPA%7{R{#5S0EP0C4S0FPCPA%7{R{#5S0GP0C4S0HPCPA%7{R{#5S0IP0C4S0JPCPA%7{R{#5S0KP0C4S0LPCPA%7{R{#5S0MP0C4S0NPCPA%7{R{#5S0OP0C4S0PPCPA%7{R{#5S0QP0C4S0RPCPA%7{R{#5S0SP0C4S0TPCPA%7{R{#5S0UP0C4S0VPCPA%7{R{#5S0WP0C4S0XPCPA%7{R{#5S0YP0C4S0ZPCPA%7{R{#5S0[P0C4S0\PCPA%7{R{#5S0]P0C4S0^PCPA%7{R{#5S0_P0C4S0`PCPA%7{R{#5S0aP0C4S0bPCPA%7{R{#5S0cP0C4S0dPCPA%7{R{#5S0eP0C4S0fPCPA%7{R{#5S0gP0C4S0hPCPA%7{R{#5S0iP0C4S0jPCPA%7{R{#5S0kP0C4S0lPCPA%7{R{#5S0mP0C4S0nPCPA%7{R{#5S0oP0C4S0pPCPA%7{R{#5S0qP0C4S0rPCPA%7{R{#5S0sP0C4S0tPCPA%7{R{#5S0uP0C4S0vPCPA%7{R{#5S0wP0C4S0xPCPA%7{R{#5S0yP0C4S0zPCPA%7{#5S0{P0C4S0|-0LU#IS0}58US0~58UR{58UR<58US1058US1158UR958URQ58US1258US1358URM58URE58US1458US1558UR`58UR858US1658US1758URX58URH58US1858US1958URt58URs58US1:58US1;58URd58URr58US1<1Ge4RU1GbPRz%KGRG#@-19FRZ%l;,GF/3\%5}R}'p'G'3R;D2X0|P|PY%]OROPvQ1<PUP;D2X0|P|PYPOPO13vrPUP;D2X0|P|PYPOPOAPOvdPUP;D2X0|P|PYPOPOPOPOPvQ1;CMPUP;D2X0|P|PYPOPOPOPOPOPvQ1:D0PUP;D2X0|P|PYPOPOPOPOPOPO13vsD0PUP;D2X0|P|PYPOPOPOPOPOPOAPOvtD0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPvQ19CMD0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPvQ18D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPO13vHD0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOAPOvXD0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPvQ17CMD0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPvQ16D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPO13v8D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOAPOv`D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPvQ15CMD0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPvQ14D0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPO13vED0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOAPOvMD0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPvQ13CMD0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPvQ12D0D0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPO13vQD0D0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOAPOv9D0D0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPvQ11CMD0D0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPvQ10D0D0D0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPO13v<D0D0D0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOAPOv{D0D0D0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPvQ0~CMD0D0D0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPvQ0}D0D0D0D0D0D0D0PUP;D2X0|P|PYPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPO%IvD0D0D0D0D0D0D0PUP;D2X0|1`2_A>24_P2P41341#JR|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|P|%I|D0D0D0D0D0D0D0PU1GF4/3\R|/p},GZ,3zR}D2XY2PqPxPlPN1Syy/S=RNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPNPN1SNy:15NNDQDQDQDQDQDQDQAn2uy'S%Fb=n2=%FFR=&0DG6142An2=y%F\'S>112y5n2'S5EVP>P@b2b3b41344R@/3PRPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPP%IPD0D0D0D0D0D0D0PU1p|4,GZ,3zD2P1b1%J@R@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@P@%I@D0D0D0D0D0D0D0PUP}D2eP_P1J10b7%dBR_1Y_e'3#JR_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_%I_D0D0D0D0D0D0D0PUP}D2e%]BRBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPBPB%IBD0D0D0D0D0D0D0PUP}D2ePOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPO%IOD0D0D0D0D0D0D0PUP;D2eQ0|P?PDPaPKPfPIPLP]PgQ0{M:6E1Q0zP?PDPaPKPfPIPLP]PgQ0yM:6E1Q0xP?PDPaPKPfPIPLP]PgQ0wM:6E1Q0vP?PDPaPKPfPIPLP]PgQ0uM:6E1Q0tP?PDPaPKPfPIPLP]PgQ0sM:6E1Q0rP?PDPaPKPfPIPLP]PgQ0qM:6E1Q0pP?PDPaPKPfPIPLP]PgQ0oM:6E1Q0nP?PDPaPKPfPIPLP]PgQ0mM:6E1Q0lP?PDPaPKPfPIPLP]PgQ0kM:6E1Q0jP?PDPaPKPfPIPLP]PgQ0iM:6E1Q0hP?PDPaPKPfPIPLP]PgQ0gM:6E1Q0fP?PDPaPKPfPIPLP]PgQ0eM:6E1Q0dP?PDPaPKPfPIPLP]PgQ0cM:6E1Q0bP?PDPaPKPfPIPLP]PgQ0aM:6E1Q0`P?PDPaPKPfPIPLP]PgQ0_M:6E1Q0^P?PDPaPKPfPIPLP]PgQ0]M:6E1Q0\P?PDPaPKPfPIPLP]PgQ0[M:6E1Q0ZP?PDPaPKPfPIPLP]PgQ0YM:6E1Q0XP?PDPaPKPfPIPLP]PgQ0WM:6E1Q0VP?PDPaPKPfPIPLP]PgQ0UM:6E1Q0TP?PDPaPKPfPIPLP]PgQ0SM:6E1Q0RP?PDPaPKPfPIPLP]PgQ0QM:6E1Q0PP?PDPaPKPfPIPLP]PgQ0OM:6E1Q0NP?PDPaPKPfPIPLP]PgQ0MM:6E1Q0LP?PDPaPKPfPIPLP]PgQ0KM:6E1Q0JP?PDPaPKPfPIPLP]PgQ0IM:6E1Q0HP?PDPaPKPfPIPLP]PgQ0GM:6E1Q0FP?PDPaPKPfPIPLP]PgQ0EM:6E1Q0DP?PDPaPKPfPIPLP]PgQ0CM:6E1Q0BP?PDPaPKPfPIPLP]PgQ0AM:6E1PCPA%5JRJP0C4P?PDPaPKPfPIPLP]PgPJM:6E1P2P220~p1XP2X;2P4g05<5I0{&0|[,GeQ0<,GF/3\/p~,GZ,3z40}eQ0>eCaF_PoP6PhPiH0zRi$12&13iPmPn&0yiRiPkJ0I&0Ji9mRS&0MiQ0:&0CiQ0;;Aw3A3D&0Gi%zi#lRwQ0=&0Fi20Ew~'<3A3DeQ01eQ02Q09Q00/`6Q04Q08PWQ0?Q0@P:Q0320xcTE1Q06PjP7%Vc1U1^XR7P5Q05217cTE1Q07F_F_bEbDbBbAbCb<WIWHP3P1O2n2001000000121000000W7WGP3P1O2n2001000000121000000W7WFP3P1O2n2001000000121000000bOW?W>W=WWXS7WXWJXU2o"). Qed.

Theorem AI_init : forall V sp fs mo,
  amodel V sp fs mo -> Forall (pfact_ok V) asan_pure_facts ->
  AsanOK.AI [] (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) (MX mo [])
  /\ aps_so (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) = stdout_init
  /\ m_fds (MX mo []) = init_fds /\ m_fs (MX mo []) = fs /\ m_halted (MX mo []) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanHandoff ()) [] "h02HMh12HPh21Vh32fsh42moh52sph61zp;1p;4p;3p;2p;6p;5p;8g00<gj10Tg00=Lj19Tg00=jj12Tg04H?j41Tg018Nj18Tg00B?j37Tg00J\j23Tg001cj64Tg04I9j55Tg05<nj86Tg00Z`g00[?R0[g00`F#0#0#0#0#0#0#9#2g0045g048cf3R1f2R2f1R3f0R4C1g01:Sf4R5#8g01;M37g04K9R6f5R7P5P1P2P0g04L:g040X/34X60g04M1P6g04N3E4P7P5P1P2P3D5P4G6W1W0W4W3W5W2o"). Qed.

(* [comment removed for export] *)
Corollary AHAND_init : forall rsA V sp inp mo,
  amodel V sp (in_fs inp) mo -> Forall (pfact_ok V) asan_pure_facts ->
  AHAND AAllocAsan nstepA PhiA minvA rsA AAllocAsanOK inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) (MX mo []).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanHandoff ()) [] "h01Hh12H1h22H2h32H3h42H4h52HMh62HPh71Vh82_Hh97__arithh:4__ffh;8__varmaph<5__with=1ah>3inph?2moh@3mo1hA1nhB3rsAhC2spp;1p;4p;3p;6p;2p;5p;7p;9g00<gj16Tg00=Lj1tTg00=jj1ZTg05=mj1CTg04H?j4sTg018Nj1mTg00B?j3^Tg05>aj6YTg00>Mj2DTg00A?j1@Tg033gj20Tg04^^j3BTg04_Qj1?Tg00>mj1GTg00DYj1_Tg00NPj1]Tg00b@R0j21Tg05?^j1WTg05@Rj2UTg05AFj1STg05B>j1RTg05C4j1QTg05Cij4NTg05Dcj5MTg00J\j2:Tg054jj1LTg01\Fj1OTg04hJj1PTg00Hdj2;Tg00TTj1KTg00KVj1TTg00L4j1rTg00L_j2>Tg00g^j1JTg00HFj1ATg029Wj3qTg00O2j3ETg00Mej4HTg00lhj7oTg00OUj2lTg00I]j2kTg00P7j2hTg00F;j37Tg00Pcj3aTg00QBj4bTg01cTj2cTg01kYj4=Tg05EWj6dTg03Pnj1eTg03R0j1fTg03KYj1gTg03Glj1\Tg04]_j4iTg035Qj1jTg037=j1ITg034Zj1[Tg05FSl9nTg05GJl9XTg00X4j7pTf3R1#ef2R2#ff1R3#gf0R4#\Cip=2g057Wg058R774p=9%j4g04VW573p=5g0045R5%I3;74p=`%[3=724p=31134,12p=8%I3%C4575p=4g05H>R5g05I?R6g05J6R7g05JkR8P1g05KaR9P2P3P4M9np=<P5P6P7P8P9P2g05L^R9P3P4M9Xp=VP3g00]`R8g00^?R:P:g00^_R;P4g00_?Fpp=Fg00[?R<g00Z`P<[g00`FR=#6R>#6R?#6#6#6#6R@#t#ZRAg05MYg048cRBP1P2%C3P4Csg01:Sf4RC#mg01;M3^f5RDPC%C1REP2P3P4EYg004c/D<#@RFPDPDPDPCC2RG%@ARH,02RI3B%?G#9g049Y,DA#GRG/5I1`IE%_ARE%]ARA73I3838P0f6RIPIPIPDC2RJ101HR15BF%?J#915G1141CA3E1A'138f8R1PDf7RJPJPJPIC210CHC<P4P1P1P1PJC210DH5BFf9RFPFPFP1C2#?#910IHRI,5G14IJA3EIA'138P0f:RIPIPIPFC2#?#910JHRJ,5G14J1A3EJA38f<RJPFf;RCPCPCPIC2101HC<P4PJPJPJPCC2#?#910IHRI,5G14ICA3EIA38P010CHRC,5G14CJA3ECA'1f@RCf=RIf?R1P1P1f>RKC210JHC<P410IH,5G10KHRK/41A3EKA'1P0101HR1/4CA3E1AfDR1fAR0fCRKPKPKfBRJC210CHC<P4100H/4J10JH=3EA%W5/D<#@RAfFREPEPEfEC2RE10KHRK3V1U5E#9RH15GKRG14K1RJP6P7%S:R0P5PEfGR5%R1#QCNRCPKDMRL'1RM'1RN'1ABAEKg00]BRA/:9RO%LE#O#P/;9g05;?RP':'1RQPIg00b[RI#@%GI%K<%T<%r<RIP8P:P:P;P<1><AR:g00cGR8%J>#J#AR>,><%A=R=,><%A?R?,><RR=q<R5E<5E<RRCH,FIP<AE<:RP8%6@#AR@,><CH,FIFo1lI;P4P2g00cnRIg00dNR;'k1h42=7I;dAa<A3Cbb:b;b<1c??,;=,;>R>,:A1;A>/:@'1P4b91;A9/:P,1OePQeC=PHPNPFPGPMPDPJPLP3P6P7P0PCPKg05NSg016VX@BWAEdC=C=C=C=P5P1PEPKC<eW8W4P3P4O2n2001000000121000000W0W3P3P4O2n2001000000121000000W0W2P3P4O2n2001000000121000000W0W1P3P4O2n2001000000121000000b=W6W5W?W>WCW7WBo"). Qed.

(* [comment removed for export] *)
Corollary equiv_PA_asan : forall rsP rsA V sp enP inp mo,
  valid_entry (mkImage psegs p_init_pc p_phdrs) enP inp -> valid_input_either inp ->
  amodel V sp (in_fs inp) mo -> Forall (pfact_ok V) asan_pure_facts ->
  trace_equiv (tree_traces (prog psegs rsP inp enP) (mo0 psegs source_alloc_limit enP inp))
              (ptraces nstepA nexit (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []))
  /\ (forall tr r mo', ~ tpath nstepA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []) tr r mo').
Proof.
  intros rsP rsA V sp enP inp mo He Hi HM HP. apply (equiv_PA _ _ _ _ rsP rsA AAllocAsanOK enP inp _ _ He Hi). apply AHAND_init; assumption.
Qed.

(* [comment removed for export] *)
Corollary equiv_PA_asan_toP_L : forall LS, 2^31 <= LS -> forall rsP rsA V sp segsX pcX phX enX inp mo,
  valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp ->
  amodel V sp (in_fs inp) mo -> Forall (pfact_ok V) asan_pure_facts ->
  trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs LS (toP enX) inp))
              (ptraces nstepA nexit (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []))
  /\ (forall tr r mo', ~ tpath nstepA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []) tr r mo').
Proof.
  intros LS HLS rsP rsA V sp segsX pcX phX enX inp mo He Hi HM HP.
  apply (equiv_PA_toP_L _ _ _ _ rsP rsA AAllocAsanOK LS HLS segsX pcX phX enX inp _ _ He Hi). apply AHAND_init; assumption.
Qed.

(* [comment removed for export] *)
Corollary equiv_PA_asan_toP : forall rsP rsA V sp segsX pcX phX enX inp mo,
  valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp ->
  amodel V sp (in_fs inp) mo -> Forall (pfact_ok V) asan_pure_facts ->
  trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs source_alloc_limit (toP enX) inp))
              (ptraces nstepA nexit (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []))
  /\ (forall tr r mo', ~ tpath nstepA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []) tr r mo').
Proof.
  intros rsP rsA V sp segsX pcX phX enX inp mo He Hi HM HP.
  apply (equiv_PA_toP _ _ _ _ rsP rsA AAllocAsanOK segsX pcX phX enX inp _ _ He Hi). apply AHAND_init; assumption.
Qed.

(* [comment removed for export] *)
Corollary AHAND_init_L : forall lim rsA V sp inp mo, LIMIT34 <= lim ->
  amodelL lim V sp (in_fs inp) mo -> Forall (pfact_ok V) asan_pure_facts ->
  AHAND AAllocAsan nstepA PhiA minvA rsA AAllocAsanOK inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) (MX mo []).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanHandoff ()) [] "h01Hh12H1h22H2h32H3h42H4h52HLh62HMh72HPh81Vh92_Hh:7__arithh;4__ffh<8__varmaph=5__with>1ah?3inph@3limhA2mohB3mo1hC1nhD3rsAhE2spp;1p;2p;5p;3p;8p;4p;7p;6p;9g00<gj16Tg00=Lj1tTg00=jj1[Tg00J\j27Tg05=mj1ETg031gj5nTg018Nj1_Tg00B?j3ZTg05<nj8XTg00>Mj2CTg00A?j1@Tg033gj20Tg04^^j3ATg04_Qj1>Tg00>mj1HTg00DYj1^Tg00NPj1]Tg00b@R0j21Tg05?^j1WTg05@Rj2UTg05AFj1TTg05B>j1RTg05C4j1NTg05Cij4MTg05Dcj5OTg054jj1LTg01\Fj1PTg04hJj1QTg00Hdj2<Tg00TTj1KTg00KVj1STg00L4j1sTg00L_j2?Tg00g^j1JTg00HFj1BTg029Wj3rTg00O2j3DTg00Mej4ITg00lhj7qTg00OUj2mTg00I]j2lTg00P7j2kTg00F;j38Tg00Pcj3aTg00QBj4bTg01cTj2cTg01kYj4=Tg05EWj6dTg03Pnj1eTg03R0j1fTg03KYj1gTg03Glj1hTg04]_j4iTg035Qj1jTg037=j1GTg034Zj1\Tg05FSl9oTg05GJl9YTg00X4j7pTf3R1#ef2R2#ff1R3#gf0R4#hCip=2g057Wg058R784p=9%j4g04VW583p=5g0045R5%G3;84p=`%\3=824p=41134,12p=:%G3%E4585p=3g05H>R5g05I?R6g05J6R7g05JkR8P1g05KaR9P2P3P4M9op=;P5P6P7P8P9P2g05L^R9P3P4M9Yp=VP3g00]`R8g00^?R:P:g00^_R;P4g00_?Fpp=Fg00[?R<g00Z`P<[g00`FR=#6R>#6R?#6#6#6#6R@#t#[RAg05MYg048cRBg040Xf5RC'7f6RDf4REP1%E2P3Dng01:S%_Cg01;M3Zf8RFPDPC%EERGP1P2P3P4GXg004c/C<#@RHPDPDPDPCC2RI%@ARJ,01R13A%>I#9g049Y,CA#HRI/511`1G%^ARG%]ARA7413:3:P0f7R1P1P1PDC2RK10EJRE5AH%>K#915IE13ECA4GEA'13:f9REPDPFPFPFP1C210CJC;P4PEPEPEPFC210DJ5AHf:RHPHPHPEC2#>#9101JR1,5I131FA4G1A'13:P0f;R1P1P1PHC2#>#910FJRF,5I13FEA4GFA3:f=RFPHf<RHPHPHP1C210EJC;P4PFPFPFPHC2#>#9101JR1,5I131HA4G1A3:P010HJRH,5I13HFA4GHA'1fARHf>R1f@RDPDPDf?RKC210FJC;P4101J,5I10KJRK/3DA4GKA'1P010DJRD/3HA4GDAfERDfBR0fDRKPKPKfCR1C210HJC;P4100J/31101J=4GA%W5/C<#@RAfGRGPGPGfFC2RG10KJRK3V1U5G#9RJ15IKRI13KDR1P6P7%T:R0P5PGfHR5%RD#NCMRHPKDORL'1RM'1RN'1AAAGKg00]BRA/79RO%LG#P#Q/<9g05;?RP'7'1RQPFg00b[RF#@%HF%K<%S<%s<RFP8P:P:P;P<1?<AR:g00cGR8%J>#J#BR>,?<%B=R=,?<%B?R?,?<RR=r<R5D<5D<RRCI,FFP<AD<:RP8%6@#BR@,?<CI,FFFq1mF;P4P2g00cnRFg00dNR;'l1k42=8F;dAa<A3Cbb;b<b=1c??,<=,<>R>,7A1<A>/7@'1P4b:1<A9/7P,1OePQeC=PJPNPEPIPMPCP1PLP3P6P7P0PHPKg05NSg016VXBBWCEdC=C=C=C=P5PDPGPKC;eW9W4P3P4O2n2001000000121000000W0W3P3P4O2n2001000000121000000W0W2P3P4O2n2001000000121000000W0W1P3P4O2n2001000000121000000b>W7W6W5WAW?WEW8XD<W@o"). Qed.

Corollary equiv_PA_asan_toP_LL : forall lim, LIMIT34 <= lim -> forall LS, 2^31 <= LS -> forall rsP rsA V sp segsX pcX phX enX inp mo,
  valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp ->
  amodelL lim V sp (in_fs inp) mo -> Forall (pfact_ok V) asan_pure_facts ->
  trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs LS (toP enX) inp))
              (ptraces nstepA nexit (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []))
  /\ (forall tr r mo', ~ tpath nstepA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []) tr r mo').
Proof.
  intros lim HL LS HLS rsP rsA V sp segsX pcX phX enX inp mo He Hi HM HP.
  apply (equiv_PA_toP_L _ _ _ _ rsP rsA AAllocAsanOK LS HLS segsX pcX phX enX inp _ _ He Hi). apply (AHAND_init_L lim); assumption.
Qed.
