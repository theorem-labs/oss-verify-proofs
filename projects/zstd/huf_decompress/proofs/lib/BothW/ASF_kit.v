(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (26 recorded proofs replaced by written proofs (granules_rup, rup8_facts, filter_is_sec_perm and 23 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes ARep ARepFrame ALayout AHeapP ASecFacts ASec ASecFrame
     AKitQ ARepQ ARepQP ARepKit ARepExt AFreeModel AFreeRep AFrameD FsKit AFake_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASF_kit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI46Stdlib7Sorting;Permutation;Permutation00C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC35stdpp8fin_maps:map_deleteK47Corelib4Init9Datatypes4list02C35stdpp8fin_maps;map_to_listC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC46Stdlib7Sorting;Permutation?Permutation_mapC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC46Stdlib5Lists4List8map_consC35stdpp4gmap;gmap_finmapC35stdpp4base6LookupC35stdpp4base6DeleteC46Stdlib5Lists4List7existsbI46Stdlib5Lists4List5NoDup00I46Stdlib5Lists4List6Exists00I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4base4fmapC35stdpp8fin_maps@lookup_delete_neC35stdpp4gmap:gmap_emptyK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib5BothW4ARep8granulesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl3rupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C46Stdlib5Lists4List6filterK46Stdlib7Sorting;Permutation;Permutation01C59OSSVerify5KrLib5BothW6AHeapP6is_secC1?~~~~~~~~~~~~~~~K46Stdlib7Sorting;Permutation;Permutation02K46Stdlib7Sorting;Permutation;Permutation03C46Stdlib7Sorting;Permutation@Permutation_reflC46Stdlib7Sorting;PermutationAPermutation_transC46Stdlib7Sorting;Permutation?Permutation_indI59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List9in_or_appC46Stdlib5Lists4List2InC35stdpp8fin_mapsBmap_to_list_deleteC35stdpp4base6lookupC35stdpp4base6deleteI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8flat_mapC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeK47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2or01C46Stdlib7Sorting;Permutation>Permutation_inC59OSSVerify5KrLib4Spec8AsanCtrl7achunksC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9filter_Inc59OSSVerify5KrLib5BothW7ASF_kit?live_in_achunksC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ASF_kitBfilter_is_sec_permC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_appC59OSSVerify5KrLib5BothW6AHeapPAfilter_is_sec_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib5BothW:AFreeModel7enq_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7b_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec8AsanCtrl:chunk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_qlocC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5a_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6astate01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>rev_involutiveC46Stdlib7Sorting;PermutationBPermutation_middleC46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib5BothW:AFreeModelCflat_map_app_chunksC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List3revC59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6abatch01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel5qfiltC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:filter_appC59OSSVerify5KrLib4Spec8AsanCtrl7Q_BATCHC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel7enq_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ASF_kitAenq_app_qfilt_secC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ASF_kitAenq_new_qfilt_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel6st_enqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel8st_afterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel>st_after_qfiltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ASF_kit@st_enq_qfilt_secC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=app_comm_consC46Stdlib7Sorting;PermutationDPermutation_app_headC46Stdlib7Sorting;PermutationDPermutation_app_tailC59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec8AsanCtrl:max_cachedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltK59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~C35stdpp8fin_mapsBlookup_delete_SomeC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC35stdpp6option;from_optionC59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6hb_idsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRep<In_lb_removeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2or02C56Stdlib6NArith6BinNat1N3eqbC47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List<NoDup_filterC59OSSVerify5KrLib5BothW8AFreeRep@hb_ids_lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRep?NoDup_lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7sec_wf1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib5BothW5ABase7ab_kindC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8SEC_UOFFC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6abkind00C1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List=Forall_forallC59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4RSECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP6sec_mbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP6sec_msC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9MorphismsDiff_impl_subrelationC59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC59OSSVerify5KrLib5BothW4ASec7asec_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec8sec_liveC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec<sec_disjointC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationAPermutation_NoDupC59OSSVerify5KrLib4Spec8AsanCtrl;needed_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<sec_map_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9sec_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecFacts9sec_factsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes4bool02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib5BothW4ASec5ASECcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec8asec_arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec9asec_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec6aprim0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec4ashzC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ASF_kit;live_sec_inC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<In_nth_errorC46Stdlib5Lists4List>nth_error_SomeC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5BothW4ASecAsec_disjoint_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec:asec_chunkC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib5BothW7ASF_kit>sec_wf1_facts'C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARepBblock_shadow_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib5BothW7ARepKit:junk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:c8_of_junkC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_lengthc59OSSVerify5KrLib5BothW7ASF_kit<granules_rupC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorK59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec?sec_user_shadowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib5BothW4ASec9SEC_MAGICC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9shlen_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AFrameD;junk_frameDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AFrameD<cells_frameDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AFrameD;fill_frameDC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_untouchedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ASF_kit9sec_same0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepExtEmunch_filter_nonemptyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecFrameDsec_untouched_filterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecFrame?nonempty_filterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib5BothW9ASecFrame5D_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<u64arr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame:junk_frameC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InC47Corelib4Init5Logic7iff_symC59OSSVerify5KrLib5BothW9ASecFrame@asec_chunk_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecFrame6D_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecFrame;clear_prim0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecFrame;su_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;azero_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec>astartup_hullsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP6aknownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecFrameAclear_free_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame@disjoint_outsideC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib5BothW7ARepExt8nonemptyC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveC59OSSVerify5KrLib5BothW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8K_REGIONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3KLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_HIGH_MEMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5FsKit5dc_atC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;Forall_implC59OSSVerify5KrLib5BothW;AFake_iface5AFAKEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_iface:afake_geomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_iface;afake_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_iface:fk_nframesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_iface8fk_fsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP>fake_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8ablk_linC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_ifaceDdisjoint_from_ForallC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5FsKitAdisjoint_from_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ASF_kit<dc_at_frameDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_iface=fk_flag_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_iface7fk_flagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_ifaceCmunch_outside_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_iface8fk_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ASF_kit?fake_frameD_lawC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AFrameDCrw_cells_transportDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_iface7FK_NCLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_iface6FAKESZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qcoupledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5q_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ9qentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ9qprim_idsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qentriesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRep>qprim_ids_permC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C46Stdlib7Sorting;PermutationBPermutation_ForallC59OSSVerify5KrLib5BothW8AFreeRepBPermutation_NoDup'C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9NoDup_appC46Stdlib5Lists4List:in_app_iffC46Stdlib5Lists4List:in_map_iffC46Stdlib5Lists4List6in_mapC46Stdlib5Lists4List:Forall_appK59OSSVerify5KrLib5BothW4ARep5xbusy01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7qb_slotC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ5qconc00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List7map_appC59OSSVerify5KrLib5BothW5ARepQ5qb_ksC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ARepQ7qbatchc01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ARepQ5qconc01C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC46Stdlib5Lists4List7combineC59OSSVerify5KrLib5BothW6ARepQP<qentries_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC47Corelib4Init5Logic6or_indK47Corelib5Lists7ListDef6Forall01K46Stdlib5Lists4List5NoDup01c59OSSVerify5KrLib5BothW7ASF_kitAqcoupled_add1_secC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_addC47Corelib7Classes9MorphismsFreflexive_proper_proxyC59OSSVerify5KrLib5BothW8AFreeRep<k24_not_busyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:removelastC59OSSVerify5KrLib5BothW8AFreeRep6xbatchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRep6bbatchC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC59OSSVerify5KrLib5BothW8AFreeRep9In_xbatchC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflK46Stdlib5Lists4List5NoDup02C47Corelib7Classes?RelationClasses=iff_Reflexive".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma granules_rup : forall n, 0 <= n -> granules n = shlen (rup n 8).
Proof.
  intros n N. unfold granules, shlen, rup. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  Z.div_mod_to_equations. nia.
Qed.
Lemma rup8_facts : forall n, 0 <= n -> n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0 /\ shlen (rup n 8) = rup n 8 / 8.
Proof. intros n N. unfold rup, shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. nia. Qed.

Lemma achunk_eq_dec : forall c1 c2 : achunk, {c1 = c2} + {c1 <> c2}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma filter_is_sec_perm : forall (l l' : list achunk), Permutation l l' -> Permutation (List.filter is_sec l) (List.filter is_sec l').
Proof.
  intros l l' HP. induction HP; cbn; [constructor| | |].
  - destruct (is_sec x); [apply perm_skip|]; assumption.
  - destruct (is_sec x), (is_sec y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

(* [comment removed for export] *)
Lemma live_in_achunks : forall st (p : aptr) ch, (a_live st) !! p = Some ch -> In ch (achunks st).
Proof.
  intros st p ch L. unfold achunks. apply in_or_app. left.
  pose proof (map_to_list_delete (a_live st) p ch L) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. eapply Permutation_in; [exact P| left; reflexivity].
Qed.
Lemma live_sec_in : forall st (p : aptr) mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> In (CSec mb ms n) (sec_chunks_of st).
Proof. intros st p mb ms n L. unfold sec_chunks_of. apply List.filter_In. split; [eapply live_in_achunks; exact L| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma sec_chunks_of_delete_sec : forall st st' (p : aptr) mb ms n,
  (a_live st) !! p = Some (CSec mb ms n) ->
  a_live st' = delete p (a_live st) ->
  Permutation (List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st')))
              (List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))) ->
  Permutation (CSec mb ms n :: sec_chunks_of st') (sec_chunks_of st).
Proof.
  intros st st' p mb ms n SOME E1 PQ. unfold sec_chunks_of, achunks. rewrite E1, !filter_is_sec_app.
  change (CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete p (a_live st)))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st')))
    with ((CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete p (a_live st))))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st'))).
  apply Permutation_app; [| exact PQ].
  pose proof (map_to_list_delete (a_live st) p (CSec mb ms n) SOME) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. apply filter_is_sec_perm in P. cbn in P. exact P.
Qed.

(* [comment removed for export] *)
Lemma enq_app_qfilt_sec : forall s1 ch s, is_sec ch = true -> enq_app s1 ch = Some s ->
  Permutation (qfilt is_sec s) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch s Hf E. unfold enq_app in E.
  destruct (rev (a_qloc s1)) as [|b rl] eqn:RV; [discriminate|].
  destruct (b_count b =? Q_BATCH); [discriminate|]. injection E as <-.
  unfold qfilt. cbn [a_qloc a_qglob set_qloc].
  assert (QL : a_qloc s1 = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc s1)), RV; reflexivity).
  rewrite QL. cbn [rev]. rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !app_nil_r.
  rewrite !List.filter_app. cbn [List.filter]. rewrite Hf.
  rewrite <- !app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma enq_new_qfilt_sec : forall s1 ch, is_sec ch = true -> Permutation (qfilt is_sec (enq_new s1 ch)) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch Hf. unfold enq_new, qfilt. cbn [a_qloc a_qglob set_qloc put_cls set_cls].
  rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !List.filter_app. cbn [List.filter]. rewrite Hf.
  rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma st_enq_qfilt_sec : forall s1 ch, is_sec ch = true -> Permutation (qfilt is_sec (st_enq s1 ch)) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch Hf. unfold st_enq. destruct (enq_app s1 ch) as [s|] eqn:E; [exact (enq_app_qfilt_sec s1 ch s Hf E)| exact (enq_new_qfilt_sec s1 ch Hf)].
Qed.
Lemma st_after_enq_qfilt_sec : forall s1 ch, is_sec ch = true -> Permutation (qfilt is_sec (st_after (st_enq s1 ch))) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch Hf. eapply Permutation_trans; [apply st_after_qfilt| apply st_enq_qfilt_sec; exact Hf].
Qed.

(* [comment removed for export] *)
Lemma sec_chunks_of_free_sec : forall st (p : aptr) mb ms n s,
  (a_live st) !! p = Some (CSec mb ms n) ->
  a_live s = delete p (a_live st) ->
  Permutation (qfilt is_sec s) (CSec mb ms n :: qfilt is_sec st) ->
  Permutation (sec_chunks_of s) (sec_chunks_of st).
Proof.
  intros st p mb ms n s SOME EL PQ. unfold sec_chunks_of, achunks. rewrite EL, !filter_is_sec_app.
  pose proof (map_to_list_delete (a_live st) p (CSec mb ms n) SOME) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. apply filter_is_sec_perm in P. cbn in P.
  unfold qfilt in PQ.
  eapply Permutation_trans; [apply Permutation_app_head; exact PQ|].
  eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
  cbn [app]. rewrite app_comm_cons. apply Permutation_app_tail. exact P.
Qed.

(* [comment removed for export] *)
Lemma sec_chunks_of_quar_sec : forall s s' mb ms n,
  a_live s' = a_live s ->
  Permutation (qfilt is_sec s') (CSec mb ms n :: qfilt is_sec s) ->
  Permutation (sec_chunks_of s') (CSec mb ms n :: sec_chunks_of s).
Proof.
  intros s s' mb ms n EL PQ. unfold sec_chunks_of, achunks. rewrite EL, !filter_is_sec_app. unfold qfilt in PQ.
  eapply Permutation_trans; [apply Permutation_app_head; exact PQ|]. apply Permutation_sym. apply Permutation_middle.
Qed.

(* [comment removed for export] *)
Lemma awf_delete_sec : forall L st X (p : aptr) mb ms n s,
  awf L st X -> (a_live st) !! p = Some (CSec mb ms n) ->
  a_space_beg s = a_space_beg st -> a_ptr_array s = a_ptr_array st -> a_cinit s = a_cinit st -> a_cls s = a_cls st ->
  a_live s = delete p (a_live st) -> a_next s = a_next st ->
  awf L s X.
Proof.
  intros L st X p mb ms n s WF LIVE E1 E2 E3 E4 E5 E6.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
  assert (GC : forall c', get_cls s c' = get_cls st c') by (intros c'; unfold get_cls; rewrite E4; reflexivity).
  assert (MC : forall c', max_count s c' = max_count st c') by (intros c'; unfold max_count; rewrite E3; reflexivity).
  assert (ND : forall c', ndist s c' = ndist st c') by (intros c'; unfold ndist; rewrite GC; reflexivity).
  unfold awf. rewrite E1, E2, E5, E6.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split. { intros c Hc. cbv zeta. rewrite GC, MC, ND. exact (PERC c Hc). }
  split. { intros c Hc. rewrite GC. exact (OUTC c Hc). }
  split. { intros b Hb. destruct (BUSY b Hb) as [CL M]. split; [exact CL|]. destruct (xb_st b) as [q| |]; [| exact M| exact M].
           destruct M as (M1 & M2 & M3 & M4 & M5 & M6). repeat (split; [assumption|]).
           rewrite lookup_delete_ne; [exact M6|]. intros ->. rewrite LIVE in M6. discriminate. }
  split. { intros q c n' Hq. apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exact (LIVEB q c n' Hq). }
  split. { intros q ch Hq. apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exact (FRESH q ch Hq). }
  exact UNIQ.
Qed.

(* [comment removed for export] *)
Lemma ablocks_free_sec : forall L st X LB (p : aptr) mb ms n st' X',
  (a_live st) !! p = Some (CSec mb ms n) -> awf L st X ->
  a_live st' = delete p (a_live st) -> (forall y, In y (x_busy X) -> In y (x_busy X')) ->
  ablocks L st X LB -> ablocks L st' X' (lb_remove p LB).
Proof.
  intros L st X LB p mb ms n st' X' LIVE WF EL INCL (BH & BF & NDI & NDL). split; [| split; [| split]].
  - intros p' A n' Hin. apply In_lb_remove in Hin. destruct Hin as [Hin NE]. cbn in NE.
    destruct (BH p' A n' Hin) as [(y & Hy & Sy & R)|(mb' & ms' & Lp & R)].
    + left. exists y. split; [apply INCL; exact Hy|]. split; [exact Sy| exact R].
    + right. exists mb', ms'. split; [| exact R]. rewrite EL, lookup_delete_ne; [exact Lp| congruence].
  - intros cls A n' Hin. apply In_lb_remove in Hin. destruct Hin as [Hin _]. exact (BF cls A n' Hin).
  - rewrite hb_ids_lb_remove. apply List.NoDup_filter. exact NDI.
  - apply NoDup_lb_remove. exact NDL.
Qed.

(* [comment removed for export] *)
Lemma freed_block_sec : forall L st X LB (p : aptr) mb ms n A n',
  awf L st X -> ablocks L st X LB -> In (HB p A n') LB -> (a_live st) !! p = Some (CSec mb ms n) ->
  A = mb + SEC_UOFF /\ n' = n /\ sec_wf1 L (CSec mb ms n).
Proof.
  intros L st X LB p mb ms n A n' WF (BH & _) Hin LIVE.
  destruct (BH p A n' Hin) as [(y & Hy & Sy & Uy & Ny)|(mb' & ms' & Lp & EA & G)].
  - exfalso. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _). destruct (BUSY y Hy) as [_ M]. rewrite Sy in M.
    destruct M as (_ & _ & _ & _ & _ & M6). rewrite LIVE in M6. discriminate.
  - rewrite LIVE in Lp. injection Lp as <- <- <-. split; [exact EA|]. split; [reflexivity| exact G].
Qed.

(* [comment removed for export] *)
Lemma no_busy_live_sec : forall L st X (p : aptr) mb ms n y,
  awf L st X -> (a_live st) !! p = Some (CSec mb ms n) -> In y (x_busy X) -> xb_st y <> BLive p.
Proof.
  intros L st X p mb ms n y WF LIVE Hy E. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY y Hy) as [_ M]. rewrite E in M. destruct M as (_ & _ & _ & _ & _ & M6). rewrite LIVE in M6. discriminate.
Qed.

(* [comment removed for export] *)
Lemma arng_sub : forall L RNG st st',
  (forall c, 1 <= c < K_NUM_CLASSES -> get_cls st' c = get_cls st c) -> a_nres st' = a_nres st ->
  (forall ch, In ch (sec_chunks_of st') -> In ch (sec_chunks_of st)) ->
  arng L RNG st -> arng L RNG st'.
Proof.
  intros L RNG st st' EC EN SUB (A1 & A2 & A3 & A4 & A5 & A6 & A6a & A6b & A6c & A7 & A8 & A9 & A10).
  repeat (split; [assumption|]). split.
  { intros c Hc. rewrite (EC c Hc). exact (A7 c Hc). }
  rewrite EN. split; [exact A8|]. split; [| exact A10].
  unfold RSEC in *. rewrite Forall_forall in A9 |- *. intros x Hx. apply A9. apply SUB. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma sec_not_live_after : forall L st cs (p : aptr) mb ms n s,
  asec_wf L st cs -> Permutation cs (sec_chunks_of st) ->
  (a_live st) !! p = Some (CSec mb ms n) -> a_live s = delete p (a_live st) ->
  ~ sec_live s (CSec mb ms n).
Proof.
  intros L st cs p mb ms n s WFS PC LIVE EL [q Hq]. rewrite EL in Hq.
  apply lookup_delete_Some in Hq. destruct Hq as [NE Hq].
  destruct WFS as (_ & _ & _ & _ & _ & _ & [ND _]).
  (* [comment removed for export] *)
  pose proof (map_to_list_delete (a_live st) p (CSec mb ms n) LIVE) as P1.
  assert (Hq' : delete p (a_live st) !! q = Some (CSec mb ms n)) by (rewrite lookup_delete_ne by exact NE; exact Hq).
  pose proof (map_to_list_delete (delete p (a_live st)) q (CSec mb ms n) Hq') as P2.
  assert (P : Permutation ((p, CSec mb ms n) :: (q, CSec mb ms n) :: map_to_list (delete q (delete p (a_live st)))) (map_to_list (a_live st))).
  { eapply Permutation_trans; [apply perm_skip; exact P2| exact P1]. }
  apply (Permutation_map snd) in P. cbn [map snd] in P. apply filter_is_sec_perm in P. cbn [List.filter is_sec] in P.
  assert (P3 : Permutation (CSec mb ms n :: CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete q (delete p (a_live st)))))
                                 ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))) cs).
  { eapply Permutation_trans; [| apply Permutation_sym; exact PC]. unfold sec_chunks_of, achunks. rewrite filter_is_sec_app.
    change (CSec mb ms n :: CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete q (delete p (a_live st))))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st)))
      with ((CSec mb ms n :: CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete q (delete p (a_live st)))))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))).
    apply Permutation_app_tail. exact P. }
  pose proof (Permutation_NoDup (Permutation_sym P3) ND) as ND2. cbn [app] in ND2.
  inversion ND2 as [|x l NI ND3]; subst. apply NI. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sec_live_other : forall st (p : aptr) mb ms n s ch,
  (a_live st) !! p = Some (CSec mb ms n) -> a_live s = delete p (a_live st) -> ch <> CSec mb ms n ->
  (sec_live s ch <-> sec_live st ch).
Proof.
  intros st p mb ms n s ch LIVE EL NE. unfold sec_live. rewrite EL. split; intros [q Hq].
  - apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exists q. exact Hq.
  - exists q. rewrite lookup_delete_ne; [exact Hq|]. intros ->. apply NE. pose proof (eq_trans (eq_sym Hq) LIVE) as XX. injection XX as <-. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sec_wf1_facts' : forall L mb ms n, sec_wf1 L (CSec mb ms n) ->
     mb mod 4096 = 0 /\ ablk mb (mb + ms) /\ mb + ms <= ATOP /\ ms = sec_map_size n /\ 64512 < n <= AREQMAX
  /\ rz_size n = 2048 /\ 73728 <= ms <= 536891392 /\ ms mod 4096 = 0 /\ needed_size n + 4096 <= ms /\ 0 <= needed_size n
  /\ sec_clear L mb ms /\ is_primary n = false /\ n + 6144 <= needed_size n + 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_kit ()) ["CANSEC1"] "h01Hh14__x1h24__p1h37__arithh44__ffh58__varmaph65__with74__x2h84__x3h91zh:4MSALh;3MSBh<3MSRh=4__p2h>1Lh?3MALh@3MCEhA3MLOhB2MShC3MSEhD2NBhE3NPRhF2NShG3RS1hH2RZhI3SCLhJ1WhK2W0hL2_HhM3_H0hN3_H1hO2mbhP2mshQ1np%0p&0p;3p;1p;2p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p10036R2p4p710R3p8P0P2p4p7210p8p1003Sp4p710R2p10040p4p710R0p8P2g004LR2p4p710R4p8p1004jp4p710R5p1005HR6p4p710R7p8P5P6p4p7210R6p8p1005ap4p70R8g006XR9p4p710p8P8p10072p4p710p8P8p1007Ip4p710p8P8p1007ep4p710p8P8P0p8P8p1008Pp4p710p8P8p1008np4p7210p8P8P1p8P8P4p8P8P3p8P8p1009Kp4p710p8P8g00S4R3p4p710p8P8p100:Gp4p710p8P8p100:dR1p4p710p8P8p100;=R0p4p710p8P8p100;]p4p710p8P8p100<JR:p4p710p8P8p100<aR;p4p710p8P8p100==R<p4p710p8P8p100=Zp4p710p8P8p100>3R=p4p710R>p8P8p100>Gp4p710p8P8p100>[p4p710R?p8P8p100?7p4p710p8P8p100?Sp4p710p8p100@0R8p4p73101R@p100@JRAp4p73110p8P@p100@cRBp4p73110p8P@p100A?p4p710p8P@p100ARRCp4p7201p8P@p100Adp4p7201p8P@P=p4p73110p8P@p100B6R=p4p73110p8P@p100BJRDp4p73110p8P@p100Bdp4p7201p8P8p4p710R@PAp4p710p8P@PBp4p710p8P@P7p8P@P6p8P@P>p8P@P=p4p710p8P@PDp4p710p8p100C7RDp4p710R@P5p8P@P7p8P@P6p8P@p100CKp4p73110p8PDp4p741110RDP;p4p73101p8P<p4p7210P4p8P?P4p8p100C]p4p7<111111111110P4p8P1p4p741110R1P8p4p7511100R4p8P4P1p8p100D?p4p741110R1P8p4p76111100R4p8P4P1p8P0p4p741110R0P8p4p771111100R1p8P1P0p8P:p4p741110R:P8p4p7:1111111100R8p8P8P:p8PCp4p7200RCPDp8PDPCp8g01BHk304Tg02gCk306Tg00F7j15Tg00E<j1:Tg00EZj21Tg0224k10?Tg00DWj19Tg00JTj2DTg03@<j13Tg00L2j22Tg03A:j3XTg03Aoj14Tg03Bnj3NTg03Cik107TP3k10NTg00STk10MTg00T4j2qTg00\gk10LTg00U0k10KTg00UNk10JTg00YKj2aTg00a[j4WTg00V\k10ITg00Ynk20GTg00ZPk20FTg00Zjk20ETP9j36Tg00[Vk30CTg00\5k40BTg03Dgk30@Tg02Ghj17TP2j6eTg00K0R2j20Tg00F\j2}Tg03Eej1zTg03FCk303Tg00Wbj3TTg01Dcj4ZTg00N9k10;Tg00NWk20:Tg00MZj1pTg00PJj2[Tg00O8j3yTg00a2j3^Tg00Q\j2xTg009gj3wTg00V9j2vTg00IMj2PTg03Ffj1_Tg02Hgj1lTg00TRk409Tg00bFj7tTg00bjk702Tg00cNj8sTg00G9j2rTg00I0j2oTg03Gck608Tf0R9#5#5#5#5#5#5#5#5p=Fg00dPR3f1RC/P9g00d2RD36p=C%99#9p=d%59#5p=Yg00k>R:f3R8#_g03HGR036f2R1?NC9'0p=B1D81g02O@R4,2C'0/09p=Mf7R?f6R<f5R;3Xf4R@/28%4C9631/09'0'0p>05%59#5#5#5p=b111C/29p=Q%_C=6:0/09p>0D12D@AN81C/09'0p>0A10C9,01p=j%l<=63;12@8121C'0/09'0p=>12C4,01/09p=~%4C9631/09p>0>1P?<=63DAX;@8121C/09'0'0p=<12@8A631C/09'0p={AN<;@%_8=6:0111C/29'0'0p=@1P;@=63D128112DC/09'0'0p=?%4@963;1D8112C4'0/09'0p=;%49963Cp=k1294p=u1D1C/09p=m%_9=6:0p=n%99#9#9#9p=S128112C9'0p=UP3P1PCP9H09p=R1v39p=LPCg00eUR0g00f4R6P6g00fTR7P9g00g4R5Ftp=`P1P0P6P6P7P3PCg00gTP9CWP5Ftp=EP1P0P6P6P7PCP9K02p>0HP;P0P6P6P7P@P0P6P6P7P8P1K02PCP9Gsp=J12C9,01p>011r1C/o9p=H1P;@=63D128112C9'0'0p=811<;/2@111C,28'0/09p==11;@/r8/o1/1C963</09p=A1P;@=63D111C9638/09'0p=KA63@8101C/09'0p=V%l1=63C/09p=i%lC=639p=hA63C9p=\12@8121C'0/09p>0=11C9,21p=G111C/r9p=g11<;963?1o81/1C963@/09'0p=f12;@/081P1C=63D/09'0p>0<121C/09p=I11C99631p=]12D9p=|PCP0P6P6P7P9J08p=cP8P0P6P6P7P1PCP9Gsp>00P<P;P@P8P1PCP9CZCZp=Og02R7p,2rcR0B041C98068P9B0481C:060@P2g00hbR5#5R=#5R>#5RB#FRA#5RE#:RF,C@RGP0P@11@8RHPH&0?0RHP8P1%95RI#9RJ#9#dRK#Y#F#:RLP1P1P1P;P@P8CBCML05P;PFP0P;11;@RMPMPH1DL8RMP8%:ARA%9>R>#5#b#F#:RNP@P@%YE#9#5#9#b#F#:RE%38RO/1FRP/2@POP<P;P@%5I#Y#F#:RI=Q8P-0D8I0A5jGF>7~8:0>@8G<P91C<FP0P?11?<RGPGPHP<P;PLP;P;P;f8RGP?P<CBCML05P211G?RP9X0GPPPHP?%4<PLP<P<P<f9RPPGP?CBCMD{PPPFP0PP11PGROPOPHPGP?PLP?P?P?PAPNPGPGPEPGPF%3?RO/1FRQPGPOf:ROPPPGP?P?PIPQF@E?F>E;G<P911OP9X0Of;RQ/1OPHPO%4PPLPPPPPPf<RPPQPOCBCMD{P2AQPQHPQPOPLPOPOPOf=ROPPPQCBE;POPFP0PO11OPRGPGPHPPPQPLPQPQPQPAPNPPPPPEPPPF%3QRG/1FRRPPPGf>RGPOPPPQPQPIPRF@E?F>E;G<P9AQGOHPGPOPLPOPOPOf@ROf?RRPGCBE;P21kRGPLPGPGPGfARGPOPRCBCMPGPFP0PG11GORQPQPHPOPRPLPRPRPRPAPNPOPOPEPOPF%3RRQ/1FRPPOPQfBRQPGPOPRPRPIPPF@E?F>E;G<P91kGOPLPGPGPGfDRGfCROPQCBCMP2%uQ9mLQPQfERPPGPOCBPPPFP0PP11PGRRPRPHPGPOPLPOPOPOPAPNPGPGPEPGPF%3ORR/1FRSPGPRfFRRPPPGPOPOPIPSF@E?F>E;G<P9%uG9mLGPPfHRPfGRGPRCBP2%nRfIRR?NPGPRPFP0PR11RPRSPSPHPPPGPLPGPGPGPAPNPPPPPEPPPF%3GRS/1FROPPPSfJRSPRPPPGPGPIPOF@E?F>E;G<P9%nPfLRPfKRO;NS&070RG%dK#SRK#9RR#dRT#5#S#S#5#Y#b#F#F#:PHPH%9T#S#S#5#Y#b#F#F#:CURTg00iGRU$0NRV&0MURW1q31RX&0L3RY7RCS00&0K3RZ&0J3R[P[P3%LLS01g00dnS021a35R\CW,`[R]1a3=R^9E[\R_&0I6R6%:5R`#L=E[\>0H[_EJ20G[7R7P9P1g00k^R_-0F:20E91=6:_dB0C3DCH0BR_b4b5b6X13X731DL9R:@019CP`PCPCP1CU[^13^73P9P4PPP?O3b3b0>0@SC%7SR?%:JR4,1SR`%:BRB;HB12S?12?`P?PB%3SR`P?PF%4SR?P`%:KRKPFPFPFP`PFP?P?P`%:RRRP?PFPNP?P?PEE8F=FAEKDV9iSA9mLSP21DLO%7OR?11O4R`?HBB12O?12?`P?PB%3OR`P?PF%4OR?P`PKPFPFPFP`PFP?P?P`PRP?PFPNP?P?PEE8F=FAEKDV9iOAfNROPFP0POfMR?,1OR`P`PHP?PPPLPPPPPPPAPNP?P?PEP?PF%3PR`/1FRaP?P`fOR`POP?PPPPPIPaF@E?F>E;G<P91DL?%7OR?11O4Ra?HBB12O?12?aP?PB%3ORaP?PF%4OR?PaPKPFPFPFPaPFP?P?PaPRP?PFPNP?P?PEE8F=FAEKDV9iOAP21h`A%7`RO11`4R??HBB12`O12O?POPB%3`R?POPF%4`R`P?PKPFPFPFP?PFP`P`P?PRP`PFPNP`P`PEE8F=FAEKDVfRR`PFP0P`fQR?,1`ROPOPHP?fPROPLPOPOPOPAPNP?P?PEP?PF%3ORa/1FRPP?PafSRaP`P?POPOPIPPF@E?F>E;G<P91h?A%7`R?11`4RP?HBB12`?12?PP?PB%3`RPP?PF%4`R`PPPKPFPFPFPPPFP`P`PPPRP`PFPNP`P`PEE8F=FAEKDVP2%7aR`11a4RP?HBB'\PaP`P`PPP`PB%3aRPP`PF%4aRaPPPKPFPFPFPPPFPaPaPPPRPaPFPNPaPaPEE8F=FAEKI0=fVRaPFP0PafURP,1aR`P`PHPPfTR`PLP`P`P`PAPNPPPPPEPPPF%3`R?/1FRbPPP?fWR?PaPPP`P`PIPbF@E?F>E;G<P9%7P11P4?HBB'\Pa%7aRPAGPa4PPPB%3aRbPPPF%4aRaAgbKFPFPFPbPFPaPaPbPRPaPFPNPaPaPEE8F=GfJ0<P2%7?RaAGa?45I?PaPB%3?RbPaPF%4?R?PbPKPFPFPFPbPFP?P?PbPRP?PFPNP?P?PEE8F=FAEKfZR?PFP0P?fYRb,1?RaPaPHPbfXRaPLPaPaPaPAPNPbPbPEPbPF%3aRP/1FR`PbPPf[RPP?PbPaPaPIP`F@E?F>E;G<P9%7bR`AG`b45Ib%7?R`PB%3?RcP`PF%4?R?PcPKPFPFPFPcPFP?P?PcPRP?PFPNP?P?PEE8F=FAEKP2%7PR?/CB%3PRcP?PF%4PRPAgcKFPFPFPcPFPPPPPcPRPPPFPNPPPPPEE8F=Gff^RPPFP0PPf]Rc,1PR?P?PHPcf\R?PLP?P?P?PAPNPcPcPEPcPF%3?R`/1FRdPcP`f_R`PPPcP?P?PIPdF@E?F>E;G<P9%7c/CB%3PRB%7PPF%4PRcAgBKFPFPFPBPFPcPcPBPRPcPFPNPcPcPEE8F=GfP2%3`Rc%7`;]F%4`RBPcPKPFPFPFPcPFPBPBPcPRPBPFPNPBPBPEE8F=FAfbRBPFP0PBfaRc,1BRdPdPHPcf`RdPLPdPdPdPAPNPcPcPEPcPF%3dR?/1FRePcP?fcR?PBPcPdPdPIPeF@E?F>E;G<P9%3c%7c;]F%4BRe%3BRBPKPFPFPFPBPFPePePBPRPePFPNPePePEE8F=FAP2%4?Re%3?R?/1K?HFF;]FP?PFPePeP?PRPePFPNPePePEE8F=ffRePFP0PefeR?,1eRBPBPHP?fdRBPLPBPBPBPAPNP?P?PEP?PF%3BRf/1FRgP?PffgRfPeP?PBPBPIPgF@E?F>E;G<P9%4?%3?/1K?HFF;]F%3eRKPF%4eRePePKPRPePFPNPePePEE8F=P2%3fRe/1F%4fRfAGfeR3IPfPFPNPfPfPEE8fjRfPFP0PffiRe,1fRKPKPHPefhRKPLPKPKPKPAPNPePePEPePF%3KRg/1FRBPePgfkRgPfPePKPKPIPBF@E?F>E;G<P9%3eRB/1F%4eRKAGKBR3I%4fRfPFPNPfPfPEE8P2%4gRg/CFPNPgPgPECUfnRgPFP0PgfmR2,1gRfPfPHP2flRfPLPfPfPfPAPNP2P2PEP2PF%3fRK/1FRBP2PKfoRKPgP2PfPfPIPBF@E?F>E;G<P9%42/CFPN%4gRgPgPECUP3%4KfpRg#3RB/1FAG9BR7I9X93P;PgPPEe%3KRK/1FAGgKR7IgP3%4g1C9FX93P1fqRgP`Ee1CgFP3%4g12N9Rg129ERK'0X93P1frRPPdEePNPPPPPECUftRd/CFRBfsRf,1dRh9X0dR012hHRh1kfPRH1DLPRi%:=Rj%5J#9Rk#:'}%9=#5R=#:,}j'1Rl,2PRm'0Rn1hPARA12NfRo12fERp'0Rq1CfFRr%3PRs/1FRt/2fRu%|sRsfuRv?NdfS03%nPS04AQPItS05'0Rt'0Rf'0Rw'0Rx'0Ry'0Rz'0R{'0R|'0R}'0R~'0P2P0P~PePhP}P?PHP|PcPnP{PiPmPGPTp-0RmPVPW1q3CRnPZP[P[P]1c[8RcP6P]EJP7P_b4b5b6X13W210:C1DLC[^13^2mP912dlR:PdP`O3b3b0PGPTPVPWPnPZP[P[Pc%LjRj%zk6033%z=:033j5T39E[\RjP6PjEJP7P_b4b5b6X13X2mB01C9l12Cl[^13^2mP91DLdPdP`O3b3b0CZPAPzPOPqPyPoPpPGPTPVPWPnPZP[P[%LN=E[\RpPcP6PpEJP7P_b4b5b6X13X2m10gC12NC[^13^2mP912vEPvP1O3b3b0PGPTPVPWPnPZP[P[Pc%LE9E[\RcP6PcEJP7P_b4b5b6X13X2m10CK12CE[^13^2mP912NvPvP1O3b3b0CZPrPxPCPuPwPGPTPVPWQ00PZP[P[%LFRw9T3\=E[^Ru1c[@P6PuEJP7P_b4b5b6X13X73X2m119F?IC1AQCF1[^13^73^2mP9%3dRu=GvRPvPuP@O4b3b0PsPfPGPT&0;5-0:3R5g00j3Rf#pRs#pRv#p,[35y31[3vRv1[3s1[3f5^3Rf5^35^3g00jRRs'x=wUVPW1q38?R8YRR?R8X9RYCPZP[P3P\g00h;Rx1a3>R>=T3wRrCW,`[P6P[P[1a3JRJ=E[>1c[;R;P6P[P[P3Q01Q02PJCW,`[1c[<P61v3D=E[\EJEJH00P7P_b4b5b6X13X73X83X2mX=m111FRD,\9AI18@10M<%|8[[[^13^73^83^2m^=mP9P:%7dR:?Gd4R4P:PdPuPQPSP`O8b3b0Q03PtPaQ04Q05PbPGPTAy35v=^3f/xs=wUVPWARR8Y9RXCPZP[P3P^PxPrCW,`[P6P[P[AE[\>P;P6%LI9T3\AT3^w5E[EJH00P7P_b4b5b6X13X73X83X2m1\CDAIC8@118F9Q1I[[^13^73^83^2mP9P4P:PuPdPQPSO6b3b0FOFOFOFOFOFOA~iP{9jhH9jB0eb<b:b;W<W:PCP9O2n2001000010121000000W0W;PCP9O2n2001000010121000000W0WBPCP9O2n2001000010121000000W0WFPCP9O2n2011000010121000000W0WNPCP9O2n2011000010121000000W0WGPCP9O2n2011000010121000000W0WMPCP9O2n2011000010121000000W0WHPCP9O2n2011000010121000000W0WLPCP9O2n2011000010121000000b0WIWEPCP9O2n2001000010121000000W0WDPCP9O2n2001000010121000000W0WCPCP9O2n2001000010121000000W0W@PCP9O2n2001000010121000000W0WAPCP9O2n2001000010121000000W0W?PCP9O2n2001000010121000000bKWJXQ3XP3XO3W>o"). Qed.

(* [comment removed for export] *)
Lemma read_chunk_sec : forall cs L st X m (p : aptr) mb ms n,
  ASECc cs L st X m -> Permutation cs (sec_chunks_of st) -> (a_live st) !! p = Some (CSec mb ms n) ->
  let hm := mb + 6128 in
  exists order i b1 ctx uw,
     Permutation order cs /\ nth_error order i = Some (CSec mb ms n) /\ (i < length order)%nat
  /\ Z.of_nat (length order) = a_nsec st
  /\ Forall (sec_wf1 L) order /\ sec_disjoint order
  /\ u64arr bsegs m (al_ptr_array L) (map (fun ch => Z_to_bv 64 (sec_mb ch)) order)
  /\ junk_at m (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))
  /\ (forall j ch, nth_error order j = Some ch -> exists lv : bool, (lv = true <-> sec_live st ch) /\ asec_chunk m ch (Z.of_nat j) lv)
  /\ asec_chunk m (CSec mb ms n) (Z.of_nat i) true
  /\ rw_cells bsegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 (Z.of_nat i))]
  /\ rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
  /\ 0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ 0 <= ctx < 2^31
  /\ rw_cells bsegs m (hm + 16) [C8 uw] /\ junk_at m (hm + 24) (ms - SEC_UOFF - 8)
  /\ fill_at m (shad mb) 768 0xfa
  /\ rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (block_shadow_bytes n)]
  /\ fill_at m (shad (hm + 16) + shlen (rup n 8)) (ms / 8 - 768 - shlen (rup n 8)) 0xfa.
Proof.
  intros cs L st X m p mb ms n (WFS & ARR & INST & PZ & SHZ) PC LIVE hm.
  pose proof WFS as (ALO & WP & WR & WL & WB & WF1 & WD).
  destruct ARR as (order & PO & U64 & JK & PER).
  assert (IN : In (CSec mb ms n) cs) by (eapply Permutation_in; [apply Permutation_sym; exact PC| eapply live_sec_in; exact LIVE]).
  assert (INo : In (CSec mb ms n) order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact IN]).
  destruct (In_nth_error _ _ INo) as [i NTH].
  assert (IL : (i < length order)%nat) by (apply (proj1 (nth_error_Some order i)); rewrite NTH; discriminate).
  assert (WF1o : Forall (sec_wf1 L) order).
  { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PO| exact Hc]. }
  assert (WDo : sec_disjoint order) by (eapply sec_disjoint_perm; [apply Permutation_sym; exact PO| exact WD]).
  destruct (PER i _ NTH) as (lv & LV & CH).
  assert (Elv : lv = true) by (apply (proj2 LV); exists p; exact LIVE). subst lv.
  pose proof (proj1 (Forall_forall _ _) WF1o _ INo) as Wch.
  destruct (sec_wf1_facts' L mb ms n Wch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
  pose proof CH as CH0. cbn [asec_chunk] in CH0.
  destruct CH0 as (H1 & H2 & H3 & H4 & (b1 & cx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in H5, H6, S2, S3. replace (mb + 6144 - 16) with hm in H5 by (subst hm; lia).
  destruct (junk_split m _ 8 (ms - 6144 - 8) ltac:(replace (8 + (ms - 6144 - 8)) with (ms - 6144) by lia; exact H6) ltac:(lia) ltac:(lia)) as [U8 UR].
  destruct (c8_of_junk m _ U8) as [uw HUW].
  exists order, i, b1, cx, uw.
  split; [exact PO|]. split; [exact NTH|]. split; [exact IL|]. split; [rewrite (Permutation_length PO); exact WL|].
  split; [exact WF1o|]. split; [exact WDo|]. split; [exact U64|]. split; [exact JK|]. split; [exact PER|]. split; [exact CH|].
  split; [exact H1|]. split; [exact H5|]. split; [exact B1|]. split; [exact B3|]. split; [exact CX|].
  replace (hm + 16) with (mb + 6144) by (subst hm; lia). replace (hm + 24) with (mb + 6144 + 8) by (subst hm; lia).
  split; [exact HUW|]. split; [unfold SEC_UOFF; exact UR|]. split; [exact S1|].
  rewrite <- (granules_rup n) by lia. unfold sec_user_shadow in S2. split; [exact S2| exact S3].
Qed.

(* [comment removed for export] *)
Lemma asec_chunk_frameD' : forall L W m m' mb ms n idx lv,
  munch W m m' -> sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb + 32 <= A -> 0 < k -> A + k <= mb + ms -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> 0 < k -> A + k <= shad mb + ms / 8 -> disjoint_from W A k) ->
  rw_cells bsegs m' mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 idx)] ->
  (exists idx0, asec_chunk m (CSec mb ms n) idx0 lv) -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros L W m m' mb ms n idx lv MU WF1 DC DS HDR [idx0 CH].
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & _). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  destruct GR as (GR1 & GR2 & GR3).
  cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in *.
  split; [exact HDR|].
  split; [eapply junk_frameD; [exact H2| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frameD; [exact H3| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frameD; [exact H4| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frameD; [exact H5| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frameD; [exact H6| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frameD; [exact S1| exact MU| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frameD; [exact S2| exact MU| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frameD; [exact S3| exact MU| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_same0 (st st' : astate) : Prop :=
     a_nsec st' = a_nsec st /\ a_nres st' = a_nres st /\ a_ptr_array st' = a_ptr_array st
  /\ (forall ch, is_sec ch = true -> (sec_live st' ch <-> sec_live st ch)).

Lemma asecc_frame : forall cs L W m m' st st' X X',
  ASECc cs L st X m -> munch W m m' -> wmono bsegs m m' -> sec_untouched L W -> sec_same0 st st' ->
  ASECc cs L st' X' m'.
Proof.
  intros cs L W0 m m' st st' X X' (WFS & ARR & INST & PZ & SHZ) MU0 WM SU0 (EN & ER & EP & EL).
  pose proof WFS as (ALO & WP & WR & WL & WB & WF1 & WD).
  pose proof (munch_filter_nonempty W0 m m' MU0) as MU. pose proof (sec_untouched_filter L W0 SU0) as SU. pose proof (nonempty_filter W0) as NE.
  set (W := List.filter nonempty W0) in MU, SU, NE.
  assert (ALLSEC : forall ch, In ch cs -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n)).
  { intros ch Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1. destruct ch as [c n|mb ms n]; [destruct W1|].
    exists mb, ms, n. split; [reflexivity| exact W1]. }
  split; [| split; [| split; [| split]]].
  - unfold asec_wf. rewrite EP, ER, EN. exact WFS.
  - destruct ARR as (order & PO & U64 & JK & PER). exists order.
    assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
    split; [exact PO|]. split; [| split].
    + destruct order as [|o0 order'].
      * destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
      * eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. apply (D_ptr L W0 SU0 ALO); cbn [length] in LEN |- *; clear -LEN WB WR; lia.
    + rewrite EN, ER. eapply junk_frame; [exact JK| exact MU| exact WM|]. intros POS. apply (D_ptr L W0 SU0 ALO); clear -POS WB WR; lia.
    + intros i ch Hi. destruct (PER i ch Hi) as (lv & LV & CH).
      assert (Hin : In ch cs) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
      destruct (ALLSEC ch Hin) as (mb & ms & n & -> & W1).
      exists lv. split; [| eapply (asec_chunk_frame L W0 m m' MU0 WM SU0 ALO); [exact W1| exact CH]].
      rewrite LV. apply iff_sym. apply EL. reflexivity.
  - destruct INST as (I1 & [srt I2] & I3 & I4 & I5 & I6). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [exists srt; eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I3| exact MU| exact WM| intros _; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I4| exact MU| exact WM| intros _; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [eapply cells_frame; [exact I5| exact MU| exact WM| cbn; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    eapply junk_frame; [exact I6| exact MU| exact WM| intros _; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia].
  - unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM|]. intros POS.
    apply (su_disjoint L); [exact SU| exact NE| exact POS|]. intros a Ha. apply (clear_prim0 L ALO). exact Ha.
  - intros x Hx HF HC.
    assert (SX : 0 <= shad x < 2^64) by (pose proof atop_range as ATR; rewrite shad_div; unfold ASHOFF, K_HIGH_MEM, AIMG_HI, KLS in *; clear -Hx ATR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia].
    apply (su_disjoint L); [exact SU| exact NE| clear; lia|]. intros a Ha K. apply (clear_free_shadow L ALO x Hx HF). replace (shad x) with a by (clear -Ha; lia). exact K.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition depot_frameD_law (AD : alayout -> amem -> Prop) : Prop :=
  forall L m m' W, AD L m -> munch W m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv ->
              ~ (0x18c1c8 <= a < 0x5dc210) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
    AD L m'.
(* [comment removed for export] *)
Definition fake_frameD_law (AFK : alayout -> list ablock -> amem -> Prop) : Prop :=
  forall L LB m m' W, AFK L LB m -> munch W m m' -> fake_untouched L W ->
    Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AFK L LB m'.

Lemma dc_at_frameD : forall W m m' A n, dc_at m A n -> munch W m m' -> (0 < n -> disjoint_from W A n) -> dc_at m' A n.
Proof. intros W m m' A n H MU D. exact (junk_frameD W m m' A n H MU D). Qed.

Lemma afake_frameD : fake_frameD_law AFAKE.
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_kit ()) ["CANSEC1"] "p'0h01Hh13posh22ivh31ch44__x1h51Fh61bh71nh87__arithh92hsh:4__ffh;8__varmaph<5__with=2h2h>2h1h?1ah@2X1hA2X2hB2X3hC2X4hD2X5hE2X6hF2X7hG2X8hH2X9hI2h0hJ4__x2hK2H0hL4__x3hM2HbhN2_HhO2HahP2HchQ2HphR4__p1hS1ohT2C1hU2C2hV2C3hW2C4hX2C5hY2C6hZ2C7h[2C8h\2CEh]2D1h^2D2h_2D3h`2D4ha2D5hb2D6hc3DC1hd3DC2he2DDhf2DFhg2DShh2DThi2FLhj1Ghk2G1hl3G10hm3G11hn2G2ho2G3hp2G4hq2G5hr2G6hs2G7ht2G8hu2G9hv3GL1hw3GL2hx3GL3hy3GL4hz2H1h{3H10h|3H11h}2H2h~2H3i002H4i012H5i022H6i032H7i042H8i052H9i062HFi072HSi083Hini093Hivi0:2Hni0;1Li0<2LBi0=3LOGi0>2LVi0?2MUi0@3NGCi0A2NZi0B2UTi0C3UT2i0D1Wi0E7__sat12i0F7__sat13i0G7__sat14i0H7__sat15i0I1mi0J2m'i0K1xp%0p%1p%2p%3p&0p&1p;1p;4p;2p;3p;6p;9p;8p;5p;:p;7p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0g002UR1p4p710R2p8P0g0134R3p4p710R4p8P0P3p4p7210p8p1003Sp4p710R0g0040R5p4p710R6p8P0g004LR0p4p710R7p8p1004jp4p710R8p1005HR9p4p710R:p8P8P9p4p7210R9p8p1005ap4p70R;g006XR<p4p710p8P;g013oR=p4p710p8P;p1007Ip4p710p8P;p1007ep4p710p8P;P6p8P;p1008Pp4p710p8P;p1008np4p7210p8P;P2p8P;P7p8P;P4p8P;p1009Kp4p710p8P;g00STR4p4p710p8P;p100:Gp4p710p8P;p100:dR2p4p710p8P;p100;=R6p4p710p8P;p100;]p4p710p8P;p100<JR>p4p710p8P;p100<aR?p4p710p8P;p100==R@p4p710p8P;p100=Zp4p710p8P;p100>3RAp4p710RBp8P;p100>Gp4p710p8P;p100>[p4p710RCp8P;p100?7p4p710p8P;g04]\R;p4p710p8p100@0RDp4p73101REp100@JRFp4p73110p8PEp100@cRGp4p73110p8PEp100A?p4p710p8PEp100ARRHp4p7201p8PEp100Adp4p7201p8PEPAp4p73110p8PEp100B6RAp4p73110p8PEp100BJRIp4p73110p8PEp100Bdp4p7201p8PDp4p710REPFp4p710p8PEPGp4p710p8PEP:p8PEP9p8PEPBp8PEPAp4p710p8PEPIp4p710p8p100C7RIp4p710REP8p8PEP:p8PEP9p8PEp100CKp4p73110p8PIp4p741110RIP?p4p73101p8P@p4p7210P7p8PCP7p8p100C]p4p7<111111111110P7p8P2p4p741110R2PDp4p7511100R7p8P7P2p8p100D?p4p741110R2PDp4p76111100R7p8P7P2p8P6p4p741110R6PDp4p771111100R2p8P2P6p8P>p4p741110R>PDp4p7:1111111100RDp8PDP>p8PHp4p7200RHPIp8PIPHp8P4k10NTg00F7j18Tg03Eek10iTg03Hgk10~Tg015Rk11OTg04^<j4@k11ETg04_8k20ITg04`9j2^Tg02^0j13Tg03UAj1`Tg00MZj1>Tg03`Ck20{Tg00S4k10wTg02@OS00j29Tg00DWj1BTg00E<j1[Tg03N2k20<Tg03^7k10nTg00`Uk20lTg00_\k10kTg04a;k102Tg016mk20CTP<j36Tg00HWk10eTg02]7k10cTg04b<j1sTg02\>k311Tg00K0R<j24Tg03gij3\Tg04c;j2]Tg017Ok21MTg02ngj1;TP1j3YTg03A:k30HTg0224k11?Tg00L2j2:Tg039:j17Tg00EZj21Tg04d;k41=Tg00F\k20jTg034jj1ETP;j6gTg04e4j4fTg03h]j3ZTg03Cik11;Tg04JEk21:Tg04Jmk319Tg04f?k318k216Tg00IMj2pTg00H6k20dTg00G9k20BTg00I0k20bTg00Imk20aTg00JTj2OTg00KKk215Tg00LNk214Tg00M4k213Tg04g0k210Tg00T4k20`Tg00TRk40RTg00U0k11ZTg00UNk11YTg00YKk20QTg00V\k11XTg00Ynk21WTg00ZPk21VTg00Zjk21STg00[Vk31RTg00\5k41QTg04\fj3bTg03V6k11PTg02FNk10KTg00\gk11NTg00V9k20vTg04glm90?Tg04hnk80^Tg01Dck40[Tg02aYk40@Tg00XEk31LTg04imk50uTg04k1j3~Tg04L5k10JTg00PJk200Tg00a2k309Tg00Q\k20tTg009gj3zTg03Gck61JTg03FCk31ITg04kom:0sTP5k61HTg04m9k307TP0k61FTg04n8k11DTg03a8j4wTP=k30mTP3k31CTg0036k31KTg02h<j2dTg04o:k20\Tg04ook212Tg00Wbk30zTg00a[k40]Tg00bFk70_Tg04KQk71BTg00cNk81ATg03lRk11TTg050dm91@Tg00bjk71UTf0R3#8#8p>0=%>3#>p>17%>3#>#>#>#>#>#>#>p>0}%>3#>#>#>#>#>#>#>#>#>#>#>#>#>#>#>p>0Og03dER=f1R0;z3p=k%`0=z=3p=_g03e:R5f2R;P0P3Cwp=H%83#[p>0Y20<;0#`=z=3p=c%83#8#8#[p=Xg00d2R1/:3p=Gg051jR4,O3,40p>0X1O03,4;p>0:A~;03$0Jp=5g02iNRHf5RIf4R>f3RD<07;<110<0m3p=IB0mH03p=Jg00dPR6%s3760p>0Pf7R2f6R7B07I>D566A6;03'4'4p=K1963,40,4;p=F117I=b2>%E;=bD0/43'4p=RP5P>11D;P0Cw/43p=C1403,4;p=LB1C663p=<B1K663p==11>D,:I11;0/:3'dp=TP5PD11;0P3Cwp=yP5P;%30P3Cwp=xP5PDP;Az=03Cwp=rAz=039z=;p>0L11;0=bD3p>0Z%ED=b>;1403'4p>0p%E0=b;3p>0o1p03=661p=hg052hRC,13p=D20\I>212D;1:03'4'4p=j212D;1:03'4p=S1:271:I>'d1:D;1:03'd'4p=?1:7I1:>D1:;0'd/43'4p=Q1:I>20\D;/40/43'4p=i1:;0/43p=W20\D;/40/43p>0G11;0/:3p=N1:>D1:;0'd/43p=21:D;1:03'dp=01:>D11;0/:3'dp=A1:7I/d>1:D;1:03'd'4p>1>%83#B#8#8p=|%B3#8p=a%83#8#8#8#8#8#8#8p>05%B3#Bp>041:10/43p=v%83#Bp>0F%B3#8#8#Bp>0;%B3#B#8#Bp>0h%B3#B#8#8p>0W%B3#B#B#Bp=U%83#B#B#8p=q%83#B#8#Bp>0g1:D;/d0/43p>1<%;0/13p>0V1:03,d;p>0f%83#8#8#8p>0U1:03,4;p>0D1O13p>01A6631p>0TA6603p>0A20v63p=VB0z603p={P;g00eUS01g00f4S02Q02g00fTS03P6P0g00gTR@P3H0]g00g4R?K0_p=PPDQ01Q02Q02Q03P6B0z6;0P@P3H0]P?K0_p=uP;Q01Q02Q02Q03P0P3K1Bp>0|PDQ01Q02Q02Q03P;P0P3L1Ap>03B07;03966Dp>0MA6;03,4D,4>p>0y20<03#`p>06P5P7PIP>CwP5PDP;P0Cw/43'4p=M%;;/10=bD3p=oP5P7PIP>Cw11;0=bD3'4p>0x&1T3$0K9Z;0p=mP5P2P7PIP>PDP;P0P3N91@p=nP7PIP>PDP;P0P3H0[H0[p=tP6P0g00dnP3H0]p>0SP0Q01Q02Q02Q03P3P?K0_p>0EP;Q01Q02Q02Q03P0P3K1Up>0>&02I,O7,42B07D;0966>/43'4p=e1963p=lA66;0/43p>0r1O34p=}14>DA66;0/43'4p>08&023,O0p>1GB07I>D9667A6;03'4p>0qg02R7&0NHg00hbRH#8S04#8S05#8R4#8R?$0=R5$0iR@$0~RE&0i4R9$0~R:$1OR8[S06Q06g040j$0Np,2rcRAP>PDP;C@P<20IAI1^ID&0N:RBf9RG#3RF%`DRJ%`;RKg00j3S07#>S08#>S09#>S0:#>S0;#>S0<#>$17S0=$0}$0O$0O$0OS0>00{3&0w=R='kS0?,_0S0@'kS0A'kS0B5H2X9B'9X=E,9EX>E,9EXIE,9EPD%3IRLQ04#BRM#BRN#8$0=RO#[RP%8M$0Y=c@=S0CPDPL%BHS0D#8$0=S0E#8RM$0YRQ20<91RR$0n/k=S0FPDPL%85$0=#XRS20lCSRTPDPL&0kCRC%G;RL00X;RU&02D:0:L;RLf8RVf:RW?5>DO120C:;RX568A6:DR$0eRR&0c7RYf<RZP7PI%s7R[f;R\EI[[[[^6:^16^36&0c;@1103R]/J2%GDS0G00XDR^20P0DR_%G3S0H&02>80:3R`PDPWP>P3P8PVA5W>3O1%[HS0I-0<9S0J-0C:R9GKX163F[^76^56^36'4GRDCDC3LA\;>D1]2D21M66Ra%<3Rb%;GRc%[MRMPc%[5R5%=3RcETX2a;Y>PAPGPVP7C@[[[P320IA21^V7%3ZRdQ0B5HWX9B,9BX=E,9EX>E,9EXIE,9EP7%3VRePPQ0CP7PePQQ0FP7PePSPTP7PePCP\f=Re?5>DO1=68XPYf?RfP7PIP[f>RgEI\R[\L\U^6:^16^361J]WP`PDPeP>P3P8P\A5e>3O1P9GKX169F^_[^76^56^36'4GRDCDC3LP<1^G2%3eRhQ0B5H\X9B,9BX=E,9EX>E,9EXIE,9EP2PFPPQ0CCyP2PFPQQ0FP2PFPSPTP2PFPCPZA5g>DO1=68XPYf@S0KP7PIP[PfEI\R[\L\U^6:^16^361J]\P`PDPgP>P3P8PZA5g>3O1P9GKX169F^_[^76^56^36'4GRDC3LA\7V21]\2Pb%;eRFPMPFP5PcETX2a=YaVPAPePZPWC@[[[P31^\GQ0KQ0B5xgX9B,9BX=E,9EX>E,9EXIE,9EPWPdPPQ0CCyPWPdPQQ0FPWPdPSPTPWPdPCPffARd?5>DO1=68XPYfCRFP7PIP[fBRiEI\R[\L\U^6:^16^361J]gP`PDPdP>P3P8PfA5d>3O1P9GKX169F^_[^76^56^36'4GRDC3LP<%3dRjQ0B5HfX9B,9BX=E,9EX>E,9EXIE,9EP\PhPPQ0CP\PhPQQ0FP\PhPSPTP\PhPCQ0KA5i>DO1=68XPYfDS0LP7PIP[PFEI\R[\L\U^6:^16^361J]fP`PDPiP>P3P8Q0KA5i>3O1P9GKX169F^_[^76^56^36'4GRDCDCA\WZ\1]f\Pb%;dRhPMPhP5PcETX2a=YaZPAPdQ0KPgC@[[[P3Q0B9xdFX9B,9BX=E,9EX>E,9EXIE,9EQ00PEQ0LQ0B5xiX9B,9BX=E,9EX>E,9EXIEPfPjPPQ0CPfPjPQQ0FPfPjPSPTPfPjPCQ0LfFS0M?5>DO1=68XPYfHRjP7PIP[fGRhEI\R[\L\U^6:^16^361J]FP`PDQ0MP>P3P8Q0LQ0M?5>3O1P9GKX169F^_[^76^56^36'4GRDCDCQ0K=\gf1]FfPbfERk#;RlPMPlP5PcETX2aQ0K5YaPAPkQ0LPiC@[[[[P3Q0LQ0MQ0B3xX9B,9BX=E,9EX>E,9EQ00PE%`>RlQ0A'k9xkhX9B,9BX=E,9EX>EPF%3kRmPPQ0CPFPmPQQ0FPFPmPSPTPFPmPCPjfJRm?5>DO1=68XPYfLS0NP7PIP[fKS0OEI\R[\L\U^6:^16^361J]hP`PDPmP>P3P8PjA5m>3O1P9GKX169F^_[^76^56^36'4GRDCDCQ0L=\iF1]hFPbfIS0P#;RnPMPnP5PcETX2aQ0L5YaPAQ0PPjQ0MC@[[[[P3PhQ0P#3Rn%`7RoQ0ACrX9B,9BX=E,9EQ00PEQ0@,kJ,_29xjmX9B,9BX=EPhPnPPQ0CPhPnPQQ0FPhPnPSPTPhPnPCQ0NfNS0Q?5>DO1=68XPYfPS0RP7PIP[fORnEI\R[\L\U^6:^16^36Q0O,J]P`PDQ0QP>P3P8Q0NQ0Q?5>3O1P9GKX169F^_[^76^56^36'4GRDCDCQ0M?\jhQ0O/]hPbfMS0S#;RJPMPJP5PcETX2a=YajPAQ0SQ0NPmC@[[[[P3Q0NQ0@,_I,_G5xmX9B,9BQ00PBQ0OQ0S#3RJ%`WQ0?:0LoKCrX9BQ0OPJPPQ0CQ0OPJPQQ0FQ0OPJPSPTQ0OPJPCQ0RfRS0T?5>DO1=68XPYfTRJP7PIP[fSS0UEI\R[\L\U^6:^16^361J]nP`PDQ0TP>P3P8Q0RQ0T?5>3O1P9GKX169F^_[^76^56^36'4GRDCDCQ0NQ0O5\mQ0O,]nPbfQS0V#;RoPMPoP5PcETX2aQ0N5YaPAQ0VQ0RQ0QC@[[[[P3Q0SQ0?,kl,_V,_Z7xnQ0QQ0R#3RlPPQ0CQ0QPlPQQ0FQ0QPlPSPTQ0QPlPCQ0UfURl?5>DO1=68XPYfWS0WP7PIP[fVRoEI\R[\L\U^6:^16^36Q0T,J]P`PDPlP>P3P8Q0UA5l>3O1P9GKX169F^_[^76^56^36'4GRDCDCP<PnQ0V#3RKPPQ0CCyPnPKPQQ0FPnPKPSPTPnPKPCPJA5o>DO1=68XPYfXRKP7PIP[Q0WEI\R[\L\U^6:^16^36Q0U,J]P`PDPoP>P3P8PJA5o>3O1P9GKX169F^_[^76^56^36'4GRDCQ0QQ0R;\nQ0U/]nPb%;lRpPMPpP5PcETX2aQ0R5YaPAPlPJQ0TC@[[[P3Q0VQ0U#3PPQ0CCyQ0T%3JRpPQQ0FQ0TPpPSPTQ0TPpPCQ0WfYRp?5>DO1=68XPYf[S0XP7PIP[fZRqEI\R[\L\U^6:^16^361J]oP`PDPpP>P3P8Q0WA5p>3O1P9GKX169F^_[^76^56^36'4GRDCP<Q0U%3lRrPQQ0FCyQ0UPrPSPTQ0UPrPCPKA5q>DO1=68XPYf\RrP7PIP[Q0XEI\R[\L\U^6:^16^36Q0W,J]P`PDPqP>P3P8PKA5q>3O1P9GKX169F^_[^76^56^36'4GRQ0TQ0U7\JQ0WQ0U']Pb%;pRsPMPsP5PcETX2a=YaJPAPpPKPoC@[[[P3PlQ0W#3PQQ0FCyPo%3KRlPSPTPoPlPCQ0Xf]Rl?5>DO1=68XPYf_RJP7PIP[f^RsEI\R[\L\U^6:^16^361J]qP`PDPlP>P3P8Q0XA5l>3O1P9GKX169F^_[^76^56^36'4GRP<Q0W%3pRtPSPTH0ZQ0WPtPCPrA5s>DO1=68XPYf`RtP7PIP[PJEI\R[\L\U^6:^16^36Q0X,J]P`PDPsP>P3P8PrA5s>3O1P9GKX169F^_[^76^56^36I0pQ0W9\oKQ0XQ0W']Pb%;lRoPMPoP5PcETX2a=YaKPAPlPrPqC@[[[P3PpQ0X#3PSPTH0ZPq%3rPCPJfaRp?5>DO1=68XPYfcRKP7PIP[fbRoEI\R[\L\U^6:^16^361J]sP`PDPpP>P3P8PJA5p>3O1P9GKX169F^_[^76^56^36I0pP<Q0X%3l<0oCPtA5o>DO1=68XPYfdRuP7PIP[PKEI\R[\L\U^6:^16^361J]JP`PDPoP>P3P8PtA5o>3O1P9GKX169F^_[^76^56^36'4Q0X9\qrQ0X,]JPb%;pRqPMPqP5PcETX2a=YarPAPpPtPsC@[[[P3%3J>0olCPKfeRl?5>DO1=68XPYfgS0YP7PIP[ffRrEI\R[\L\U^6:^16^361J]oP`PDPlP>P3P8PKA5l>3O1P9GKX169F^_[^76^56^36'4P<PuA5r>DO1=68XPYfhS0ZP7PIP[Q0YEI\R[\L\U^6:^16^361J]KP`PDPrP>P3P8PuA5r>3O1P9GKX169F^_[^76^56^36A\stJ1]KJPb%;lRJPMPJP5PcETX2a=YatPAPlPuPoC@[[[P3PrQ0Z?5>DO1=68XPYfjS0[P7PIP[fiS0\EI\R[\L\U^6:^16^361J]rP`PDQ0\P>P3P8Q0YQ0\?5>3O1P9GKX169F^_[^76^56^36A\pKo1]roPbQ0Z#;RrPMPrP5PcETX2a=YaKPtQ0Z-0IAP<Q0\#3Rt/hS%DtRK:0HAt&1?ARr,:KQ0\#7Ro/hSPoPSPoPSPSPoEj11oSRpPrQ0\#;RuPSPuPSPSPuCS11uSRlPrPKPoPpPtPlPoPpPuPlPtPKPuG?FQEi3L3LPAQ0[Q0\Q0YC@P3fkS0]#3/hSflS0^#3Ru%DuRK60HA1:KrQ0^#7Rt/hSPtPSPtPSPSPtEj11tSRlPrQ0^#;RpPSPpPSPSPpCS11pSRoPrPKPtPlPuPoPtPlPpPoPuPKPpG?FQEi3L3LP<fmS0_#3Rp%DpRK60HAQ0_#7Ru/hSPuPSPuPSPSPuEj11uSRoPrQ0_#;RlPSPlPSPSPlCS11lSRtPrPKPuPoPpPtPuPoPlPtPpPKPlG?FQEi3L9WKrPAfnS0`Q0_Q0]C@P3foS0a#3RK%DK60HAfpRK#3Rl#DRp%7KRt/hSPtPSPtPSPSPtEj11tSRoPr%;KRKPSPKPSPSPKCS11KSRuPrPpPtPoPlPuPtPoPKPuPlPpPKG?FQEi3L7WrP<fqRK#3Rp#DRl/:r%7KRu/hSPuPSPuPSPSPuEj11uSRoPr%;KRtPSPtPSPSPtCS11tSRJPrPlPuPoPpPJPuPoPtPJPpPlPtG?FQEi3LPAfrS0bPKQ0aC@P3fsRK#3#D/:rftRt#7Rl/hSPlPSPlPSPSPlEj11lSRpPr%;tRJPSPJPSPSPJCS11JSRoPr%3tRt#DRuPlPpPtPoPlPpPJPoPtPuPJG?FQEi3LP<fuRJ#7Ru/hSPuPSPuPSPSPuCS11uSRtPr%;JRoPSPoPSPSPoCS11oSRpPr%3JRl#DRsPuPtPlPpPuPtPoPpPlPsPoG?FQEiH0GPAfvPJPKC@P3fwS0c#7/hSfxS0d#7RKPSPKPSPSPKCS11KSRJPrQ0d#;RoPSPoPSPSPoCS11oSRsPrQ0d#3Rl#DRpPKPJPlPsPKPJPoPsPlPpPoG?FQEiH0GP<fyRo#7RpPSPpPSPSPpEj11pSRlPr%;oRsPSPsPSPSPsCS11sSRJPr%3oRK#DRtPpPlPKPJPpPlPsPJPKPtPsG?FQEiPAfzS0ePoQ0cC@P3f{Ro#7RsPSPsPSPSPsEjf|S0f#7Rs/1SRtPrQ0f#;RKPSPKPSPSPKCS11KSRJPrQ0f#3Rl#DRpPsPtPlPJPsPtPKPJPlPpPKG?FQEiP<f}S0g#7RK/1SRp/:rQ0g#;RlPSPlPSPSPlCS11lSRJPrQ0g#3Rt#DRsPKPpPtPJPKPpPlPJPtPsPlG?FQH0GPAf~Q0gPoC@P3p+01@Ro#7?NSrp+01AS0h#;RlPSPlPSPSPlCS11lSRsPrQ0h#3Rt#DRJQ0h#7Rp11pSRKPtPsPpPKPlPsPtPJPlG?FQH0GP<p+01BRl#;RJPSPJPSPSPJEj11JSRtPr%3lRs#DRK%7lRp11pSRuPsPtPpPuPJPtPsPKPJG?FQPAp+01CPlPoC@P3p+01DRo#;RlPSPlPSPSPlEjp+01ES0i#;Rl/1SRJPrQ0i#3RK#DRsQ0i#7Rt11tSRuPKPJPtPuPlPJPKPsPlG?FQP<p+01FRl#;Rs/1SRK/:r%3lRJ#DRu%7lRt11tSRpPJPKPtPpPsPKPJPuPsG?D2PAp+01GPlPoC@P3p+01HRo#;?NSrp+01IS0j#3Rl#DRsQ0j#7Ru11uSRJPlQ0j#;RK/1SRpPuPJPKPpPlPsPKG?D2P<p+01JS0k#3RK#DRsQ0k#7Rl11lSRpPKC0Q0k#;RJ/1SRuPlPpPJPuPKPsPJG?PAp+01KQ0kPoC@P3p+01LRo#3RJ#D%7oRsPsPSPJDAp+01MS0l#;RJ/1SRsQ0l#7RKANKSJPsQ0l#3Rs%DsPJK1>P<p+01NS0m#;RJ/1SRsQ0m#7RKPKPSPJDAPsQ0m#3Rs%DsPJC0PAp+01OS0nQ0mPoC@P3p+01PRo#;RJ/1S%7oRoPoPSPJDAp+01QS0o#;RJ/1SQ0o#3Ro%DoPJC0PAp+01RS0p#3RJ%|O#a$05#XRO,1JRoQ0VH1=g04Z=Rs%[4R4Q04#[S0q&04N#[S0r+0jS0s5No9Wor,vJ7WJP<p+01SS0t#3RJ,:s11JORoQ0s9No47Wr,vJPAp+01TS0uQ0tQ0oC@P3p+01URJ#3,:sp+01VS0v#3Rs11sORsQ0s9Ns47Wr'vP<p+01WS0w#3Rs#G11sORsQ0s9Ns47WrPAp+01XS0xQ0wPJC@P3p+01YS0y#3#Gp+01Z#3/1ORJQ0s9NJ47WrP<p+01[S0z#3/1ORJ/:rQ0s9NJ4PAp+01\S0{Q0zQ0yC@P3p+01]S0|#3?NOrp+01^S0}#3/1OQ0s7N4Q0zp+01_S0~#3S10POPaPbp+01`S11#3RJPJPOPcDARsPb%EJS12Q12&0kORJPcDAPbQ11#7RoANoScPb&0FH$0;$04$0h$0W#XRo11o4S13PcC0S14Pb%8H#U#q$0;#|$0F#XRN%[?R?,1NS15PcC0S16Pb%8H#U#q$0;#|$04#XRK11K4RuPcC0S17Pb%8H#U#q$0;$0g$04#XRp11p4RlPcC0S18Pb%|H#a#U#a#a$0W$0F#[RtQ0I,1tRqPcC0S19Pb%8H#a#|$04#a$0W$04#XRvQ05#[S1:,1vRwPcC0S1;'43L3LS1<H1<3LS1=X2aPsX2aQ1=P<%<0Rsp+01aS1>#3S1?Q1?/1OS1@%=0RxC0S1APsQ1?#ES1BQ1B/1JS1CPxPsQ1>#7S1DQ1D/1SS1EPxPsPoQ13PxC0S1FPsPNQ15PxC0S1GPsPKPuPxC0S1HPsPpPlPxC0S1IPsPtPqPxC0S1JPsPvPwPxC0S1K'43L3LS1LD2D2%<;S1Mp+01bS1N#3S1OQ1O/1OS1P%=;S1QC0P3%<DS1Rp+01cS1S#3S1TQ1T/1OS1U%=DS1VC0%<>Ryp+01dS1W#3S1X#ES1YQ1Y/1JS1Z%=>RzPyQ1W#7S1[Q1[/1SS1\PzPyPoQ13PzPyPNQ15PzPyPKPuPzPyPpPlPzPyPtPqPzPyPvPwPzG?D2D2D2D2S1]D2D2P<%<IR{p+01eS1^#3S1_#ES1`Q1`/1JS1a%=IR|C0P{Q1^#7S1bQ1b/1SS1cP|P{PoQ13P|P{PNQ15P|P{PKPuP|P{PpPlP|P{PtPqP|P{PvPwP|G?D2D2D2D2S1dD2%<7S1ep+01fR}#3S1fQ1f/1OS1g%=7S1hC0P3%<2S1ip+01gR~#3S1j#ES1kQ1k/1JS1l%=2S1mC0%<VS1np+01hS1o#7S1pQ1p/1SS1q%=VS1rQ1nPoQ13Q1rQ1nPNQ15Q1rQ1nPKPuQ1rQ1nPpPlQ1rQ1nPtPqQ1rQ1nPvPwQ1rG?D2D2D2D2S1sD2P<%<GS1tp+01iS1u#7S1vQ1v/1SS1w%=GS1xC0Q1tPoQ13Q1xQ1tPNQ15Q1xQ1tPKPuQ1xQ1tPpPlQ1xQ1tPtPqQ1xQ1tPvPwQ1xG?D2D2D2D2S1y%<WS1zp+01jS1{#3S1|Q1|/1OS1}%=WS1~C0P3%<\S20p+01kS21#7S22Q22/1SS23%=\S24C0%<ZS25PoQ13%=ZS26Q25PNQ15Q26Q25PKPuQ26Q25PpPlQ26Q25PtPqQ26Q25PvPwQ26G?D2D2D2D2S26P<%<eS25PoQ13%=eS27C0S28Q25PNQ15Q27Q25PKPuQ27Q25PpPlQ27Q25PtPqQ27Q25PvPwQ27G?D2D2D2S27%<gS25p+01nS29#3S2:Q2:PO%=gS2;DAP3%<fPoQ13%=fC0S2<Q0K#<S2=PNQ15Q0K#=S2>Q2=PKPuQ2>Q2=PpPlQ2>Q2=PtPqQ2>Q2=PvPwQ2>G?D2D2D2S2>P<%<dS2=PNQ15%=dS2?C0S2@Q2=PKPuQ2?Q2=PpPlQ2?Q2=PtPqQ2?Q2=PvPwQ2?G?D2D2S2?%<iS2=p+022S2A#3S2BQ2BPO%=iS2BDAP3%<FS2CPNQ15%=FS2DC0S2EQ0L#<S2FPKPuQ0L#=S2GQ2FPpPlQ2GQ2FPtPqQ2GQ2FPvPwQ2GG?D2D2S2GP<%<kS2FPKPu%=kS2HC0S2IQ2FPpPlQ2HQ2FPtPqQ2HQ2FPvPwQ2HG?D2S2HQ0M#<S2Fp+026S2J#3S2KQ2KPOQ0M#=S2LDAP3%<hPKPu%=hC0S2M%<jS2NPpPl%=jS2OQ2NPtPqQ2OQ2NPvPwQ2OG?D2S2OP<Q0P#<S2NPpPlQ0P#=S2PC0S2QQ2NPtPqQ2PQ2NPvPwQ2PG?S2P%<mS2Np+02:S2R#3S2SQ2SPO%=mS2TDAP3Q0O#<PpPlQ0O#=C0S2UQ0N#<S2VPtPqQ0N#=RmQ2VPvPwPmG?S2VP<Q0S#<S0NPtPqQ0S#=RmC0S2WQ0NPvPwPmC0S0NQ0Q#<S2Xp+02>S2Y#3RmPmPOQ0Q#=S2ZDAP3%<nPtPq%=nC0S2[Q0R#<PvPwQ0R#=C0S2\Q0SWHWGP0P3O2n2001000000120000000W0WFP0P3O2n2001000000121000000W0WEP0P3O2n2011000000121000000W0WDP0P3O2n2011000000121000000W0WCP0P3O2n2011000000121000000W0WBP0P3O2n2011000000121000000W0WAP0P3O2n2011000000121000000W0W@P0P3O2n2011000000121000000W0X2aPbQ1?Q1@PcPbQ1BQ1CPcC0S1CPbQ1DQ1EPcC0Q1<3LD2S1EX2aRmP3O1Q1A[^?aeQ0zQ0YEgCfQ0zQ10;ZOQ0{Q12PJPaPmQ1CX2aQ1EP<PsQ1OQ1PPxC0PsQ1O#ES1CQ1C/1JS10PxC0S0zPsQ1N#7Rm11mSS0YPxC0Q1L3LQ1MQ1T#ES1AQ1A/1JS1BQ1QC0P3Q1RQ1XQ1X/1OS1@Q1VC0PyQ1`Q1aPzPyQ1bQ1cPzQ1]D2D2P<P{Q1f#ES1?Q1?/1JS1=P|C0P{%7}S2]Q2]/1SS2^P|Q1dD2Q1eQ1kQ1lQ1hC0P3Q1iQ1o#3S2_#ES2`Q2`/1JS2aQ1mC0Q1nQ1vQ1wQ1rQ1sD2P<Q1tQ1{#7S2bQ2b/1SS2cQ1xC0Q1yQ1zQ21#3S2d#ES2eQ2e/1JS2fQ1~C0P3Q20p+01lS2g#7S2hQ2h/1SS2iQ24C0Q26P<Q28Q27Q25p+01oS2j#3S2k#ES2lQ2l/1JS2mQ2;C0P3Q2<Q2>P<Q2@Q2?Q2=p+023S2n#3S2o#ES2pQ2pPJQ2BDAP3Q2EQ2GP<Q2IQ2HQ2Fp+027S2p#3S2q#ES2rQ2rPJQ2LDAP3Q2MQ2OP<Q2QQ2PQ2Np+02;S2r#3#ES2sQ2sPJQ2TDAP3Q2UQ2VP<Q2WQ0NQ2Xp+02?S2s#3#ES2tQ2tPJQ2ZDAP3Q2[Q2\Q0PWHWGP0P3O2n2001000000120000000W0WFP0P3O2n2001000000121000000W0WEP0P3O2n2011000000121000000W0WDP0P3O2n2011000000121000000W0WCP0P3O2n2011000000121000000W0WBP0P3O2n2011000000121000000W0WAP0P3O2n2011000000121000000W0W@P0P3O2n2011000000121000000W0X2aPbQ1OQ1PPcPbQ1CQ10PcPbPmQ0YPcC0S0YQ1<'4D2D2S10X2aRmP3O1Q0z[^?aeQ0{Q0ZEgCfQ0{Q12;ZJQ0|Q1DPSPaPmQ0YX2aQ10P<PsQ1TQ1UPxC0PsQ1AQ1BPxPsQ1S#7S0YQ0Y/1SS12PxC0S0{Q1L'4D2Q1MQ1[Q1\Q1QC0P3Q1RQ1_Q1_/1OS0ZQ1VC0PyQ1?Q1=PzPyQ2]Q2^PzQ1]D2D2P<P{Q1kQ1lP|C0P{%7~S0zQ0z/1SS1CP|Q1dD2Q1eQ1pQ1qQ1hC0P3Q1iQ1u#3Rm#ES1PQ1P/1JS1OQ1mC0Q1nQ2bQ2cQ1rQ1sD2P<Q1tQ22Q23Q1xC0Q1yQ1zQ2hQ2iQ1~C0P3Q20p+01mS1E#7S2tQ2t/1SS2uQ24C0Q26P<Q28Q27Q25p+020S2v#7S2wQ2w/1SS2xQ2;C0P3Q2<Q2>P<Q2@Q2?Q2=p+024S2y#7S2zQ2zPSQ2BDAP3Q2EQ2GP<Q2IQ2HQ2Fp+028S2{#7S2|Q2|PSQ2LDAP3Q2MQ2OP<Q2QQ2PQ2Np+02<S2}#7S2~Q2~PSQ2TDAP3Q2UQ2VP<Q2WQ0NQ2Xp+02@S2~#7S30Q30PSQ2ZDAP3Q2[Q2\PkWHWGP0P3O2n2001000000120000000W0WFP0P3O2n2001000000121000000W0WEP0P3O2n2011000000121000000W0WDP0P3O2n2011000000121000000W0WCP0P3O2n2011000000121000000W0WBP0P3O2n2011000000121000000W0WAP0P3O2n2011000000121000000W0W@P0P3O2n2011000000121000000W0X2aPbQ1TQ1UPcPbQ1AQ1BPcPbQ0YQ12PcQ1<D2D2D2S12X2aS0YP3O1Q0{[^?aeQ0|Q0\EgCfQ0|Q1D;ZSQ0}PoP4PaQ0YQ14X2aQ12P<PsQ1XQ1@PxC0PsQ1YQ1ZPxPsQ1[Q1\PxQ1LD2D2Q1MPoQ13Q1QC0P3Q1RQ1fQ1gQ1VC0PyQ1kQ1lPzPyQ0zQ1CPzQ1]D2D2P<P{Q2`Q2aP|C0P{Q1pQ1qP|Q1dD2Q1ePoQ13Q1hC0P3Q1iQ1|#ES14Q14/1JS0YQ1mC0Q1nQ22Q23Q1rQ1sD2P<Q1tQ2hQ2iQ1xC0Q1yQ1zPoQ13Q1~C0P3Q20Q29#7S1DQ1D/1SS0\Q24C0Q26P<Q28Q27Q25PoQ13Q2;C0P3Q2<Q2>P<Q2@Q2?Q2=PoQ13Q2BC0P3Q2EQ2GP<Q2IQ2HQ2FPoQ13Q2LC0P3Q2MQ2OP<Q2QQ2PQ2NPoQ13Q2TC0P3Q2UQ2VP<Q2WQ0NQ2XPoQ13Q2ZC0P3Q2[Q2\PdWHWGP0P3O2n2001000000120000000W0WFP0P3O2n2001000000121000000W0WEP0P3O2n2011000000121000000W0WDP0P3O2n2011000000121000000W0WCP0P3O2n2011000000121000000W0WBP0P3O2n2011000000121000000W0WAP0P3O2n2011000000121000000W0W@P0P3O2n2011000000121000000W0X2aPbQ1XQ1@PcPbQ1YQ1ZPcPbQ1[Q1\PcQ1<D2D2D2S1\X2aS1[P3O1Q1F[^?aeQ0}Q0[EgCfQ0}?Zo4Q0~PNP?PaQ1[Q16X2aQ1\P<PsQ1_Q0ZPxC0PsQ1`Q1aPxPsQ1bQ1cPxQ1LD2D2Q1MPNQ15Q1QC0P3Q1RQ1jQ1j/1OS16Q1VC0PyQ2`Q2aPzPyQ1pQ1qPzQ1]D2D2P<P{Q1PQ1OP|C0P{Q1vQ1wP|Q1dD2Q1ePNQ15Q1hC0P3Q1iQ2eQ2fQ1mC0Q1nQ2hQ2iQ1rQ1sD2P<Q1tQ2tQ2uQ1xC0Q1yQ1zPNQ15Q1~C0P3Q20Q2j#7S1[Q1[/1SS0}Q24C0Q26P<Q28Q27Q25PNQ15Q2;C0P3Q2<Q2>P<Q2@Q2?Q2=PNQ15Q2BC0P3Q2EQ2GP<Q2IQ2HQ2FPNQ15Q2LC0P3Q2MQ2OP<Q2QQ2PQ2NPNQ15Q2TC0P3Q2UQ2VP<Q2WQ0NQ2XPNQ15Q2ZC0P3Q2[Q2\PeWHWGP0P3O2n2001000000120000000W0WFP0P3O2n2001000000121000000W0WEP0P3O2n2011000000121000000W0WDP0P3O2n2011000000121000000W0WCP0P3O2n2011000000121000000W0WBP0P3O2n2011000000121000000W0WAP0P3O2n2011000000121000000W0W@P0P3O2n2011000000121000000W0X2aPbQ1_Q0ZPcPbQ1`Q1aPcPbQ1bQ1cPcQ1<D2D2D2S1cX2aS1bP3O1Q1G[^?aeQ0~Q0]EgCfQ0~?ZN?Q11PKP4PaQ1bQ17X2aQ1cP<PsQ1fQ1gPxC0PsQ1?Q1=PxPsQ2]Q2^PxQ1LD2D2Q1MPKPuQ1QC0P3Q1RQ2_Q2_/1OS17Q1VC0PyQ1PQ1OPzPyQ1vQ1wPzQ1]D2D2P<P{Q14Q0YP|C0P{Q2bQ2cP|Q1dD2Q1ePKPuQ1hC0P3Q1iQ2g#3S1b#ES0~Q0~/1JS0]Q1mC0Q1nQ2tQ2uQ1rQ1sD2P<Q1tQ1DQ0\Q1xC0Q1yQ1zPKPuQ1~C0P3Q20Q2wQ2xQ24C0Q26P<Q28Q27Q25PKPuQ2;C0P3Q2<Q2>P<Q2@Q2?Q2=PKPuQ2BC0P3Q2EQ2GP<Q2IQ2HQ2FPKPuQ2LC0P3Q2MQ2OP<Q2QQ2PQ2NPKPuQ2TC0P3Q2UQ2VP<Q2WQ0NQ2XPKPuQ2ZC0P3Q2[Q2\PGWHWGP0P3O2n2001000000120000000W0WFP0P3O2n2001000000121000000W0WEP0P3O2n2011000000121000000W0WDP0P3O2n2011000000121000000W0WCP0P3O2n2011000000121000000W0WBP0P3O2n2011000000121000000W0WAP0P3O2n2011000000121000000W0W@P0P3O2n2011000000121000000W0X2aPbQ1fQ1gPcPbQ1?Q1=PcPbQ2]Q2^PcQ1<D2D2D2S2^X2aRuP3O1Q1H[^?aeQ11Q0^EgCfQ11?ZK4Q1>PpP4PaPuQ18X2aQ2^P<PsQ1jQ16PxC0PsQ1kQ1lPxPsQ0zQ1CPxQ1LD2D2Q1MPpPlQ1QC0P3Q1RPm11mOS18Q1VC0PyQ14Q0YPzPyQ2bQ2cPzQ1]D2D2P<P{Q2eQ2fP|C0P{Q22Q23P|Q1dD2Q1ePpPlQ1hC0P3Q1iQ1E#3S2c#ERu11uJS2bQ1mC0Q1nQ1DQ0\Q1rQ1sD2P<Q1tQ1[Q0}Q1xC0Q1yQ1zPpPlQ1~C0P3Q20p+021S0\#7S0YQ0Y/1SS11Q24C0Q26P<Q28Q27Q25PpPlQ2;C0P3Q2<Q2>P<Q2@Q2?Q2=PpPlQ2BC0P3Q2EQ2GP<Q2IQ2HQ2FPpPlQ2LC0P3Q2MQ2OP<Q2QQ2PQ2NPpPlQ2TC0P3Q2UQ2VP<Q2WQ0NQ2XPpPlQ2ZC0P3Q2[Q2\PIWHWGP0P3O2n2001000000120000000W0WFP0P3O2n2001000000121000000W0WEP0P3O2n2011000000121000000W0WDP0P3O2n2011000000121000000W0WCP0P3O2n2011000000121000000W0WBP0P3O2n2011000000121000000W0WAP0P3O2n2011000000121000000W0W@P0P3O2n2011000000121000000W0X2aPbQ1jQ16PcPbQ1kQ1lPcPbQ0zQ1CPcQ1<D2D2D2RlX2aS1CP3O1Q1I[^?aeQ1>Q0_EgCfQ1>?Zp4Q1NPtQ0IPaQ1CQ19X2aP<PsQ2_Q17PxC0PsQ2`Q2aPxPsQ1pQ1qPxQ1LD2D2Q1MPtPqQ1QC0P3Q1RQ1|Q1}Q1VC0PyQ2eQ2fPzPyQ22Q23PzQ1]D2D2P<P{Q0~Q0]P|C0P{Q2hQ2iP|Q1dD2Q1ePtPqQ1hC0P3Q1iQ2:#ES23Q23PJQ1mDAQ1nQ1[Q0}Q1rQ1sD2P<Q1tQ2wQ2xQ1xC0Q1yQ1zPtPqQ1~C0P3Q20Q2A#7RJPJPSQ24DAQ26P<Q28Q27Q25PtPqQ2;C0P3Q2<Q2>P<Q2@Q2?Q2=PtPqQ2BC0P3Q2EQ2GP<Q2IQ2HQ2FPtPqQ2LC0P3Q2MQ2OP<Q2QQ2PQ2NPtPqQ2TC0P3Q2UQ2VP<Q2WQ0NQ2XPtPqQ2ZC0P3Q2[Q2\P0WHWGP0P3O2n2001000000120000000W0WFP0P3O2n2001000000121000000W0WEP0P3O2n2011000000121000000W0WDP0P3O2n2011000000121000000W0WCP0P3O2n2011000000121000000W0WBP0P3O2n2011000000121000000W0WAP0P3O2n2011000000121000000W0W@P0P3O2n2011000000121000000X0lX2aPbQ2_Q17PcPbQ2`Q2aPcPbQ1pQ1qPcQ1<D2D2D2RlX2aRqP3O1Q1J[^?aeQ1NQ0`EgCfQ1NQ0I7ZtQ1SPvQ1:PaPqQ1;X2aP<PsPmQ18PxC0PsQ1PQ1OPxPsQ1vQ1wPxQ1LD2D2Q1MPvPwQ1QC0P3Q1RQ2dQ2dPOQ1VDAPyQ0~Q0]PzPyQ2hQ2iPzQ1]D2D2P<P{PuQ2bP|C0P{Q2tQ2uP|Q1dD2Q1ePvPwQ1hC0P3Q1iQ2lQ2mQ1mC0Q1nQ2wQ2xQ1rQ1sD2P<Q1tQ0YQ11Q1xC0Q1yQ1zPvPwQ1~C0P3Q20Q2n#7S20Q20PSQ24DAQ26P<Q28Q27Q25PvPwQ2;C0P3Q2<Q2>P<Q2@Q2?Q2=PvPwQ2BC0P3Q2EQ2GP<Q2IQ2HQ2FPvPwQ2LC0P3Q2MQ2OP<Q2QQ2PQ2NPvPwQ2TC0P3Q2UQ2VP<Q2WQ0NQ2XPvPwQ2ZC0P3Q2[Q2\P3WHWGP0P3O2n2001000000120000000W0WFP0P3O2n2001000000121000000W0WEP0P3O2n2011000000121000000W0WDP0P3O2n2011000000121000000W0WCP0P3O2n2011000000121000000W0WBP0P3O2n2011000000121000000W0WAP0P3O2n2011000000121000000W0W@P0P3O2n2011000000121000000X0lX2aPbPmQ18PcPbQ1PQ1OPcPbQ1vQ1wPcQ1<D2D2D2X2aP3O1Q1K[^?aeQ1SQ0aEgCfQ1SQ1:7ZvQ1WQ1o00VMS1SP?PaQ1u#;Rl/1MS1:,:bRw11l5<0fcS1KX2aQ1:/1?>0fwcX2aQ1K&1;ARwQ0D#B#U#U#URl#8#U#U$0U$05$05#X/:rS1<%Bl#U#U$0U$05$05#XS1w80DrRlQ0qQ0r+1:Q0q$01Q0r#GQ0s$01[[Q0q#GR|g01_UR{Q0qQ0r<190UWOQ0s#G\{^O|Q2c@18SF%GSR|Q2:/pS#G[Q1D016SQ1D#GQ2w/pSR{#G\|[Q1[00dS&0TSR|$0eRuQ2wQ2w00BS-0bS/1{+0A[Q2w00aS&01SR{Q0Y/pSRz1OzS'v[Q0Y015S1OS1Rz1pJSRy,OS@0Dy1[214JSQ2000BS$0T\|Q20013SQ2z/pSQ2z+0A\|g01`1RJQ2z010SRyePyp+025S1[#300dSQ2KQ2K00BS-0bSQ2K/pS'1+0A\uQ2K00aSQ2q/pSRu1OuS'v\{Q2q015SQ2{#3R{/pSRu,OS@0Du1\z214{Sp+029S2q#3R{00BS$0T\|213{SQ2S/pSQ2S+0A\|PJQ2S010SRJePJg00iGS2S$0wRJQ2S$0NR|P620`6;S2KP020`6DS1DH0R&1Z6R{&1Y6Rz20Q6HRuQ04-0Q6S04%VM'{Ry5PzRqPzQ04%V5Q0D-0Q6S0DCu60|zQ02$1XS2:PzPy%V?Q0DCu:0|zqH03Q03-1WzRqP3P;g00k>S0sg00k^Ry+1VQ0s21S3;;6ydB1R610H1QRyb:b;b<X46XJ6XL6P3P0PMP0P5P;ETP011;MS0sQ0sP?PDDA[^46^J6^L6P3Q2DQ2}#;S2DQ2CPiO4b8Q2=Q2r00VMS2=Q2=P?Q2BDAeb|b{c05c04c03c02c01c00b~b}bzbKc0Ec0Fc0Gc0Hb0Y09X2aPbQ1{#;S1K/1MRbQ1KP5PcDAX2aP3O1PsPbPbP?PxDA[^?aeQ1WQ0aEgCfQ1WQ1S;Z?Q1u-0IAQ1u/^}RaQ1{Q2cQ0B3HX9B,9BX=E,9EX>E,9EXIES0B,9ES1S11mPS1WQ0C5H}S0a11mQS1KQ0F5H}S2B11mSS2==b}TS2CQ1P=b}CS0sQ21Q29?5>DO1=68XS0rPYQ2vP7PIP[Q2jEI\R[\L\U^6:^16^36S1OQ21,J]S18P`PDQ29P>P3H0MS26P8Q21Q29?5>3S2<O1P9I0yX169F^_[^76^56^36S2>'4S2E'4S2G'4S2M'4S2O'4S2U'4R]'4Q1>PaP]P<&0FH#q$0=$0U#a#q$0Y=c@=R]9H~oP~PN%8H#U#q#a$0g#q#X-06@Ra206@m<0L=P~PKQ1v=c@=P~Pp%8H#U#q$0h#|#a#X=c@=R[P~Q1vQ0E#[RY'1%8H#U#q$0;#|#a#X=c@=RHP~PtQ0J$0n/k=RXP~Pv20<@1$1P/k=RxQ1:=b~?FMFMFMQ1{/^~Q0|Q1u?Ho]Q1{PNQ1b-06@>0La=Q1{PKQ2h=c@=Q1{PpP[Q1{Q2h/1YPHQ1{PtPXQ1{PvPxQ1{Q2gPMP?CoFMFMFMP<Q21PNPaQ2c=c@=CrQ21PKQ2t=c@=Q21PpP[Q21Q2tPYPHQ21PtPXQ21PvPxQ21Q1EPMP?CoFMDCFMQ29Q21'^P3Q1EPNPaQ2k=c@=CrQ29PKQ2w=c@=Q29PpP[Q29Q2wPYPHQ29PtPXQ29PvPxQ29Q2vPMP?CoFMDCFMP<Q2jPKQ0Y-06@P=CrQ2jPpP[Q2jQ0Y/1YPHQ2jPtPXQ2jPvPxQ2jQ0\PMP?CoFMFMQ2AQ2j'^P3Q0\PKQ20-06@P=CrQ2APpP[Q2AQ2z/1YPHQ2APtPXQ2APvPxQ2AQ2yPMP?CoFMFMP<Q2n?Hp[Q2nQ1[#7PYPHQ2nPtPXQ2nPvPxQ2nQ1[PMP?CoFMDCQ2JQ2n'^P3Q1[?Hp[Q2JQ2|PYPHQ2JPtPXQ2JPvPxQ2JQ2{PMP?CoFMDCP<Q2pQ2q#7PYPHCyQ2pPtPXQ2pPvPxQ2pQ2qPMP?CoFMQ2RQ2p'^P3Q2qQ2r#7PYPHCyQ2RPtPXQ2RPvPxQ2RQ2DPMP?H0ZFMP<Q2r?HtXQ2rPvPxQ2rp+02=S2D#;PMP?K0xQ2YQ2r'^P3Q2D?HtXQ2YPvPxQ2YQ2~#;PMP?K0xP<Q2s?HvxQ2sp+02ARbPMP?Cop+02BRsQ2s'^P3AHbvxPsp+02DPMP?CoAHso]p+02ERc#3S2|-06@>0La=S2z9HsNS20%7cS0Y=c@=S2w9HsKS2kAHsp[S21Q0Y/1YRa=HsHS2tAHstXS2cAHsvxS1{20VcMS2h=bs?S0|'4S1:'4S0J'4S1v'4S0E'4S1>'4Pbp+02CRMPsPoP]Q0PQ0nQ0TAmbo]eGnQ20Q1>PbPMPsPNQ2zPkQ0nQ0VQ2z9mbNeGnQ2kQ0EPbPMPsPKQ2wPdQ0nQ0RQ2w9mbKeGnQ21Q1vPbPMPsPpP[PeQ0nPnAmbp[eGnQ2tQ0JPbPMPsPaPHPGQ0nPbQ0YPSPaQ0=$0KR[Q0UPwPlPJP|20`60RpP{%VY,{uRn9PzuPqPyb:b;b<X46113YRY,:3^46P3p+02G#7O1RKb8b0PwPlPJP|PpP{PzPn%V4Rn%VSRN,{uR]CuPqPyb:b;b<X46113SRo9NY4^46PKb8b0PwPlPJP|&1N6RKP{20v61R1=PznPqPyb:b;b<%G4P3b8b0RYN90?AmbaHeGnQ2cQ1:PbPMPsPtPXPIQ0nQ0QAmbtXeGnQ1{Q0|PbPMPsPvPxP0Q0nQ0SAmbvxeGnPbPMPsQ2hP?P3Q0n&01?Q0SWNL0^H0[FtFtFt1^cseW[WZP0P3O2n2001000000121000000W0WYP0P3O2n2001000000121000000W0WXP0P3O2n2001000000121000000W0WWP0P3O2n2001000000121000000W0WVP0P3O2n2011000000121000000W0WUP0P3O2n2011000000121000000W0WTP0P3O2n2011000000121000000Q1SQ2UPEQ0BQ0vPEQ1uQ1bQ0y#`Q0ACrX9B,9BX=E,9EX>EQ0pPEQ1oQ2dQ0x#`Q0uQ0@'_CrX9B,9BX=EQ0mPBP~Q1|Q0w#`Q0tQ0nQ0?'_'_CrX9BQ0kQ1^P~P}PmQ0vQ0pQ0mQ0>Q0k+0{/k='_'_'_R=Q0jQ0bQ1^PmPOPmQ0>$0}$0O$0KPGPwPlPJP|PpP{APzuuPqPyb:b;b<X461:33^46P3Q2dO1R?b8b0PwPlPJP|PpP{%VPRx,{uRv%VORX,{uRt5PzPqPyb:b;b<X46113PRa113ORH':^46P?b8b0PwPlPJP|PKP{APz1xPqPyb:b;b<%GPP3b8b0N90?Q1^?mm=eGnH0@H0@H0@H0@Q0aQ2OQ1^P~P}Q1WQ0CQ0iQ0bQ1^PmPOQ1WP[PGPwPlPJP|PpP{APzuvPqPyb:b;b<X461:3a^46P?b8b0PwPlPJP|PpP{PzPvPnPtCuPqPyb:b;b<X46ANa4H^46P?b8b0PYN90?Q1^Q1WQ0C3meGnQ2BQ2MQ1^P~P}Q1KQ0FQ0hQ0bQ1^PmPOQ1KQ08$0KPGPwPlPJP|PpP{%VQ,{uRm9PzuPqPyb:b;b<X46113QRQ,:3^46P?b8b0PwPlPJP|PpP{PzPmQ0I#VRmPtCuPqPyb:b;b<X46Q0I=NQH^46P?b8b0PwPlPJP|PKP{APz1mPqPyb:b;b<Q0I#GP3b8b0N90?Q1^Q1KQ0F3meGnQ2CQ2GQ1^P~P}Q2=PTQ0fQ0b&01TP}Q1|POQ1|/1SRm20lOSR?PWPwPlPJP|PpP{APzu]PqPyb:b;b<X461:3o^46P3Q1bO1RQb8b0PwPlPJP|PpP{PzP]B1L6XNRpPtCuPqPyb:b;b<X46ANo?H^46PQb8b0PwPlPJP|PKP{APz1pPqPyb:b;b<%G?P3b8b0N90?AZ}mTeWNL0^Q0sQ2EQ1^P~P}Q1PPCQ0dQ0b&01CPGQ14=Z}CeWNL0^Q1OQ2>Q0rQ2vP7PIPDP;I0uQ2v#3R}/1SQ2v?~7IRCQ05#a$05#XR~,1},OC3WP8Q29Q0\?~27RC$0JR}O120C:79683XS8P;Q2jP}O1R}Q1EQ2jQ29Q0\#3POPCQ0ePdPwPlPJP|P6Q2KP0PKH0RP{PzQ049Pz]Q04%V~R],{u+0S-0Ez60>zQ2:Q049PzuQ0400St-0Ez60>zH03PqPyb:b;b<X46XJ6Rt113~,O09Wo0110O,O;9W0;[^46^J6RoP3Q2n?~GVRCQ2oP;O3b8bKPwPlp-0RmQ2SQ0;-006Q08-006Q07-006RT60966096g00jRR?+0tQ2SQ0<-006Q0:-006Q09-006>096T6096609600t?;zJ3zP|P6P6Q1DPDPKH0RP0Q2KH0RP{PzPzQ01Q02Q02Q03PIJ1JQ05-0Q6R{Q1w#V5Pz60>zQ2:PzPzQ0DPNPuCuQ0D/{]-0Su-0Ez60>zQ2:PzPzQ0DPXP{CuQ2:PzQ0D9Pz1Q2:APz1uQ0q#V>1I6@-0Su-0Ez60>zH03H03H03H03PqPyb:b;b<X46XJ6XL6WRRyQ1w:0DD;11;S11;~,O07W0ANDO>%G>RqQ0q00j5:0:q>[[[[^46^J6^L6^RmRmP3Q1<PrQ2oPCP0P;PkQ0PO8b8bKN:0sJ1H20C:I968}Q0gPVP2P7PIP>P3P;O7bMb0Z0ARWMXQLXPUX6:X16X36Q18Q0cPDP;P0P3O4P`Q26P8Q2gQ2<O1P9I0yX169F^_P<20Xq>%s>Q0HP3PIP>Q2jPIP3Q1EQ2j?5I3O1=689GeX16#l60r;%GI%}IPD%sIQ0HP3P7PIQ2vP7P3Q1EQ2v?573O1=689GeX16#lI08P3%}7,v7%s2Q0HP3PVP2Q2APVP3Q2vQ2A?5V3O1=689GeX16#l60rIP<20P7VQ0HP3PGPVQ2nPGP3Q0\Q2n?5G3O1=689GeX16#l%GGR7%}GP2%sGQ0HP3PWPGQ2yPWP3Q0\Q2y?5W3O1=689GeX16#lI08P320PVWQ0HP3PZP\Q2JPZP3Q2yQ2J?5Z3O1=689GeX16#lQ00P6Q0HP3PePZQ2pPeP3Q1[Q2p?5e3O1=689GeX16%Ge%}eP\%seQ0HP3PgPeQ2{PgP3Q1[Q2{?5g3O1=689GeX16#lI08P3Q0HP3PfPgQ2qPfP3Q2pQ2q?5f3O1=689GeP<Q0K-1G0,v0PfQ2RQ0KP0P8Q2{Q2RQ0K;50O1P9K0q%Gd%}dPf%sdQ0H&02iRf,O3PdQ2}@07i3Q2qQ2}?5i3O1=689I08X16#lI08P3Q0G@0:DfPiQ2DPFP>P8Q2rQ2D?5F>O1P9K0qP<PFQ2YQ0LPIH0MQ2}Q2YQ0L;5IO1=689%Gk%}kPF%skQ0HP3Q0MPkQ2~Q0MP3Q2DQ2~Q0M;53O1=689GeX16#lI08P3PkQ2~Q0MP2H0MQ2sA5bhVO1=689%}j,vjQ0M00PjRVQ0HP3Q0PPjPMQ0PP3Q2~Q0P=5M3O1=689GeX16R2#lRk'4PdPVPkPeP6P2PG&02j:0:7GPhPsPjPGH0MRhQ2sA~sjGR7$0JO1=689R2'4PIPhP2P0PsPjPGPdPII0u%3sRs/1S11s~,O77W7P8PbQ0P=~MWRW$0JR7O1A6839XS8P0Q2~P7O1Q2sPbQ2~%3MPOPWQ0lQ0UPwPlPtPoP3Q0O=~cZRcQ2|P;O3b8bKPwPlPyPmP3Q1<PrQ2|PcP0P;Q0WQ0XO8b8bKN:0sJ1Fb0FtH0@FtWMY06P0P3O2n2001000000121000000W0WQP0P3O2n2001000000121000000W0X16P0P3O2n200100000012110K000W0Y0:P0P3O2n2001000000121000000W0WPP0P3O2n2001000000121000000b?Y08X76X56X36FtFtFtFtbhbbbab`b_b^b]bebgbfWyWxP0P3O2n2001000000121000000W0WwP0P3O2n2001000000121000000W0WvP0P3O2n2001000000121000000b0PAQ0pQ0oQ0nC@eWmWlP0P3O2n2001000000121000000W0WuP0P3O2n2001000000121000000W0WtP0P3O2n2001000000121000000W0WsP0P3O2n2001000000121000000W0WrP0P3O2n2011000000121000000W0WqP0P3O2n2011000000121000000W0WpP0P3O2n2011000000121000000W0WoP0P3O2n2011000000121000000W0WnP0P3O2n2011000000121000000W0WkP0P3O2n2011000000121000000b0Y0CY0BY0?Y0>WiP0P3O2n2001000000121000000W0WdP0P3O2n2001000000121000000W0WcP0P3O2n2001000000121000000W0Y0@P0P3O2n2011000000121000000W0Y0=P0P3O2n2011000000121000000W0Y07X9BP0P3O2n200100001012110K000W0X=EP0P3O2n200100001012110K000W0X>EP0P3O2n200100001012110K000W0XIEP0P3O2n200100001012110K000W0P0P3O2n2111000000121000000W0W\P0P3O2n2011000000121000000W0WjP0P3O2n2011000000121000000W0Y0DY0JY0IY0<Y0;&1EA$1Deo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qcoupled_add1_sec : forall L s s' X X' Q Q' mb ms n k (newb : list xbusy),
  qcoupled L s X Q ->
  length (q_loc Q') = length (a_qloc s') -> length (q_glob Q') = length (a_qglob s') ->
  Permutation (qentries (a_qloc s') (q_loc Q') ++ qentries (a_qglob s') (q_glob Q'))
              ((CSec mb ms n, k) :: qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)) ->
  Permutation (map qb_slot (q_loc Q' ++ q_glob Q')) (map xb_slot newb ++ map qb_slot (q_loc Q ++ q_glob Q)) ->
  (forall y, In y (x_busy X') /\ xb_st y = BQuar <-> In y (x_busy X) /\ xb_st y = BQuar) ->
  (forall y, In y (x_busy X') /\ xb_st y = BBatch <-> (In y (x_busy X) /\ xb_st y = BBatch) \/ In y newb) ->
  Forall (fun y => xb_st y = BBatch /\ xb_class y = K_BATCH_CLASS /\ 0 <= xb_slot y) newb ->
  (forall y, In y (x_busy X) -> xb_st y = BBatch -> xb_class y = K_BATCH_CLASS -> In (xb_slot y) (map xb_slot newb) -> False) ->
  List.NoDup (map xb_slot newb) ->
  q_pend Q' = q_pend Q ->
  qcoupled L s' X' Q'.
Proof.
  intros L s s' X X' Q Q' mb ms n k newb (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 PE PB HQ HB NEWB FB NDB PD.
  assert (PEQ : Permutation (qprim_ids (qentries (a_qloc s') (q_loc Q') ++ qentries (a_qglob s') (q_glob Q')))
                             (qprim_ids (qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)))).
  { pose proof (qprim_ids_perm _ _ PE) as P. cbn [qprim_ids flat_map fst snd app] in P. exact P. }
  unfold qcoupled. cbv zeta. rewrite PD.
  split; [exact L1|]. split; [exact L2|]. split.
  { eapply Permutation_Forall; [apply Permutation_sym; exact PE|]. constructor; [exact I|].
    eapply Forall_impl; [| exact OK]. intros [ch k'] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
    destruct ch as [c' n'| mb' ms' n']; [| exact I]. destruct HOK as (b1' & ctx' & Hin). exists b1', ctx'.
    apply (proj1 (proj2 (HQ _) (conj Hin eq_refl))). }
  split; [eapply Permutation_NoDup'; [apply Permutation_app_tail; apply Permutation_sym; exact PEQ| exact ND1]|].
  split.
  { eapply Permutation_NoDup'; [apply Permutation_sym; exact PB|]. apply List.NoDup_app; [exact NDB| exact ND2|].
    intros k0 Hn Ho. apply (BS k0) in Ho. destruct Ho as (y & Hy & Sy & Cy & Ky). subst k0. exact (FB y Hy Sy Cy Hn). }
  split.
  { intros k0. split.
    - intros H. apply (Permutation_in _ PB) in H. apply in_app_iff in H. destruct H as [H|H].
      + apply in_map_iff in H. destruct H as (y & <- & Hy). pose proof (proj1 (Forall_forall _ _) NEWB y Hy) as (Sy & Cy & _).
        exists y. split; [apply (proj1 (proj2 (HB y) (or_intror Hy)))|]. auto.
      + apply (BS k0) in H. destruct H as (y & Hy & Sy & Cy & Ky). exists y. split; [apply (proj1 (proj2 (HB y) (or_introl (conj Hy Sy))))|]. auto.
    - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_sym; exact PB|]. apply in_app_iff.
      destruct (proj1 (HB y) (conj Hy Sy)) as [[Hy0 _]|Hn].
      + right. apply (BS k0). exists y. auto.
      + left. subst k0. apply in_map. exact Hn. }
  split.
  { intros c0 k0. split.
    - intros H. apply (Permutation_in _ (Permutation_app_tail (q_pend Q) PEQ)) in H.
      apply (PS c0 k0) in H. destruct H as (y & Hy & Sy & Cy & Ky). exists y. split; [apply (proj1 (proj2 (HQ y) (conj Hy Sy)))|]. auto.
    - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_app_tail; apply Permutation_sym; exact PEQ|].
      apply (PS c0 k0). exists y. pose proof (proj1 (HQ y) (conj Hy Sy)) as [Hy0 _]. auto. }
  eapply Permutation_Forall; [apply Permutation_sym; exact PB|]. apply Forall_app. split; [| exact NN].
  apply Forall_forall. intros k0 H. apply in_map_iff in H. destruct H as (y & <- & Hy).
  pose proof (proj1 (Forall_forall _ _) NEWB y Hy) as (_ & _ & P). exact P.
Qed.

Section QUpdatesS.
Variables (L : alayout) (st : astate) (X : aconc) (Q : qconc) (mb ms n : Z).
Let ch := CSec mb ms n.
Hypothesis WF : awf L st X.
Hypothesis CP : qcoupled L st X Q.

(* [comment removed for export] *)
Lemma qcoupled_app_sec : forall s' l bl ql qz ia k,
  a_qloc st = l ++ [bl] -> q_loc Q = ql ++ [qz] ->
  a_qloc s' = l ++ [mkABatch (b_count bl + 1) (b_size bl + n) (ch :: b_chunks bl)] -> a_qglob s' = a_qglob st ->
  qcoupled L s' X (mkQConc (ql ++ [mkQB (qb_slot qz) (k :: qb_ks qz)]) (q_glob Q) ia (q_pend Q)).
Proof.
  intros s' l bl ql qz ia k QL QQ QL' QG'.
  pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _).
  assert (LNl : length ql = length l).
  { rewrite QL, QQ, !length_app in LN1. cbn in LN1. lia. }
  eapply (qcoupled_add1_sec L st s' X X Q _ mb ms n k []); try exact CP.
  - cbn [q_loc]. rewrite QL', !length_app. cbn. lia.
  - cbn [q_glob]. rewrite QG'. exact LN2.
  - cbn [q_loc q_glob]. rewrite QL', QG', QL, QQ. rewrite !qentries_app by exact LNl. cbn [qentries combine b_chunks qb_ks app].
    rewrite <- !app_assoc. cbn [app]. apply Permutation_sym. rewrite ?app_nil_r.
    apply Permutation_middle.
  - cbn [q_loc q_glob map app]. rewrite QQ, !map_app. cbn [map qb_slot]. apply Permutation_refl.
  - intros y; tauto.
  - intros y. cbn [In]. tauto.
  - constructor.
  - intros y _ _ _ [].
  - constructor.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma qcoupled_new_sec : forall s' k24 cnt sz ia k,
  c_count (get_cls st K_BATCH_CLASS) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (cnt - 1)) = Some k24 ->
  a_qloc s' = a_qloc st ++ [mkABatch 1 sz [ch]] -> a_qglob s' = a_qglob st ->
  qcoupled L s' (xbatch X k24) (mkQConc (q_loc Q ++ [mkQB k24 [k]]) (q_glob Q) ia (q_pend Q)).
Proof.
  intros s' k24 cnt sz ia k CNT POS NK QL' QG'.
  pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & _ & BS & _).
  pose proof (k24_not_busy L _ X k24 cnt WF CNT POS NK) as (NB & KR & _).
  eapply (qcoupled_add1_sec L st s' X (xbatch X k24) Q _ mb ms n k [bbatch k24]); try exact CP.
  - cbn [q_loc]. rewrite QL', !length_app. cbn. lia.
  - cbn [q_glob]. rewrite QG'. exact LN2.
  - cbn [q_loc q_glob]. rewrite QL', QG'. rewrite !qentries_app by exact LN1. cbn [qentries combine b_chunks qb_ks app].
    apply Permutation_sym. rewrite <- ?app_assoc. cbn [app]. apply Permutation_middle.
  - cbn [q_loc q_glob map xb_slot bbatch]. rewrite <- app_assoc, !map_app. cbn [map qb_slot app]. apply Permutation_sym.
    apply Permutation_middle.
  - intros y. rewrite (In_xbatch X k24 y). unfold bbatch. split.
    + intros [[-> |H] S]; [cbn in S; discriminate| exact (conj H S)].
    + intros [H S]. split; [right; exact H| exact S].
  - intros y. rewrite (In_xbatch X k24 y). cbn [In]. split.
    + intros [[-> |H] S]; [right; left; reflexivity| left; exact (conj H S)].
    + intros [[H S]|[<-|[]]]; [split; [right; exact H| exact S]| split; [left; reflexivity| reflexivity]].
  - constructor; [| constructor]. cbn. split; [reflexivity|]. split; [reflexivity| lia].
  - intros y Hy Sy Cy Hin. cbn in Hin. destruct Hin as [E|[]]. apply NB.
    unfold busy_slots. rewrite E. apply in_map. apply List.filter_In. split; [exact Hy| rewrite Cy; apply Z.eqb_refl].
  - constructor; [intros []| constructor].
  - reflexivity.
Qed.
End QUpdatesS.
End CANSEC1.
(* [comment removed for export] *)
