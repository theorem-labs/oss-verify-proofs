(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (22 recorded proofs replaced by written proofs (sec_chunk_in_ranges, avoids_all_In, asec_wf_all and 19 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes ARep ARepKit ARepFrame ALayout AHeapP
     AKitQ AMalloc_iface ADepot_iface ASec ASecFacts ASecFrame ASecModel AModelFacts APrimFacts F_amalloc_arep ARepExt.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASecStore () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC35stdpp4gmap;gmap_lookupC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC46Stdlib5Lists4List8map_consC35stdpp4gmap;gmap_finmapC46Stdlib5Lists4List8flat_mapC35stdpp4base6LookupC46Stdlib5Lists4List7existsbI46Stdlib5Lists4List5NoDup00I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4base4fmapC46Stdlib5Lists4List6nth_okC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterK59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C46Stdlib5Lists4List6filterI47Corelib4Init5Logic3and00C46Stdlib5Lists4List9filter_InC59OSSVerify5KrLib4Spec8AsanCtrl7achunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP6is_secC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec8AsanCtrl;asec_rangesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List;in_flat_mapC59OSSVerify5KrLib4Spec8AsanCtrl6sec_ivC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes4prod01I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC59OSSVerify5KrLib4Spec8AsanCtrl:avoids_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8iv_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z3lebC46Stdlib4Bool4Bool8orb_propI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5BothW4ASec7asec_wfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec<sec_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7sec_wf1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C46Stdlib5Lists4List2hdC59OSSVerify5KrLib5BothW9ASecModelAsfresh_true_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<sec_map_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6is_errC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecFacts9sec_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec8AsanCtrl;needed_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface4pcovC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib5BothW5ABase4al_VC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01C59OSSVerify5KrLib5BothW=AMalloc_iface:pcov_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec8AsanCtrl5TWO64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib5BothW4ASec>astartup_hullsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6al_resC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02c59OSSVerify5KrLib5BothW9ASecStore9valid_geoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffC59OSSVerify5KrLib5BothW6AHeapP9sec_clearC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASecStore;valid_hullsC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib5BothW6AHeapP6sec_mbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP6sec_msC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8ablk_linC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init5Logic2or02c59OSSVerify5KrLib5BothW9ASecStoreCsec_chunk_in_rangesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASecStore=avoids_all_InC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASecStore;valid_clearC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec4ashzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07C59OSSVerify5KrLib5BothW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List;Forall_implC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indc59OSSVerify5KrLib5BothW9ASecStore:wview_someC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3KLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_HIGH_MEMC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K46Stdlib7Sorting;Permutation;Permutation01K46Stdlib7Sorting;Permutation;Permutation02K46Stdlib7Sorting;Permutation;Permutation03C46Stdlib7Sorting;Permutation@Permutation_reflC46Stdlib7Sorting;PermutationAPermutation_transC46Stdlib7Sorting;Permutation?Permutation_indI46Stdlib7Sorting;Permutation;Permutation00C35stdpp8fin_mapsBmap_to_list_insertC35stdpp4base6lookupC35stdpp4base6insertC59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC46Stdlib7Sorting;Permutation?Permutation_mapc59OSSVerify5KrLib5BothW9ASecStoreBfilter_is_sec_permC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationDPermutation_app_tailC59OSSVerify5KrLib5BothW6AHeapPAfilter_is_sec_appC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listC47Corelib5Lists7ListDef3mapI47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z6inj_ltI59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASecStore>awf_fresh_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecModel=st_sec_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecModel6st_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5a_clsC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecModel>get_cls_st_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecModel@max_count_st_secC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat3N2Z8inj_succC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableC59OSSVerify5KrLib5BothW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6hb_idsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_userC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7ab_kindC1?~~~~~~~~~~~~~~~K46Stdlib5Lists4List5NoDup02I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8SEC_UOFFC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6abkind00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9arng_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4RSECC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASecStoreHsec_chunks_of_insert_secC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_symC59OSSVerify5KrLib5BothW6AHeapP9RSEC_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib5BothW4ASec5ASECcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec8asec_arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec9asec_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec6aprim0C1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_lengthC47Corelib7Program6Basics4implC46Stdlib7Sorting;Permutation>Permutation_inC59OSSVerify5KrLib5BothW4ASecAsec_disjoint_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec8sec_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec:asec_chunkC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationI47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9shlen_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8granulesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec?sec_user_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame:junk_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame:fill_frameC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec9SEC_MAGICC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula01C46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib5BothW4ASec7ASEC_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6ao_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout4aobjC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC46Stdlib7Sorting;PermutationDPermutation_app_commC59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AKitQ:u64arr_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<u64arr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AKitQ;u64arr_snocC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appC59OSSVerify5KrLib5BothW7ARepKit:junk_splitC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decc59OSSVerify5KrLib5BothW9ASecStore=junk_zero_lenC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesI47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_app1C46Stdlib5Lists4List<nth_error_Inc59OSSVerify5KrLib5BothW9ASecStore;asec_wf_allC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos7compareC47Corelib4Init9Datatypes7CompOppC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z<pos_div_euclC57Corelib7BinNums6PosDef3Pos3mulC59OSSVerify5KrLib4Spec8AsanCtrl7needed0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl3rupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASecStoreAasec_chunk_frameWC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC46Stdlib5Lists4List>nth_error_app2C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;azero_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame@disjoint_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASecStore:ASECc_permC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C59OSSVerify5KrLib4Spec8AsanCtrl:K_MAX_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl2PGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASecStore>asec_chunk_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8K_REGIONC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASecStore2WTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepExt8nonemptyC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib5BothW7ARepExtDdisjoint_from_ForallC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma sec_chunk_in_ranges : forall st mb ms n, In (CSec mb ms n) (sec_chunks_of st) -> In (mb, mb + ms) (asec_ranges st).
Proof.
  intros st mb ms n H. unfold sec_chunks_of in H. apply List.filter_In in H. destruct H as [H _].
  unfold asec_ranges. apply in_flat_map. exists (CSec mb ms n). split; [exact H| left; reflexivity].
Qed.

Lemma avoids_all_In : forall a n l iv, avoids_all a n l = true -> In iv l -> a + n <= fst iv \/ snd iv <= a.
Proof.
  intros a n l iv H Hin. unfold avoids_all in H. rewrite forallb_forall in H. specialize (H iv Hin).
  unfold iv_clear in H. apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

(* [comment removed for export] *)
Lemma asec_wf_all : forall L st cs ch, asec_wf L st cs -> In ch cs -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n).
Proof.
  intros L st cs ch (_ & _ & _ & _ & _ & WF1 & _) Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1.
  destruct ch as [c n|mb ms n]; [destruct W1|]. exists mb, ms, n. split; [reflexivity| exact W1].
Qed.

Section Valid.
Variables (L : alayout) (RESV : list (Z * Z)) (st : astate) (n a : Z).
Let ms := sec_map_size n.
Hypothesis ALO : alayout_ok L.
Hypothesis N : 1 <= n <= AREQMAX.
Hypothesis PRIM : is_primary n = false.
Hypothesis FR : sfresh RESV st n a = true.
Hypothesis ROK : aresv_ok L RESV.

Lemma valid_geo : a mod 4096 = 0 /\ ablk a (a + ms) /\ a + ms <= ATOP /\ 0 < ms /\ ms = sec_map_size n.
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & AV & _ & POS & AL & TOPB & _).   (* [comment removed for export] *)
  pose proof (sec_facts n N PRIM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSB).
  destruct ROK as (R1 & R2 & _).
  pose proof (pcov_clear _ _ _ _ _ R1 AV ltac:(unfold AIMG_HI; clear; lia) ltac:(clear -MSB; lia)) as C1.   (* [comment removed for export] *)
  pose proof (pcov_clear _ _ _ _ _ R2 AV ltac:(clear; lia) ltac:(clear -MSB; lia)) as C2.                    (* [comment removed for export] *)
  subst ms. split; [exact AL|]. split; [| split; [exact TOPB| split; [clear -MSB; lia| reflexivity]]].
  unfold ablk, KLS. unfold AIMG_HI in *. clear -C1 C2 POS TOPB MSB. lia.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma valid_hulls : Forall (fun iv => a + ms <= fst iv \/ snd iv <= a) (astartup_hulls L).
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & AV & _ & _ & _ & _ & _).   (* [comment removed for export] *)
  pose proof valid_geo as (_ & _ & _ & MSP & _).
  destruct ROK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  unfold astartup_hulls. fold (al_res L) in R3. change (4096 * al_V L 323%nat) with (al_dtls L) in R10.
  repeat (apply Forall_cons; [cbn [fst snd]; eapply pcov_clear; [eassumption| exact AV| clear; lia| exact MSP] |]). apply Forall_nil.
Qed.

Lemma valid_clear : sec_clear L a ms.
Proof.
  pose proof valid_hulls as H. unfold astartup_hulls in H.
  repeat lazymatch type of H with Forall _ (_ :: _) => apply Forall_cons_iff in H; destruct H as [? H] | _ => idtac end.
  cbn [fst snd] in *. unfold sec_clear. repeat split; lia.
Qed.

Lemma valid_chunks : Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) (sec_chunks_of st).
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & _ & AV & _ & _ & _ & _).   (* [comment removed for export] *)
  apply Forall_forall. intros ch Hin. destruct ch as [c k|mb ms' k]; cbn [sec_mb sec_ms].
  - pose proof valid_geo as (_ & G & _). pose proof (ablk_lin _ _ G) as (_ & G0 & _). right. clear -G0. lia.   (* [comment removed for export] *)
  - pose proof (avoids_all_In _ _ _ _ AV (sec_chunk_in_ranges st mb ms' k Hin)) as D. cbn [fst snd] in D. exact D.
Qed.

Lemma valid_wf1 : sec_wf1 L (CSec a ms n).
Proof.
  pose proof valid_geo as (G1 & G2 & G3 & G4 & G5). pose proof (sec_facts n N PRIM) as (NB & _).
  cbn [sec_wf1]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G5|].
  split; [lia|]. split; [exact PRIM| exact valid_clear].
Qed.
End Valid.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wview_some : forall m (x : word) b, m x = Some b -> wview bsegs m x = Some b.
Proof. intros m x b H. unfold wview. rewrite H. reflexivity. Qed.

Lemma ashz_azero : forall L cs m a ms,
  ashz L cs m ->
  a mod 8 = 0 -> ablk a (a + ms) -> a + ms <= ATOP -> 0 <= ms ->
  Forall (fun iv => a + ms <= fst iv \/ snd iv <= a) (astartup_hulls L) ->
  Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) cs ->
  azero m (shad a) (ms / 8).
Proof.
  intros L cs m a ms SHZ A8 ALO AHI MS0 HH HC.
  assert (PT : forall i, 0 <= i < ms / 8 -> m (wa (shad a + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. replace (shad a + i) with (shad (a + 8 * i)) by (rewrite !shad_div; clear -A8; Z.div_mod_to_equations; lia).
    apply SHZ.
    - unfold ablk, KLS, K_HIGH_MEM in *. unfold AIMG_HI in *. clear -Hi ALO AHI A8. Z.div_mod_to_equations. lia.   (* [comment removed for export] *)
    - eapply Forall_impl; [| exact HH]. cbn beta. intros iv Hiv. clear -Hi Hiv A8. Z.div_mod_to_equations. lia.
    - eapply Forall_impl; [| exact HC]. cbn beta. intros ch Hch. clear -Hi Hch A8. Z.div_mod_to_equations. lia. }
  assert (SR : 0 <= shad a /\ shad a + ms / 8 <= 2^64).
  { pose proof (ablk_lin _ _ ALO) as (AL1 & AL2 & AL3 & AL4). rewrite shad_div. unfold ASHOFF in *. clear -AL2 AL4 AHI MS0. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
  split; [exact PT|]. split; [lia|]. split; [lia|]. intros i Hi. rewrite (wview_some _ _ _ (PT i Hi)). discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma filter_is_sec_perm : forall (l l' : list achunk), Permutation l l' -> Permutation (List.filter is_sec l) (List.filter is_sec l').
Proof.
  intros l l' HP. induction HP; cbn; [constructor| | |].
  - destruct (is_sec x); [apply perm_skip|]; assumption.
  - destruct (is_sec x), (is_sec y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

(* [comment removed for export] *)
Lemma sec_chunks_of_insert_sec : forall st st' p mb ms n,
  (a_live st) !! p = None ->
  a_live st' = <[p := CSec mb ms n]> (a_live st) -> a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  Permutation (sec_chunks_of st') (CSec mb ms n :: sec_chunks_of st).
Proof.
  intros st st' p mb ms n NONE E1 E2 E3. unfold sec_chunks_of, achunks. rewrite E1, E2, E3, !filter_is_sec_app.
  change (CSec mb ms n :: List.filter is_sec (map snd (map_to_list (a_live st))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st)))
    with ((CSec mb ms n :: List.filter is_sec (map snd (map_to_list (a_live st)))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))).
  apply Permutation_app_tail.
  pose proof (map_to_list_insert (a_live st) p (CSec mb ms n) NONE) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P.
  eapply Permutation_trans; [apply filter_is_sec_perm; exact P|]. cbn. apply Permutation_refl.
Qed.

Lemma awf_fresh_none : forall L st X, awf L st X -> (a_live st) !! (a_next st) = None.
Proof.
  intros L st X WF. destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _).
  destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as F. clear -F. lia.
Qed.

Lemma awf_sec : forall L st X nres' a ms n, awf L st X -> awf L (st_sec st nres' a ms n) X.
Proof.
  intros L st X nres' a ms n WF.
  pose proof (awf_fresh_none L st X WF) as NONE.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof (st_sec_fields st nres' a ms n) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  unfold awf. rewrite E1, E2, E7, E8.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split. { intros c Hc. rewrite get_cls_st_sec, max_count_st_sec. unfold ndist. rewrite get_cls_st_sec. exact (PERC c Hc). }
  split. { intros c Hc. rewrite get_cls_st_sec. exact (OUTC c Hc). }
  split. { intros b Hb. destruct (BUSY b Hb) as [CLB M]. split; [exact CLB|]. destruct (xb_st b) as [p| |]; try exact M.
           destruct M as (M1 & M2 & M3 & M4 & M5 & M6). repeat (split; [assumption|]).
           rewrite lookup_insert_ne; [exact M6|]. intros E. assert (X0 : a_live st !! p = None) by (rewrite <- E; exact NONE). rewrite X0 in M6. discriminate. }
  split. { intros p c k Hp. destruct (N.eq_dec p (a_next st)) as [->|NE].
           - rewrite lookup_insert_eq in Hp. discriminate.
           - rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). exact (LIVE p c k Hp). }
  split. { intros p ch Hp. destruct (N.eq_dec p (a_next st)) as [->|NE]; [lia|].
           rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). pose proof (FRESH p ch Hp). lia. }
  exact UNIQ.
Qed.

Lemma ablocks_sec : forall L st X LB nres' a ms n,
  awf L st X -> ablocks L st X LB -> sec_wf1 L (CSec a ms n) ->
  ablocks L (st_sec st nres' a ms n) X (HB (a_next st) (a + SEC_UOFF) n :: LB).
Proof.
  intros L st X LB nres' a ms n WF (BH & BF & NDI & NDL) W1.
  pose proof (awf_fresh_none L st X WF) as NONE.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _ & FRESH & _).
  pose proof (st_sec_fields st nres' a ms n) as (_ & _ & _ & _ & _ & _ & E7 & _).
  assert (OLD : forall p A n', In (HB p A n') LB -> (p < a_next st)%N).
  { intros p A n' Hin. destruct (BH p A n' Hin) as [(b & Hb & Sb & _)|(mb & ms' & Lp & _)].
    - destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (FRESH _ _ M5).
    - exact (FRESH _ _ Lp). }
  split; [| split; [| split]].
  - intros p A n' [E|Hin].
    + injection E as <- <- <-. right. exists a, ms. rewrite E7, lookup_insert_eq. split; [reflexivity|]. split; [reflexivity| exact W1].
    + destruct (BH p A n' Hin) as [(b & Hb & R)|(mb & ms' & Lp & R)].
      * left. exists b. split; [exact Hb| exact R].
      * right. exists mb, ms'. split; [| exact R]. rewrite E7, lookup_insert_ne; [exact Lp|].
        intros E. pose proof (OLD _ _ _ Hin) as F. rewrite E in F. clear -F. lia.
  - intros cls A n' [E|Hin]; [discriminate| exact (BF cls A n' Hin)].
  - cbn. constructor; [| exact NDI]. intros Hin. unfold hb_ids in Hin. apply in_flat_map in Hin. destruct Hin as (b & Hb & Hp).
    destruct b as [[p|cls] A n']; cbn in Hp; [| destruct Hp]. destruct Hp as [E|[]]. subst p. pose proof (OLD _ _ _ Hb) as F. clear -F. lia.
  - constructor; [| exact NDL]. intros Hin. pose proof (OLD _ _ _ Hin) as F. clear -F. lia.
Qed.

Lemma arng_sec : forall L RNG RNG' st X nres' a ms n,
  awf L st X -> arng L RNG st -> fp_le RNG RNG' ->
  rng RNG' a ms -> rng RNG' (shad a) (ms / 8) -> rng RNG' (al_ptr_array L) (8 * nres') ->
  arng L RNG' (st_sec st nres' a ms n).
Proof.
  intros L RNG RNG' st X nres' a ms n WF AR LE R1 R2 R3.
  pose proof (arng_mono L RNG RNG' st LE AR) as (A1 & A2 & A3 & A4 & A5 & A6 & A6a & A6b & A6c & A7 & A8 & A9 & A10).
  pose proof (st_sec_fields st nres' a ms n) as (_ & _ & E3 & _ & _ & _ & E7 & _ & E9 & _ & E11 & _).
  unfold arng. rewrite E3. repeat (split; [assumption|]). split; [| exact A10].
  eapply RSEC_perm; [apply Permutation_sym; eapply sec_chunks_of_insert_sec; [eapply awf_fresh_none; exact WF| exact E7| exact E9| exact E11]|].
  constructor; [| exact A9]. cbn [sec_mb sec_ms]. split; [exact R1| exact R2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Proof.
  intros cs cs' L st X m P (WFS & ARR & INST & PZ & SHZ).
  split; [| split; [| split; [exact INST| split; [exact PZ|]]]].
  - destruct WFS as (ALO & WP & WR & WL & WB & WF1 & WD). unfold asec_wf.
    split; [exact ALO|]. split; [exact WP|]. split; [exact WR|]. split; [rewrite <- (Permutation_length P); exact WL|]. split; [exact WB|].
    split; [| eapply sec_disjoint_perm; [exact P| exact WD]].
    rewrite Forall_forall in WF1 |- *. intros ch Hin. apply WF1. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
  - destruct ARR as (order & PO & U64 & JK & PER). exists order. split; [eapply Permutation_trans; [exact PO| exact P]|].
    split; [exact U64| split; [exact JK| exact PER]].
  - intros x Hx HF HC. apply (SHZ x Hx HF). rewrite Forall_forall in HC |- *. intros ch Hin. apply HC.
    eapply Permutation_in; [exact P| exact Hin].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asec_chunk_frameW : forall L W m m' mb ms n idx lv,
  munch W m m' -> wmono bsegs m m' ->
  sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb <= A -> A + k <= mb + ms -> 0 < k -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> A + k <= shad mb + ms / 8 -> 0 < k -> disjoint_from W A k) ->
  asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros L W m m' mb ms n idx lv MU WM WF1 DC DS CH.
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & _). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  destruct GR as (GR1 & GR2 & GR3).
  cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in *.
  split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frame; [exact H5| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frame; [exact H6| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed.

Lemma junk_zero_len : forall m A n, junk_at m A n -> n <= 0 -> forall m', junk_at m' A n.
Proof.
  intros m A n [bs H] Hn m'. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
  split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Section Append.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Variables (st : astate) (X : aconc) (nres' a n id : Z).
Let ms := sec_map_size n.
Let cs := sec_chunks_of st.
Let nsec := a_nsec st.
Let nres := a_nres st.
Let PA := al_ptr_array L.
Let UB := a + 6144.
Hypothesis WF : awf L st X.
Hypothesis SEC : ASECc cs L st X m.
Hypothesis N : 1 <= n <= AREQMAX.
Hypothesis PRIM : is_primary n = false.
Hypothesis W1 : sec_wf1 L (CSec a ms n).
Hypothesis DJ : Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) cs.
Hypothesis NR' : (nsec <> nres /\ nres' = nres)
              \/ (nsec = nres /\ nres' = nres + 16384
                  /\ rw_cells bsegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))]).
Hypothesis NRB : nres' <= 1048576.
(* [comment removed for export] *)
Hypothesis Wch : forall ch, In ch cs ->
     (forall A k, sec_mb ch <= A -> A + k <= sec_mb ch + sec_ms ch -> 0 < k -> disjoint_from W A k)
  /\ (forall A k, shad (sec_mb ch) <= A -> A + k <= shad (sec_mb ch) + sec_ms ch / 8 -> 0 < k -> disjoint_from W A k).
Hypothesis Wpa : 0 < nsec -> disjoint_from W PA (8 * nsec).
Hypothesis Wpj : nsec + 1 < nres -> disjoint_from W (PA + 8 * nsec + 8) (8 * (nres - nsec - 1)).
Hypothesis Wbase : disjoint_from W (AINSTANCE + 80) 8.
Hypothesis Wp0 : disjoint_from W (shad (al_space_beg L)) (shlen K_REGION).
Hypothesis Wshz : forall x, (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) -> (x < a \/ a + ms <= x) -> disjoint_from W (shad x) 1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis C_srt : rw_cells bsegs m' (AINSTANCE + 128) [C1 (Z_to_bv 8 0)].
Hypothesis C_jst : junk_at m' (AINSTANCE + 136) 32.
Hypothesis C_jbs : junk_at m' (AINSTANCE + 168) 512.
Hypothesis C_mtx : rw_cells bsegs m' (AINSTANCE + 680) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Hypothesis C_jgl : junk_at m' (AINSTANCE + 704) 16.
Hypothesis C_slot : rw_cells bsegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)].
Hypothesis C_hdr : rw_cells bsegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)].
Hypothesis C_pgj : junk_at m' (a + 32) (4096 - 32).
Hypothesis C_mag : rw_cells bsegs m' (a + 4096) [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))].
Hypothesis C_lcj : junk_at m' (a + 4096 + 16) (2048 - 32).
Hypothesis C_ahd : rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
Hypothesis IDR : 0 < id < 2^31.
Hypothesis C_usr : junk_at m' UB (ms - 6144).
Hypothesis C_shf : fill_at m' (shad a) 768 0xfa.
Hypothesis C_shu : rw_cells bsegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)].
Hypothesis C_sht : fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa.

Lemma asec_chunk_new : asec_chunk m' (CSec a ms n) nsec true.
Proof.
  cbn [asec_chunk]. unfold SEC_UOFF, SEC_MAGIC. fold UB.
  replace (UB - 16) with (UB + -16) by (subst UB; lia).
  split; [exact C_hdr|]. split; [exact C_pgj|]. split; [exact C_mag|]. split; [exact C_lcj|].
  split. { exists 17, id. split; [exact C_ahd|]. split; [lia|]. split; [reflexivity| lia]. }
  split; [unfold SEC_UOFF; exact C_usr|]. split; [exact C_shf|]. split; [| exact C_sht].
  unfold sec_user_shadow. exact C_shu.
Qed.

Theorem asec_append : ASEC_of L (st_sec st nres' a ms n) X m'.
Proof.
  pose proof (awf_fresh_none L st X WF) as NONE.
  pose proof (st_sec_fields st nres' a ms n) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  destruct SEC as (WFS & ARR & INST & PZ & SHZ).
  pose proof WFS as (ALO & WP & WR & WL & WB & WF1 & WD).
  pose proof W1 as W0. cbn [sec_wf1] in W0. destruct W0 as (G1 & G2 & G3 & G4 & G5 & G6 & GC).
  pose proof (sec_facts n N PRIM) as (NB & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & MSB). fold ms in MSR, MSM, MSB.
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. fold PA in OP.
  assert (NEWNOT : ~ In (CSec a ms n) cs).
  { intros Hin. pose proof (proj1 (Forall_forall _ _) DJ _ Hin) as D. cbn [sec_mb sec_ms] in D. clear -D MSB. lia. }
  assert (NSR : 0 <= nsec /\ nsec + 1 <= nres' /\ (nres' = nres \/ nres' = nres + 16384)).
  { subst nsec nres. destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia. }
  destruct NSR as (NS0 & NS1 & NS2).
  unfold ASEC_of. eapply ASECc_perm; [apply Permutation_sym; eapply sec_chunks_of_insert_sec; [exact NONE| exact E7| exact E9| exact E11]|].
  fold cs. split; [| split; [| split; [| split]]].
  - (* [comment removed for export] *)
    unfold asec_wf. rewrite E2, E3, E4. split; [exact ALO|]. split; [exact WP|].
    split. { split; [| clear -NRB NS0 NS1; lia]. destruct WR as [WRM _]. destruct NS2 as [-> | ->]; [exact WRM|].
             subst nres. clear -WRM. Z.div_mod_to_equations. lia. }
    split; [cbn [length]; subst nsec; clear -WL; lia|]. split; [clear -NS0 NS1; subst nsec; lia|].
    split; [constructor; [exact W1| exact WF1]|].
    destruct WD as [ND PW]. split; [constructor; [exact NEWNOT| exact ND]|].
    intros ci cj [<-|Hi] [<-|Hj] NE; [exfalso; exact (NE eq_refl)| | |].
    + pose proof (proj1 (Forall_forall _ _) DJ _ Hj) as D. cbn [sec_mb sec_ms] in D |- *. clear -D. lia.
    + pose proof (proj1 (Forall_forall _ _) DJ _ Hi) as D. cbn [sec_mb sec_ms] in D |- *. clear -D. lia.
    + exact (PW ci cj Hi Hj NE).
  - (* [comment removed for export] *)
    destruct ARR as (order & PO & U64 & JK & PER). unfold asec_arr. rewrite E3, E4. fold PA. fold nsec.
    assert (LEN : Z.of_nat (length order) = nsec) by (rewrite (Permutation_length PO); exact WL).
    exists (order ++ [CSec a ms n]).
    split. { eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip. exact PO. }
    split; [| split].
    + rewrite map_app. cbn [map sec_mb]. apply u64arr_snoc.
      * destruct order as [|o0 order'].
        { destruct U64 as [[B0 [B1 _]] _]. apply u64arr_nil; [clear -OP; lia| clear -OP; atop_facts; lia]. }
        eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. cbn [length] in LEN |- *.
        replace (8 * Z.of_nat (S (length order'))) with (8 * nsec) by (clear -LEN; lia). apply Wpa. clear -LEN; lia.
      * rewrite length_map. replace (PA + 8 * Z.of_nat (length order)) with (PA + 8 * nsec) by (clear -LEN; lia). exact C_slot.
    + destruct NR' as [(A1 & A2)|(A1 & A2 & ZC)].
      * rewrite A2. destruct (junk_split m (PA + 8 * nsec) 8 (8 * (nres - nsec - 1))
                      ltac:(replace (8 + 8 * (nres - nsec - 1)) with (8 * (nres - nsec)) by (clear; lia); exact JK) ltac:(clear; lia) ltac:(clear -A1 WB; subst nsec nres; lia))
          as [_ JR].
        replace (PA + 8 * (nsec + 1)) with (PA + 8 * nsec + 8) by (clear; lia).
        replace (8 * (nres - (nsec + 1))) with (8 * (nres - nsec - 1)) by (clear; lia).
        destruct (Z_lt_le_dec (nsec + 1) nres) as [LT|GE].
        { eapply junk_frame; [exact JR| exact MU| exact WM| intros _; apply Wpj; exact LT]. }
        eapply junk_zero_len; [exact JR| clear -GE; lia].
      * rewrite A2, A1. subst nres. replace (PA + 8 * (a_nres st + 1)) with (PA + 8 * a_nres st + 8) by (clear; lia).
        replace (8 * (a_nres st + 16384 - (a_nres st + 1))) with (131072 - 8) by (clear; lia). eexists. exact ZC.
    + intros i ch Hi.
      destruct (Nat.lt_ge_cases i (length order)) as [LT|GE].
      * rewrite nth_error_app1 in Hi by exact LT. destruct (PER i ch Hi) as (lv & LV & CH).
        assert (Hin : In ch cs) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
        destruct (asec_wf_all L st cs ch WFS Hin) as (mb & ms' & n' & -> & WF1c).
        exists lv. split.
        { rewrite LV. unfold sec_live. rewrite E7. split; intros [p Hp].
          - exists p. rewrite lookup_insert_ne; [exact Hp|]. intros E. subst p. rewrite NONE in Hp. discriminate.
          - destruct (N.eq_dec p (a_next st)) as [->|NE].
            + rewrite lookup_insert_eq in Hp. injection Hp as Ea Em En. exfalso. apply NEWNOT. rewrite <- Ea, <- Em, <- En in Hin. exact Hin.
            + exists p. rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). exact Hp. }
        destruct (Wch _ Hin) as [DC DS]. cbn [sec_mb sec_ms] in DC, DS.
        eapply asec_chunk_frameW; [exact MU| exact WM| exact WF1c| exact DC| exact DS| exact CH].
      * rewrite nth_error_app2 in Hi by exact GE.
        assert (EI : i = length order) by (destruct (i - length order)%nat as [|k] eqn:EK; [clear -GE EK; lia| cbn in Hi; destruct k; discriminate]).
        subst i. rewrite Nat.sub_diag in Hi. cbn in Hi. injection Hi as <-.
        exists true. split.
        { split; [intros _| reflexivity]. exists (a_next st). rewrite E7, lookup_insert_eq. reflexivity. }
        rewrite LEN. exact asec_chunk_new.
  - (* [comment removed for export] *)
    destruct INST as (I1 & _ & _ & _ & _ & _). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; exact Wbase]|].
    split; [exists (Z_to_bv 8 0); exact C_srt|]. split; [exact C_jst|]. split; [exact C_jbs|]. split; [| exact C_jgl].
    pose proof C_mtx as M4. rw_split M4 1%nat M0 M3. exact M3.
  - (* [comment removed for export] *)
    unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM| intros _; exact Wp0].
  - (* [comment removed for export] *)
    intros x Hx HF HC. apply Forall_cons_iff in HC. destruct HC as [HCn HC]. cbn [sec_mb sec_ms] in HCn.
    assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; unfold AIMG_HI, KLS in Hx; clear -Hx; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia]. apply Wshz; [exact Hx| clear -HCn Hx; lia].
Qed.
End Append.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WT (L : alayout) (sp a ms nsec nres nres' : Z) : list (Z * Z) :=
  [(sp - 4096, sp); (al_t L + 2800, al_t L + 3169); (AINSTANCE + 112, AINSTANCE + 720);
   (al_ptr_array L + 8 * nsec, al_ptr_array L + 8 * nsec + 8); (al_ptr_array L + 8 * nres, al_ptr_array L + 8 * nres');
   (a, a + ms); (shad a, shad a + ms / 8);
   (0x18c1c8, 0x5dc210); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z.

(* [comment removed for export] *)
Definition wt_facts (L : alayout) (sp lo a ms nsec nres nres' : Z) : Prop :=
     alayout_ok L /\ ATOP <= lo /\ lo <= sp - 4096
  /\ ablk a (a + ms) /\ a + ms <= ATOP /\ a mod 4096 = 0 /\ ms mod 4096 = 0 /\ 0 < ms /\ sec_clear L a ms
  /\ 0 <= nsec /\ nsec + 1 <= nres' /\ 8 * nres' <= 8388608 /\ 0 <= nres <= nres'.

(* [comment removed for export] *)
Local Lemma ablk_int : forall lo hi, ablk lo hi ->      (* [comment removed for export] *)
  exists k, 0 <= k <= 1 /\ 6352896 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_ASecStore ()) ["CANSEC1"] "h01Hh14__p1h24__x1h34__x2h44__x3h51kh62H1h77__arithh84__ffh98__varmaph:5__with;2H0h<2hih=2lop;3p;1p;2p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p10137p4p710R1p8P0p1002lp4p710p8P0p1003MR2p4p710p8P0P2p4p7210p8p1003jp4p710R2p1004HR0p4p710R3p8P2P0p4p7210R0p8p1004ap4p70R4P1p8P4p1005Xp4p710R1p8P4p10064p4p710p8P4p1006Rp4p7210p8P4p1006op4p710R5p8P4p1007MR6p4p710p8P4p1007fR7p4p710p8P4p1008=R8p4p710p8P4p1008YR9p4p710p8P4p10096p4p710p8P4p1009OR:p4p710p8P4P:p4p7210p8P4p1009lR:p4p710R;p8P4p100:@p4p710p8P4p100:\p4p710p8p100;8R4p4p73101R<p100;RR=p4p73110p8P<p100;kR>p4p73110p8P<p100<Gp4p710p8P<p100<ZR?p4p7201p8P<p100<lp4p7201p8P<P:p4p73110p8P<p100=>R:p4p73110p8P<p100=RR@p4p73110p8P<p100=lp4p7201p8P4p4p710R<P=p4p710p8P<P>p4p710p8P<P3p8P<P0p8P<P;p8P<P:p4p710p8P<P@p4p710p8p100>?R@p4p710R<P2p8P<P3p8P<P0p8P<p100>Sp4p73110p8P@p4p741110R@P8p4p73101p8p100>ep4p710P1p8P9p4p7210P5p8p100?@p4p7<111111111110R9P1p8P9P5p8p100?bp4p7<111111111110R9P1p8P9P5p8P6p4p741110R6P4p4p7511100R5p8P5P6p8p100@Dp4p741110R6P4p4p76111100R5p8P5P6p8p100@\p4p741110R6P4p4p771111100R5p8P5P6p8P7p4p741110R7P4p4p7:1111111100R4p8P4P7p8P?p4p7200R?P@p8P@P?p8g018_j3bTg01FPj1aTg00Zaj15Tg00YYj11Tg00k<j1:Tg014Tj1OTg00V5j20Tg00D1R?j2<Tg01<hj2=Tg00G<j2DTg00HWj2ITg01?@j1CTg01GNj2BTg01H7j3HTg01H`j2VTg00Jdj1UTg01ILj3TTg00C6j1STg00W1j2ETg00WOj4RTg00Wmj1QTg00XKj1PTg00Y6j2ATg00`Qj6NTg00\1j1MTg01Djj2GTg01QCj3@Tg00Z>j3FTg00\Sj2LTg00KDj2`Tg00]5j2_Tg00JJj3^Tg00]aj3[Tg00^@j4ZTg00LSj4JTg00[Fj4YTg00_mj7\Tg01Ilj7WTg00aYj8]Tf0R@#5#5#5#5p=7%5@#5p=X%1@#1p=?%1@#1#1#1p=9%1@#1#1#1#1#1#1#1p=3f2R7f1R4'0/<@p=21<4@,<7p=>g00OHR6/G@p=8P7g00b=R5g00b\R9P9g00c<R1P6P4g00eMP@CYg00c\F\p=4P7P5P9P9P1P4P@FWp=6f3R8P5P9P9P1P7P4P@G]p=;104@,<7p=Kp,2rcR<?b4@%a<g00dhR0#5R3#5#7#7#7R2#1#5#XR:#5#7#1#?#9#3#3#:R;%O<R<'0R>%52#7#7#1#?#9#3#3#:R2,0<R='<g00U[%50#1#9#7#9#3#:RA/08RB%9:#3#:R:,07RC'<%10RD#9#3RE#7#7#7#7#1#?#9#3#:RF107<728g00f4RG%:0RH,0@72@RIf5RJ,0ARK1=F@RLf4RM%1E#?#3#3#3#3#3#3#:RE,=@,D:RN10M<RO3272J3>X56,I6P4108:92AMP?PK10M:f7RK,0ARPf6RQ10Q<72N92LK5>IX56,I6RQP@10K:P6f:RR,0Af9RS10S<72N92LR5>IX56RIPGp-0RLg00d<RNg01MGRT#C#CRU#C,B61B6U1B6T5H65H6g01Mf'V%UN3TRT%SNRNP61E67P41E68CRRU%Q6RV%P6RW%8;1A63R354WPWP5P9P9P1PJENR556W%M9R9PW1A6DRD%8:RX54WP9PW%8A1A60R054WRYP91G6GRZ=4WZ%8HR[94WZR\56W%8FR]=@6Z=4W0%8ER^9@6Z9F6X94WDA4WD3RZ56W56W96WY56WC;C;C;1LW1R1P@P7g00NHR_g00NhR`'`1_@7=^_`dA[6G4CZR`b8b9b:X26X36X46W1A2;7810A710GHRA92GG1=FG1=GE,D:10MJRG52M7287>B[\C[^26^36^46^1LP@P=P<PSPRPKP4P7O7b7CJW6X0PP4P@O2n2001000010121000000W0P@O1108<92FMP?10FJPOPQP@10FK10K<P6PIPHPTPNPUPVPW%8294W396W5P9PWPZP9PWA4W]0P9A4W[[96W\A@6][=4W0A@6[^9F6X94WD=6WZ56W96WY56WC;C;C;P1P`b8b9b:X26X36X46X1LAK872107810F7AKAHH1=FH1=HE,D:=2MG7287>B[[[^26^36^46^1LP@P>P<PSPRPKP4P7O7b7CJW6W0P4P@O2n2001000010121000000W0P@O1n200100001021100011000b;W0X<6X=6o"). Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6352896 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_ASecStore ()) ["CANSEC1"] "h04__x1h14__x2h21Hh31kh47__arithh54__ffh68__varmaph75__with84__x3h94__p1h:2H0h;2H1h<3H10h=2H2h>2H3h?2H4h@2H5hA2H6hB2H7hC2H8hD2H9hE2HnhF6__sat6hG1ahH1np;3p;1p;2p;4p;7p;6p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p10137p4p710R1p8P0p1002lp4p710p8P0p1003MR2p4p710p8P0P2p4p7210p8p1003jp4p710R2p1004HR0p4p710R3p8P2P0p4p7210R0p8p1004ap4p70R4P1p8P4p1005Xp4p710R1p8P4p10064p4p710p8P4p1006Rp4p7210p8P4p1006op4p710R5p8P4p1007MR6p4p710p8P4p1007fR7p4p710p8P4p1008=R8p4p710p8P4p1008YR9p4p710p8P4p10096p4p710p8P4p1009OR:p4p710p8P4P:p4p7210p8P4p1009lR:p4p710R;p8P4p100:@p4p710p8P4p100:\p4p710p8p100;8R4p4p73101R<p100;RR=p4p73110p8P<p100;kR>p4p73110p8P<p100<Gp4p710p8P<p100<ZR?p4p7201p8P<p100<lp4p7201p8P<P:p4p73110p8P<p100=>R:p4p73110p8P<p100=RR@p4p73110p8P<p100=lp4p7201p8P4p4p710R<P=p4p710p8P<P>p4p710p8P<P3p8P<P0p8P<P;p8P<P:p4p710p8P<P@p4p710p8p100>?R@p4p710R<P2p8P<P3p8P<P0p8P<p100>Sp4p73110p8P@p4p741110R@P8p4p73101p8p100>ep4p710P1p8P9p4p7210P5p8p100?@p4p7<111111111110R9P1p8P9P5p8p100?bp4p7<111111111110R9P1p8P9P5p8P6p4p741110R6P4p4p7511100R5p8P5P6p8p100@Dp4p741110R6P4p4p76111100R5p8P5P6p8p100@\p4p741110R6P4p4p771111100R5p8P5P6p8P7p4p741110R7P4p4p7:1111111100R4p8P4P7p8P?p4p7200R?P@p8P@P?p8g04NMj3yTg00YYj12Tg00k<j1;Tg00V5j20Tg01FPj1oTg00Zaj17Tg014Tj1^Tg00kZj2BTg00G<j21Tg01<hj2?Tg00D1R?j28Tg01]Ij2dTg01maj2cTg01nBj1aTg01<Kj2STg00JJj3LTg01n[j2`Tg018Cj2KTg01oBj2_Tg01oij2]Tg020Oj2\Tg04QFj2[Tg01?@j1JTg01GNj2GTg01H7j3NTg01H`j2ZTg00Jdj1xTg01ILj3YTg00C6j1wTg00_2j1vTg00W1j2XTg00WOj4HTg00Wmj1uTg00XKj1tTg00Y6j2PTg00\1j1rTg00Z>j3MTg00a5j7qTg00\Sj2pTg00KDj2nTg00]5j2mTg00]aj3lTg00^@j4kTg01Djj2UTg01QCj3OTg00LSj4VTg00`Qj6iTg00L8j4TTg00U[R@j2WTg00HWj2hTg00[Fj4gTg00_mj7fTg01Ilj7sTg00aYj8eTf0R7#2#2p=D%27#2#2#2#2#2#2#2p=5%77#7#7#7p=9%77#7p=b%27#2#2#2p=@f2R4f1R6/07'8p=Eg00OHR5g00f4R97L7p=Qf3R1/041067'Wp=31867,84p=R1046/87,81p=:1097p=C1146/07p=F1067,84,81p=I1h57p=A1046/87p=61U57p==P4g00b=R8g00b\R<P<g00c<R0P5P6g00eMP7Cgg00c\Ffp=4P4P8P<P<P0P6P7Fsp=>P1P8P<P<P0P4P6P7Gep=<1W67,84p=jp,2rcR3?y67g00dhR2#2R:#2R;#D#5R>#2R=#2#DRA#;RB/06RC%o3%72RD#7#9#9#9RE#2#7#bRF#7#9#2#D#@#5#5#;%^3R3'0RG%7E#9#9#2#D#@#5#5#;RE7E3P?f4RH%;>R>'B#Q10>HRI11H1RJP3PJ%@F#5#;RF%9=#9#9#9#2#D#@#5#;R=PHC3PJPB%72#2#@#9#@#5#;RJPHC37RIC:f5RI11IH%C7%;2RK7E7RLf6RM%5A#5#5#5#5#5#;RA,?7,1FRN7FI1?=7ROPMCIX35#A76356JP41BM>#Qf7RP,0>RQ11PMRRP3PRPFP=PPC3PRPBPJPPC37RQC:P?f8RQ,0>RR11QPRPPPPFP=PQC3PPPBPJPQC37RR763f9RR11RQPLf:RP?FRNPOPPCIX35#A76356JP710>Pf;RR/1PRPPPPFP=PRC3P>PRPPPBPJPRC3C:763P?f<RP/1RRR/03PRPFP=PPC3P>PPPRPBPJPPC3C:f=RR11RPPLf>RS/1RRRPN10OSC:X35#A76356JP710R3f?RR/1SRSPFP=PRC3P>PRPSPBPJPRC3C:P?f@R?/1RRRPFP=P?C3PRPBPJP?C396>?fARR11R?PLfBR?/1RRSPN10O?C:X35#A76356JP7PSPFP=P?C3fCRS11S?PBPJPSC356>fDR?,0J11?SRT/03RUPLfERV/1?RWPN10OVC:X35#ARX'81d?>%C?%C>fFRY/B>RZ#C[[1cV>%Q>R[#a1SY>,?>/1Z9L5Y[1`Y>1K9>fGRZ/B>R\#C1K\>'8[1_Z>1K>9fHR\/B>R],K>?E]9[1]\>fIR\/S>#Q\[1\\>fJR]/B>=L5]\[g02?^1[]>R]eP]g00d<R]g01MGR[#JR^#JR_#JR`#J,G51G5^R^1G5_5N55N5g01MfR_'Z%x]Ra3Y%w]RbP5%v5RcP61X54RdCH%u5Re%t5Rf%=BRg1P5DRD54f%r<RhPf%=>1P52R254fRiPfP8P<P<P0AM52D=4fg%=J=4f2RgFq5>fPhPfPiPhPgC<C<C<1pf0RgP7P4g00NHRjg00NhRk'n1m74=LjkdAl596CkRkb5b6b7X05X1510>6Rj1164Rl/0B10J63j10>410J1[[\C^05^15P7fKRCfLP\PQPRO5b410JCeb<bDbCbBbAb2bFPUPXPaPbP5PdP61X51RXCHPePf1P5:9M52R:=4fDRDPhPDC<PgPkb5b6b7X05X15X851176RD/0410l1[^05^15^85P7P3P?PVPMO4b4P@10TF10=?PLAFYVNPOPYCIX35#AP610WFP5PLAFZYNPOPZCIX35ROP9PaPbP5PdP6PcCHPePf%=FRd94f:PhPfPiPh1U59Ri=4fi%=KRN94fiRL5>f%=ARW9O5i9M5d94f:%==R?=O5i=4f25>f5>fC<C<PgPkb5b6b7X05X1510DF%CKRD96991141Ri1?9A,1F1?=9/04C:\j[^05^15P7PYPZP6PPO4b4CVW2P7O110=VP5POPKp-0RO1G5`1G5[9N5^5N5/Z_=Y]aPbP5P5PXP4PcCHP6PcCHPePfPfP8P<P<P0PIEi1P5;R;%=E54f5>fPhPfA4f?2PhPfA4f:;PhA4fNN9>fLAO5NW9M5d94f:AO5?N=4f25>f5>fC<C<C<PgPkb5b6b7X05X15X85W9AE14E10=610iHAEDKK1?KA,1F9F1H1?=KP1CI[[[^05^15^85^9OP7PGP3PYPZPSP6PQO7b4CVW2P7O1n200100001021100011000CTCTW@W?P6P7O2n2001000010121000000W2W>P6P7O2n2001000010121000000W2W=P6P7O2n2011000010121000000W2W;P6P7O2n2011000010121000000b:WEW2XH5XG5o"). Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6352896 * j <= a).
Proof.
ltac2:(KReplay.run1 (kr_t_ASecStore ()) ["CANSEC1"] "h04__x1h11jh21Hh31kh47__arithh54__ffh68__varmaph75__with84__x2h94__p1h:2H5h;2H0h<2H1h=2H2h>2H3h?2H4h@2_HhA1ap;1p;3p;2p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p10137p4p710R1p8P0p1002lp4p710p8P0p1003MR2p4p710p8P0P2p4p7210p8p1003jp4p710R2p1004HR0p4p710R3p8P2P0p4p7210R0p8p1004ap4p70R4P1p8P4p1005Xp4p710R1p8P4p10064p4p710p8P4p1006Rp4p7210p8P4p1006op4p710R5p8P4p1007MR6p4p710p8P4p1007fR7p4p710p8P4p1008=R8p4p710p8P4p1008YR9p4p710p8P4p10096p4p710p8P4p1009OR:p4p710p8P4P:p4p7210p8P4p1009lR:p4p710R;p8P4p100:@p4p710p8P4p100:\p4p710p8p100;8R4p4p73101R<p100;RR=p4p73110p8P<p100;kR>p4p73110p8P<p100<Gp4p710p8P<p100<ZR?p4p7201p8P<p100<lp4p7201p8P<P:p4p73110p8P<p100=>R:p4p73110p8P<p100=RR@p4p73110p8P<p100=lp4p7201p8P4p4p710R<P=p4p710p8P<P>p4p710p8P<P3p8P<P0p8P<P;p8P<P:p4p710p8P<P@p4p710p8p100>?R@p4p710R<P2p8P<P3p8P<P0p8P<p100>Sp4p73110p8P@p4p741110R@P8p4p73101p8p100>ep4p710P1p8P9p4p7210P5p8p100?@p4p7<111111111110R9P1p8P9P5p8p100?bp4p7<111111111110R9P1p8P9P5p8P6p4p741110R6P4p4p7511100R5p8P5P6p8p100@Dp4p741110R6P4p4p76111100R5p8P5P6p8p100@\p4p741110R6P4p4p771111100R5p8P5P6p8P7p4p741110R7P4p4p7:1111111100R4p8P4P7p8P?p4p7200R?P@p8P@P?p8g00YYj12Tg00k<j1>Tg04NMj3mTg01FPj1lTg00Zaj1:Tg014Tj1\Tg00V5j20Tg00kZj2TTg00JJj3ITg00G<j21Tg01<hj2?Tg00D1R?j26Tg00Jdj1aTg00C6j1_Tg00W1j2OTg00Wmj1^Tg00XKj1]Tg00Y6j2JTg00\1j1[Tg00\Sj2ZTg00KDj2YTg00]5j2XTg00]aj3WTg00^@j4VTg00_2j1UTg00WOj4STg00Z>j3ETg01Djj2RTg00LSj4GTg01?@j1NTg01GNj2KTg01H7j3QTg01H`j2kTg01ILj3jTg00`Qj6iTg00L8j4MTg00U[R@j2gTg00HWj2fTg00[Fj4eTg00_mj7dTg00aYj8cTg01Ilj7hTg01QCj3bTf0R7#2#2p=F%27#2#2#2#2#2#2#2p=8%:7#:#:#:p=<%:7#:p=`%27#2#2#2p=Bf2R4f1R6/07'6p=Hf3R5/041067'gp=41667,64p=L1046/67,65p=D1046/67p=7f4R910541067'6'6p=5g00OHR1/f7p=91R17p=@P4g00b=R8g00b\R<P<g00c<R0P1P6g00eMP7Ceg00c\Fdp=3P5P8P<P<P0P4P6P7Gcp=;1146/07p=CP4P8P<P<P0P6P7Fhp==Ab167p=A1067,64,65p=Pp,2rcR3g00dhR2#2R:#2#F#8R;#>R>7m7%l3%:2R=#:#<#<#<RA#2#:#`RB#:#<#2#F#B#8#8#>%\3R3'0RC%:A#<#<#2#F#B#8#8#>RA7H3P?1T4>g00f4RD5I110>4RE114>RFP3PF%BB#8#>RB%2;R;#<#<#<#<#2#F#B#8#>RGP4C4PF%2;#FR;#>RH%:2#2#B#<#B#8#>RIP4C47LECD115>RE%>2RJ,0797D7RK119>RL%8;#8#8#8#8#8#>R;,?7RM,1BRN1?G7ROP9D5X31#9PKPL11HMRM1?I7RLP9D5X11#9'677397>5P61T9>=I1Df5RP,0>RQ11P>RRP3PRPBPGPPC4PRPHPIPPC47LQCDP?f6RQ,0>RP11Q>RRPRPBPGPQC4PRPHPIPQC47LP773f7RP11P>PKf8RP/1>RRPNPOPPD5X31#9PKPRPMPLPPD5X11#9'677357>P710>Pf9RR/1>RSPSPBPGPRC4P>PRPSPHPIPRC4CD773P?f:RR/1>RS/03PSPBPGPRC4P>PRPSPHPIPRC4CDf;RS11S>PKf<RS/1>RTPNPOPSD5X31#9PKPTPMPLPSD5X11#9'677357>P710T3f=RT/1>RUPBPGPTC4P>PTPUPHPIPTC4CDP?f>RT/1>RUPBPGPTC4PUPHPIPTC497>Tf?RT11T>PKf@RT/1>RUPNPOPTD5X31#9PKPUPMPLPTD5X11#9'677357>P7PUPBPGPTC4fARU11U>PHPIPUC457>fBRU,0>RV11U>RW/03RXPKfCRY/1>RZPNPOPYD5X31#9R[PKPZPMPLPYD5X11#9R\'6R]'6g00d<R^#aR_%_^R`1O16Ra%^1Rb%]1Rc%@>Rd1J12R253cRe%[<RfPeC;1Zc0RgP7P4g00NHRhg00NhRi'Y1X74=IhidAW1D6CVRib5b6b7X0110>710>6Rh[^01P7PYPRO2b4PXP]P_P`P11O14R]P6%U1RXCSPbPcAE12dRd1J1:53cR:PfP:C;PgPib5b6b7X01X81117>R:/06AC6>4[^01^81P7P3PYPQO3b4P[P\P@10WB10GUPKfDR\/1>R[PNPOP\D5X31#9P610ZBP1PKfERZ/1>RQPNPOPZD5X31ROPDP_P`PaPbPc%@BRN93cdPfPcPePf1R1DRR=3cR%@JRj93cRRk5=cRl%@;Rm,ARRn9E1N93cd%@GRo/AR=3c25=c5=cC;C;PgPib5b6b7X0110:B10DJRp97DDRqPF1?D;Rr,1B1?GDP4D5\h[^01P7PZP6PSO3b4CGW2P7O110GYP1POPJp-0ROg01MGRs#NRt#N#N,K11K1t1K1s5Q15Q1g01Mf'k=j^_R^P`P1PXP6P]CSR]PbPcPcP8P<P<P0P9Ei1J1=R=%@A53c5=cR9PfPcA3co2PfPcA3cd=R=PfA3cjj9=ckRk1AjmRm9E1N93cd1Aoj=3c25=c5=cC;C;C;PgPib5b6b7X01X81W9AH46ARA10G610F5RoAHpJJRpPE1?J;R;,1B1?GJP5D5[[[^01^81^9OP7PCP3PZPYP6PPO6b4CGW2P7O1n200100001021100011000P?PVPWPHPIPUC4PKP[PMPLP\D5X11#9P710>\PQPHPIPZC4P@fFR@?C>H10I@PKfHR@?C>MPLP@CPX11#9P7fGR@?C>HP1PKfIRK?C>MPLPKCPX11RLPDP_P`PaPbPc%@HRa93cdPfPcPePfAE1an93cd%@IRn/AR=3c25=c9=clC;C;PgPib5b6b7X0110:HPqPF11Hr1?IDP4D5\h[^01P7PKP6PTO3b4CGW:P7O110I@P1PLPJP^P`P]PbPcP9PfPcA3cn2PfPcP=PfAE1am93cd1Anj=3c25=c9=ckC;C;C;PgPib5b6b7X01X81X9O10I6PpPE11H;1?IJP5D5\o[\A^01^81^9OP7PCP3PKP@P6PSO6b4CGW:P7O1n200100000021100011000W2W@P6P7O2n2001000000121000000CMCMCMW:W?P6P7O2n2001000010121000000W2W>P6P7O2n2011000010121000000W2W=P6P7O2n2011000010121000000W2W<P6P7O2n2011000010121000000b;W2XA1o"). Qed.

Section KW.
Variables (L : alayout) (sp lo a ms nsec nres nres' : Z).
Hypothesis WTF : wt_facts L sp lo a ms nsec nres nres'.
Let W' := List.filter nonempty (WT L sp a ms nsec nres nres').

Local Ltac inWT Hiv := unfold WT in Hiv; cbn [In] in Hiv;
  destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in *.
Local Ltac facts :=
  lazymatch goal with |- _ =>
  pose proof WTF as (ALO & CEIL & LO & AHI0 & ACE & AAL & MSM & MSP & (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d) & NS0 & NS1 & NS8 & NS9);
  pose proof (ao_t L ALO) as OT; pose proof (ao_ctx L ALO) as OC; pose proof (ao_res L ALO) as ORS; pose proof (ao_nodes L ALO) as ON;
  pose proof (ao_store L ALO) as OS; pose proof (ao_ptr L ALO) as OP; unfold aobj in OT, OC, ORS, ON, OS, OP;
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT OTs] & [jT OTi]); pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (OCi & _ & [kC OCs]);   (* [comment removed for export] *)
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (ONi & _ & [kN ONs]); pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (OSi & _ & [kS OSs]);
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & [kP OPs]); pose proof (ao_res_hi L ALO) as RHI;
  destruct (ablk_int _ _ AHI0) as [kA ABND]; pose proof (ablk_lin _ _ AHI0) as (AL1 & AL2 & _ & _); unfold AIMG_HI in AL1;   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res; pose proof (ad_nodes_res L ALO) as D_n_res; pose proof (ad_store_res L ALO) as D_s_res;
  pose proof (ad_ptr_res L ALO) as D_p_res; pose proof (ad_t_ctx L ALO) as D_t_c; pose proof (ad_t_nodes L ALO) as D_t_n;
  pose proof (ad_t_store L ALO) as D_t_s; pose proof (ad_t_ptr L ALO) as D_t_p; pose proof (ad_ctx_nodes L ALO) as D_c_n;
  pose proof (ad_ctx_store L ALO) as D_c_s; pose proof (ad_ctx_ptr L ALO) as D_c_p;
  unfold adisj in D_t_res, D_n_res, D_s_res, D_p_res, D_t_c, D_t_n, D_t_s, D_t_p, D_c_n, D_c_s, D_c_p
  end.

Lemma WT_shad : 0x800b9e00 <= shad a /\ shad a + ms / 8 = shad (a + ms) /\ shad (a + ms) <= 0x10007fef8000      (* [comment removed for export] *)
                /\ (forall x, x < a -> shad x + 1 <= shad a) /\ (forall x, a + ms <= x -> shad (a + ms) <= shad x).
Proof.
  facts. rewrite !shad_div. unfold ASHOFF in *. split; [clear -AL1; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]|].
  split; [clear -AAL MSM; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]|]. split; [clear -ACE; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]|].
  split; intros x Hx; rewrite shad_div; unfold ASHOFF; [clear -Hx AAL| clear -Hx]; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
Qed.

Lemma KT_X : forall A k, 0 <= k ->
  (forall iv, In iv (WT L sp a ms nsec nres nres') -> fst iv < snd iv -> A + k <= fst iv \/ snd iv <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k Hk H. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros iv Hiv.
  apply List.filter_In in Hiv. destruct Hiv as [Hiv NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV. exact (H iv Hiv NEV).
Qed.

Lemma KT_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= AIMG_HI ->      (* [comment removed for export] *)
  (A + k <= AINSTANCE + 112 \/ AINSTANCE + 720 <= A) -> (A + k <= 0x18c1c8 \/ 0x5dc210 <= A) -> disjoint_from W' A k.
Proof.
  facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  intros A k H1 H2 H3 H4 H5. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H1 H2 H3 H4 H5 NEV CEIL LO OT OP AL1 SA1 ON OS NS0 NS9 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
Qed.

Lemma KT_obj : forall A k, (A + k <= 65536 \/ 6352896 <= A) -> (A + k <= 2147446784 \/ 17594333495296 <= A) -> 0 <= k -> A + k <= ATOP ->      (* [comment removed for export] *)
  (A + k <= al_t L + 2800 \/ al_t L + 3169 <= A) -> (A + k <= al_ptr_array L \/ al_ptr_array L + 8388608 <= A) ->
  (A + k <= a \/ a + ms <= A) -> (A + k <= al_nodes L \/ al_nodes L + 1048576 <= A) -> (A + k <= al_store L \/ al_store L + 8388608 <= A) ->
  disjoint_from W' A k.
Proof.
  facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  intros A k H0 H1 H2 H3 H4 H5 H6 H7 H8. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H0 H1 H2 H3 H4 H5 H6 H7 H8 NEV CEIL LO NS0 NS1 NS8 NS9 SA1 SA2 SA3; lia.
Qed.

Lemma KT_shad : forall A k, 2147446784 <= A -> 0 <= k -> A + k <= 17594333495296 ->      (* [comment removed for export] *)
  (A + k <= shad a \/ shad (a + ms) <= A) -> disjoint_from W' A k.
Proof.
  facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  intros A k H1 H2 H3 H4. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H1 H2 H3 H4 NEV CEIL LO OT OP ABND ON OS SA2 NS0 NS1 NS8 NS9 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
Qed.

(* [comment removed for export] *)

Lemma KT_t : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 2800 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 OT D_t_p C_t D_t_n D_t_s OTs OTi; lia. Qed.   (* [comment removed for export] *)

Lemma KT_ctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 OC OT D_t_c D_c_p C_c D_c_n D_c_s OTs OTi OCs OCi; lia. Qed.

Lemma KT_res : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 ORS RHI OT D_t_res D_p_res C_r D_n_res D_s_res OTs OTi; lia. Qed.   (* [comment removed for export] *)

Lemma KT_res_geo : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                   /\ shad (al_res L + 137439023104) <= 0x10007fef8000      (* [comment removed for export] *)
                   /\ (shad (al_res L + 137439023104) <= shad a \/ shad (a + ms) <= shad (al_res L)).
Proof. facts. rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI C_r AAL. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. Qed.

Lemma KT_res_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k.
Proof. pose proof KT_res_geo as (SR1 & SR2 & SR3 & SR4). intros A k H1 H2 H3. apply KT_shad; clear -H1 H2 H3 SR1 SR3 SR4; lia. Qed.

(* [comment removed for export] *)
Lemma KT_rt : forall m m', munch W' m m' -> wmono bsegs m m' -> arep_rt L m -> arep_rt L m'.
Proof.
  intros m m' MU WM RT. eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
  repeat (apply Forall_cons; [cbn [fst snd]; first [apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia | apply KT_ctx; clear; lia] |]). apply Forall_nil.
Qed.
Lemma KT_rt2 : forall m m', munch W' m m' -> wmono bsegs m m' -> arep_rt2 m -> arep_rt2 m'.
Proof. intros m m' MU WM RT2. eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia. Qed.
Lemma KT_rt3 : forall m m', munch W' m m' -> wmono bsegs m m' -> arep_rt3 m -> arep_rt3 m'.
Proof.
  intros m m' MU WM RT3. eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]. unfold rt3_hulls.
  repeat (apply Forall_cons; [cbn [fst snd]; apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia |]). apply Forall_nil.
Qed.
Lemma KT_relro : forall m m', munch W' m m' -> arelro m -> arelro m'.
Proof. intros m m' MU HRO. eapply arelro_frame; [exact MU | exact HRO | apply KT_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AINSTANCE; lia]. Qed.
End KW.

Section Store.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Let AHS : aholes := AH DI AQ ASEC_of AFK.
Hypothesis HL : ahole_laws AHS.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem store_sec : forall (L : alayout) (RNG RNG' : footprint) (sp lo : Z) (m m' : amem) (st : astate) (X : aconc) (LB : list ablock)
    (n a nres' id : Z) (sj' : list word) (RESV : list (Z * Z)),
  let nsec := a_nsec st in let nres := a_nres st in let PA := al_ptr_array L in let ms := sec_map_size n in
  let UB := a + 6144 in let t := al_t L in
  alayout_ok L -> arng L RNG st -> AREP AHS L st X m -> ablocks L st X LB -> AFK L LB m ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  sfresh RESV st n a = true -> aresv_ok L RESV ->
  ATOP <= lo -> lo <= sp - 4096 -> sp <= 2^47 ->
  fp_le RNG RNG' -> rng RNG' a ms -> rng RNG' (shad a) (ms / 8) ->
  ((nsec <> nres /\ nres' = nres)
   \/ (nsec = nres /\ nres' = nres + 16384
       /\ rw_cells bsegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])) ->
  nres' <= 1048576 -> rng RNG' PA (8 * nres') ->
  munch (WT L sp a ms nsec nres nres') m m' -> wmono bsegs m m' ->
  (* [comment removed for export] *)
  u64arr bsegs m' (t + 2800) sj' -> length sj' = 46%nat -> rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m' (AINSTANCE + 112) [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))] ->
  rw_cells bsegs m' (AINSTANCE + 128) [C1 (Z_to_bv 8 0)] -> junk_at m' (AINSTANCE + 136) 32 -> junk_at m' (AINSTANCE + 168) 512 ->
  rw_cells bsegs m' (AINSTANCE + 680) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m' (AINSTANCE + 704) 16 ->
  rw_cells bsegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)] ->
  rw_cells bsegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)] ->
  junk_at m' (a + 32) (4096 - 32) ->
  rw_cells bsegs m' (a + 4096) [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))] ->
  junk_at m' (a + 4096 + 16) (2048 - 32) ->
  rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 < id < 2^31 ->
  junk_at m' UB (ms - 6144) ->
  fill_at m' (shad a) 768 0xfa ->
  rw_cells bsegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
  fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa ->
  ADEPOT DI L m' ->
     aheap_pres CI LB sp m m'
  /\ AHEAP_P AHS L RNG' (st_sec st nres' a ms n) (HB (a_next st) UB n :: LB) m'.
Proof.
  intros until RESV. cbv zeta.
  intros ALO ARNG AR BL HFK N PRIM FRSH ROK CEIL LO SP47 FPLE RA RSA NR' NRB RPA' MU0 WM
         STATS LSJ UNW I112 I128 J136 J168 I680 J704 SLOT HDR PGJ MAG LCJ AHD IDR USR SHF SHU SHT DEP.
  set (ms := sec_map_size n) in *.
  pose proof (valid_geo L RESV st n a N PRIM FRSH ROK) as (AAL & AHI0 & ACE & MSP & _). fold ms in ACE, MSP.
  pose proof (valid_clear L RESV st n a N PRIM FRSH ROK) as VC. fold ms in VC.
  pose proof (valid_hulls L RESV st n a N PRIM FRSH ROK) as VH. fold ms in VH.
  pose proof (valid_chunks L RESV st n a N PRIM FRSH ROK) as VK. fold ms in VK.
  pose proof (valid_wf1 L RESV st n a N PRIM FRSH ROK) as VW. fold ms in VW.
  pose proof (sec_facts n N PRIM) as (NB & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & MSB). fold ms in MSR, MSM, MSB.
  destruct VC as (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d).
  unfold K_HIGH_MEM in AHI0.
  pose proof (munch_filter_nonempty _ m m' MU0) as MU. clear MU0. set (W' := List.filter nonempty (WT L sp a ms (a_nsec st) (a_nres st) nres')) in *.
  assert (NE : Forall (fun iv => fst iv < snd iv) W') by (apply nonempty_filter).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_fake L ALO) as OFK. pose proof (ao_ptr L ALO) as OP. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in OT, OC, ORS, ON, OS, OFK, OP, OD. pose proof (ao_space L ALO) as RSP.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT OTs] & [jT OTi]). pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (OCi & _ & [kC OCs]).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (ONi & _ & [kN ONs]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (OSi & _ & [kS OSs]).
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & [kP OPs]). pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & [kF OFKs]).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & [kD ODs] & [jD ODi]). pose proof (ao_res_hi L ALO) as RHI.
  destruct (ablk_int _ _ AHI0) as [kA ABND]. pose proof (ablk_lin _ _ AHI0) as (AL1 & AL2 & _ & _). unfold AIMG_HI in AL1.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_ptr_res L ALO) as D_p_res. pose proof (ad_t_ctx L ALO) as D_t_c.
  pose proof (ad_t_nodes L ALO) as D_t_n. pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_ptr L ALO) as D_t_p.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s. pose proof (ad_ctx_fake L ALO) as D_c_f. pose proof (ad_ctx_ptr L ALO) as D_c_p.
  pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_fake L ALO) as D_s_f. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p.
  pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d. pose proof (ad_fake_dtls L ALO) as D_f_d.
  unfold adisj in D_t_res, D_c_res, D_n_res, D_s_res, D_f_res, D_p_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_p, D_c_n, D_c_s, D_c_f, D_c_p,
                   D_n_f, D_n_p, D_s_f, D_s_p, D_f_p, D_d_res, D_t_d, D_d_p, D_n_d, D_s_d, D_f_d.
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof HS as HS0. unfold AHS, AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  pose proof HS0 as (WFS & ARR & INST2 & PZ & SHZ). pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  assert (NSR : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ 8 * nres' <= 8388608 /\ a_nres st <= nres').
  { destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB NRB WR; lia. }
  destruct NSR as (NS0 & NS1 & NS8 & NS9).
  assert (WTF : wt_facts L sp lo a ms (a_nsec st) (a_nres st) nres').
  { unfold wt_facts. repeat lazymatch goal with |- _ /\ _ => split end; try assumption.
    - unfold sec_clear. repeat (split; [assumption|]). assumption.
    - clear -WB; lia. }
  pose proof (WT_shad L sp lo a ms _ _ _ WTF) as (SA1 & SA2 & SA3 & SAlt & SAge).
  pose proof (KT_X L sp a ms (a_nsec st) (a_nres st) nres') as KX. pose proof (KT_img L sp lo a ms _ _ _ WTF) as Kimg.
  pose proof (KT_obj L sp lo a ms _ _ _ WTF) as Kobj. pose proof (KT_shad L sp lo a ms _ _ _ WTF) as Kshad.
pose proof (KT_t L sp lo a ms _ _ _ WTF) as Kt.
  pose proof (KT_ctx L sp lo a ms _ _ _ WTF) as Kctx. pose proof (KT_res L sp lo a ms _ _ _ WTF) as Kres.
  pose proof (KT_res_sh L sp lo a ms _ _ _ WTF) as Kres_sh. pose proof (KT_res_geo L sp lo a ms _ _ _ WTF) as (SR1 & SR2 & SR3 & SR4).
  fold W' in KX, Kimg, Kobj, Kshad, Kt, Kctx, Kres, Kres_sh.
  Local Ltac inWT Hiv := unfold WT in Hiv; cbn [In] in Hiv;
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in *.
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  pose proof (st_sec_fields st nres' a ms n) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  set (st2 := st_sec st nres' a ms n) in *.
  assert (AR' : AREP AHS L st2 X m').
  { split; [apply awf_sec; exact WF|].
    split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
             repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
    split. {
      destruct INST as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold ainstance. subst st2. rewrite E3, E4.
      split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I3| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I4| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [exact I112|].
      split; [pose proof I680 as M4; rw_split M4 1%nat M0 M3; exact M0|].
      split; [eapply cells_frame; [exact I7| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I8| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      eapply cells_frame; [exact I9| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]. }
    split. {
      destruct THR as (T0 & T40 & CACHES & CSTATS & _ & _). unfold athread.
      split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
      split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
      split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | subst st2; reflexivity | subst st2; reflexivity | reflexivity |].
               unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
      split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
      split; [exists sj'; split; [exact STATS| exact LSJ]| exact UNW]. }
    split. {
      intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
      destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
      pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
      assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                   /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
      { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
      destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
      split; [| split; [| split]].
      - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity |].
        apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
      - eapply afreearray_frame; [exact MU | exact WM | exact FARR | subst st2; reflexivity | subst st2; reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
        + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
        + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
          rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). apply shad_mono.
          unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
      - eapply (aslots_update L W' m m' MU WM st st2 X X c (-1)); [exact SLOTS | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
        + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
          split; [reflexivity|]. split.
          * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
          * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
            apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
            split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
        + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
      - eapply (aslot_shadow_update L W' m m' MU WM st st2 X X c (-1)); [exact SHADOW | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
        + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
          pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
          split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | rewrite shlen_div; clear -QS QS16; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ] |].
          rewrite <- shad_add_shlen by (clear -AL; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
        + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
          rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
          apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
    split. {
      eapply (hq_frame _ HL L st st2 X X m m' W'); [exact HQ | exact MU | exact WM | |].
      - unfold quar_untouched. apply Forall_forall. intros iv Hin.
        unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV.
        inWT Hin. all: unfold AINSTANCE in *.
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS C_t D_t_p D_t_n D_t_s NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: intros b Hb; destruct (BB b Hb) as [B1 B2]; destruct (xb_st b); [exact I| |];
          clear -NEV B1 B2 CEIL LO OT OP ORS AHI0 SA1 SA2 SA3 SR1 ON OS D_t_res D_p_res C_r D_n_res D_s_res NS0 NS1 NS8 NS9 WB ABND AL1 RHI OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - unfold quar_same. subst st2. rewrite E9, E10, E11, E12, E1. repeat (split; [reflexivity|]).
        split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
    split. {
      unfold AHS, AH. cbn [ah_sec]. subst st2.
      eapply (asec_append L W' m m' MU WM st X nres' a n id WF HS0 N PRIM VW VK NR' NRB).
      - intros ch Hin. destruct (asec_wf_all L st _ ch WFS Hin) as (mb & ms' & n' & -> & W1c). cbn [sec_mb sec_ms].
        pose proof W1c as W0. cbn [sec_wf1] in W0. destruct W0 as (G1 & G2 & G3 & G4 & G5 & G6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
        pose proof (proj1 (Forall_forall _ _) VK _ Hin) as D. cbn [sec_mb sec_ms] in D.
        pose proof (sec_facts n' ltac:(clear -G5; lia) G6) as (_ & _ & _ & _ & _ & _ & _ & _ & MSM' & MSB'). rewrite <- G4 in MSM', MSB'.
        destruct (ablk_int _ _ G2) as [kB GB].
        assert (SHc : 0x800b9e00 <= shad mb /\ shad mb + ms' / 8 = shad (mb + ms') /\ shad (mb + ms') <= 0x10007fef8000
                      /\ (shad (mb + ms') <= shad a \/ shad (a + ms) <= shad mb)).
        { rewrite !shad_div. unfold ASHOFF, K_HIGH_MEM in *. clear -G1 GB G3 MSM' D AAL MSM. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
        destruct SHc as (SC1 & SC2 & SC3 & SC4). unfold K_HIGH_MEM in *.
        split; intros A k H1 H2 H3.
        + apply Kobj; clear -H1 H2 H3 GB G3 Ct Cp Cn Cs D; lia.
        + apply Kshad; clear -H1 H2 H3 SC1 SC2 SC3 SC4; lia.
      - intros POS. apply KX; [clear -POS; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
          clear -POS NEV CEIL LO OT OP AHI0 ON OS SA2 SA3 D_t_p C_p D_n_p D_s_p NS0 NS1 NS8 NS9 WB ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - intros LT. apply KX; [clear -LT NS0; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
          clear -LT NEV CEIL LO OT OP AHI0 ON OS SA2 SA3 D_t_p C_p D_n_p D_s_p NS0 NS1 NS8 NS9 WB ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia.
      - replace (shlen K_REGION) with 536870912 by reflexivity.
        apply Kres_sh; [apply shad_mono; clear -RSP; lia| clear; lia|].
        rewrite !shad_div. clear -RSP. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
      - intros x Hx Hxa. unfold K_HIGH_MEM, KLS in Hx. unfold AIMG_HI in Hx.
        assert (SX : 2147446784 <= shad x /\ shad x + 1 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -Hx; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
        apply Kshad; [clear -SX; lia| clear; lia| clear -SX; lia|].
        destruct Hxa as [Hxa|Hxa]; [left; apply SAlt; exact Hxa| right; apply SAge; exact Hxa].
      - exact I128. - exact J136. - exact J168. - exact I680. - exact J704. - exact SLOT. - exact HDR. - exact PGJ. - exact MAG. - exact LCJ.
      - exact AHD. - exact IDR. - exact USR. - exact SHF. - exact SHU. - exact SHT. }
    split; [exact DEP|].
    split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AINSTANCE; lia]|].
    split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia|].
    split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia |]); apply Forall_nil].
    intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | subst st2; reflexivity | subst st2; reflexivity | |].
    - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
      rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
      apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
    - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
      rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
      apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }
  assert (SHFK : 0x800b9e00 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 = shad (al_fake L + 11571200)
                 /\ shad (al_fake L + 11571200) <= 0x10007fef8000
                 /\ (shad (a + ms) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad a)).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFK C_f AAL OFKs OFKi. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
  destruct SHFK as (SF1 & SF2 & SF3 & SF4).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  split.
  -
    intros x Hx CL. split; [| intros Hw; apply WM; exact Hw]. apply MU. rewrite wa_unsigned by exact Hx.
    destruct CL as [STa | [CIa | [BLK | SH]]].
    + eapply (disjoint_outside W' x 1); [| clear; lia]. apply KX; [clear; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
        clear -STa NEV CEIL LO OT OP AHI0 ACE ON OS SA2 SA3 NS0 NS1 NS8 NS9 WB SP47 ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
    + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Kimg x 1); unfold AIMG_HI, AINSTANCE in *; clear -R Q1 Q2 Q3 Q4; lia | clear; lia].
    + destruct BLK as (b & Hb & R). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      * destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        -- destruct (BB xb Hxb) as [Bb1 Bb2].
           pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
           eapply disjoint_outside; [eapply (Kres x 1) | clear; lia]; clear -R Bb1 Bb2 FIT; lia.
        --
           assert (Hin : In (CSec mb0 ms0 n') (sec_chunks_of st)).
           { unfold sec_chunks_of, achunks. apply List.filter_In. split; [| reflexivity]. apply in_app_iff. left.
             apply in_map_iff. exists (p, CSec mb0 ms0 n'). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Lp. }
           pose proof (proj1 (Forall_forall _ _) VK _ Hin) as D. cbn [sec_mb sec_ms] in D.
           cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
           pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SFc. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
           destruct (ablk_int _ _ Gs2) as [kB GB].
           eapply disjoint_outside; [eapply (Kobj x 1) | clear; lia]; clear -R GB Gs3 Gs4 Gs5 SFc Ct Cp Cn Cs D; lia.
      * destruct (FKD cls A n' Hb) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Kobj x 1) | clear; lia]; clear -R K1 K3 OFK D_t_f D_f_p C_f D_n_f D_s_f OFKs OFKi; lia.
    + destruct SH as (x' & Hx' & ->).
      destruct Hx' as [STa | [CIa | FK]].
      * assert (SX : shad (a + ms) <= shad x' /\ shad x' + 1 <= 17594333495296).
        { split; [apply SAge; atop_facts; clear -STa ACE; lia|]. rewrite shad_div. unfold ASHOFF. clear -STa. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
        eapply disjoint_outside; [eapply (Kshad (shad x') 1); clear -SX SA1 SA2 MSB; lia | clear; lia].
      * destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
        assert (SX : 2147446784 <= shad x' /\ shad x' + 1 <= 0x800b9e00) by (rewrite shad_div; unfold ASHOFF, AIMG_HI in *; clear -R Q1 Q3; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
        eapply disjoint_outside; [eapply (Kshad (shad x') 1); clear -SX SA1; lia | clear; lia].
      * destruct FK as (cls & FA & sz & Hin & R). destruct (FKD cls FA sz Hin) as (K1 & K2 & K3).
        assert (SX : shad (al_fake L) <= shad x' /\ shad x' + 1 <= shad (al_fake L + 11571200)).
        { rewrite !shad_div. clear -R K1 K3 OFK OFKs OFKi. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
        eapply disjoint_outside; [eapply (Kshad (shad x') 1) | clear; lia]; clear -SX SF1 SF3 SF4; lia.
  -
    split; [exact ALO|].
    split; [eapply (arng_sec L RNG RNG' st X); [exact WF| exact ARNG| exact FPLE| exact RA| exact RSA| exact RPA']|].
    split; [exists X; split; [exact AR'| replace (a + 6144) with (a + SEC_UOFF) by reflexivity; apply ablocks_sec; [exact WF| exact BL| exact VW]]|].
    unfold AHS, AH. cbn [ah_fake].
    eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM |] |].
    + unfold fake_untouched. apply Forall_forall. intros iv Hin.
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV.
      inWT Hin. all: unfold AINSTANCE in *.
      all: clear -NEV CEIL LO OT OP OFK OD AHI0 ACE SA1 SA2 SA3 SF1 SF2 SF3 SF4 ON OS D_t_f D_t_d D_f_p D_d_p C_f C_d D_n_f D_s_f D_n_d D_s_d NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi OFKs OFKi ODs ODi.
      all: first [ lazymatch goal with
                   | |- context [al_t _] => clear D_f_p D_d_p C_f C_d D_n_f D_s_f D_n_d D_s_d
                   | |- context [al_ptr_array _] => clear D_t_f D_t_d C_f C_d D_n_f D_s_f D_n_d D_s_d
                   | |- context [al_nodes _] => clear D_t_f D_t_d D_f_p D_d_p C_f C_d D_s_f D_s_d
                   | |- context [al_store _] => clear D_t_f D_t_d D_f_p D_d_p C_f C_d D_n_f D_n_d
                   | |- _ => clear D_t_f D_t_d D_f_p D_d_p D_n_f D_s_f D_n_d D_s_d
                   end; repeat (split; [lia|]); lia
                 | repeat (split; [lia|]); lia ].
    + intros c F n'. split; [intros H; cbn [In] in H; destruct H as [H|H]; [discriminate H| exact H]| intros H; cbn [In]; right; exact H].
Qed.
End Store.
End CANSEC1.
