(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import MM_syscalls WStr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg AProto ABase AKit AKit2 AKitQ AKitR ABytes AQConst AModelFacts ARep ARepKit ARepFrame ALayout AHeapP ASec
     ASecFacts ARepQ ARepQP ARepQR AFreeRep AFreeGeo AFreeRead ARecRep ARepQD ARefillP AFrameD ARepExt RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_apopulate F_agetfrom F_arefill F_amaybe F_areturn F_acdrain F_acdealloc F_arecyc1
     ASecRecycle_iface ARecyc1P ACdeallocP ARecGeo.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_adorec () := "C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI46Stdlib7Sorting;Permutation;Permutation00I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3appI59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC46Stdlib7Sorting;Permutation?Permutation_mapC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base6LookupI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeC35stdpp4base;RelDecisionI35stdpp4gmap4gmap00I35stdpp9countable9Countable00C35stdpp4base4fmapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List7map_appC46Stdlib5Lists4List:firstn_nilC35stdpp4gmap:gmap_emptyI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init9Datatypes4prod00c59OSSVerify5KrLib5AsanW8F_adorec4ehdrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib5AsanW5ARepQ5qhdrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ4qhdrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List7combineC46Stdlib5Lists4List3revC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib5Lists4List:filter_appc59OSSVerify5KrLib5AsanW8F_adorec5esecsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC59OSSVerify5KrLib5AsanW6AHeapP6is_secC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~K46Stdlib7Sorting;Permutation;Permutation01K46Stdlib7Sorting;Permutation;Permutation02K46Stdlib7Sorting;Permutation;Permutation03C46Stdlib7Sorting;Permutation@Permutation_reflC46Stdlib7Sorting;PermutationAPermutation_transC46Stdlib7Sorting;Permutation?Permutation_indC59OSSVerify5KrLib5AsanW6ARepQR<qcoupled_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQR6qr_tmpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQR8qr_pendbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQR7qr_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQD@qcoupled_rec_popC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQD6qr_popC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQR6qr_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQR7qr_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ9qentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQR:qr_entriesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQR9qr_bslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep6x_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7xb_slotC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00c59OSSVerify5KrLib5AsanW8F_adorec7qr_poprC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib5AsanW5ARepQ8qentriesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ5qb_ksC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_revC46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib7Sorting;PermutationDPermutation_app_headC59OSSVerify5KrLib5AsanW6ARepQR5qr_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ7qb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQR8qr_qpendC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW6ARepQR6qrconc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQDAqcoupled_rec_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ9qprim_idsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C47Corelib4Init5Logic3iffI59OSSVerify5KrLib5AsanW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4ARep5aconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW6ARepQR6qrconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4ARep6bstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW4ARep6bstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW4ARep6bstate02C1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationDPermutation_app_commc59OSSVerify5KrLib5AsanW8F_adorec:esecs_permC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationDPermutation_app_tailC46Stdlib5Lists4List9app_nil_rc59OSSVerify5KrLib5AsanW8F_adorec9esecs_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_adorec8inflightC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=cache_deallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl>recycle_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:do_recycleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=large_deallocC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5AsanW6ARepQR<aquar_constsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7AQConst9aq_tcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ7aqcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQD5qnumRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQR8qnum_tmpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ6qaddrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ<abatch_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ;abatches_toC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_invC46Stdlib5Lists4List?Forall_inv_tailC59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ8abatchesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ6aintalC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_adorecAqcoupled_rec_poprC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib5AsanW6ARepQD4AQdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQR;aquar_mutexC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ6qfirstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7AQConst9AQ_GCACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQDEqcoupled_rec_drop_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQD7qr_dropC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP9quar_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQDAqcoupled_rec_sameC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I59OSSVerify5KrLib5AsanW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5AsanW6ARepQD<In_qr_bslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQDGqcoupled_rec_bslot_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ;abatch_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ARecGeo=busy_slot_geoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5AsanW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8xb_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout6al_resC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8K_REGIONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQP@size_of_class_24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List9filter_InC59OSSVerify5KrLib4Spec8AsanCtrl7achunksC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listC46Stdlib5Lists4List8flat_mapC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp8fin_mapsBmap_to_list_deleteC35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC46Stdlib7Sorting;Permutation>Permutation_inC46Stdlib5Lists4List9in_or_appC59OSSVerify5KrLib5AsanW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC46Stdlib5Lists4List7existsbC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~K47Corelib4Init6Specif7sumbool01K47Corelib4Init6Specif7sumbool02C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init6Specif;sumbool_recC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec8AsanCtrl:achunk_recC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalI47Corelib4Init5Logic5False00C47Corelib5Lists7ListDef3seqI47Corelib4Init5Peano2le00C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C46Stdlib5Lists4List:in_map_iffC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8max_specC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphK47Corelib4Init5Logic2ex01C46Stdlib5Lists4List4inclC46Stdlib5Lists4ListANoDup_incl_lengthC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:length_seqK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib5Lists4List8map_consC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith4Znat5Z2Nat2idc59OSSVerify5KrLib5AsanW8F_adorec?nodup_range_lenC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appK46Stdlib9micromega7EnvRing5PExpr07I46Stdlib5Lists4List6Exists00K59OSSVerify5KrLib5AsanW4ARep6aholes01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep4AREPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7athreadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase6ablock00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout7ao_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout4aobjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout7ao_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib5AsanW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrame9shlen_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP>quar_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ARepQD;AQdr_frameDC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanWAASecRecycle_iface=srec_holes_ok01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_adorec5drinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP4arngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_adorec3csxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA9rng_fp_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ARecGeo5cpresC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_adorec7st_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP6sec_mbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_adorec<live_sec_in'C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>NoDup_remove_2C59OSSVerify5KrLib5AsanW6AHeapP6sec_msC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP7sec_wf1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_adorec@live_vs_inflightC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_adorec>achunk_eq_dec'C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib5AsanW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<sec_map_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP9sec_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecFacts9sec_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;needed_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib5AsanW6AHeapP8SEC_UOFFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_adorec?map_fst_combineC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List5splitC59OSSVerify5KrLib5AsanW5ARepQ5qlastC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4lastc59OSSVerify5KrLib5AsanW8F_adorec7qr_doneC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib5AsanW8F_adorec9AREP_reqsC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition adorec_entry : Z := 0x33804.
Definition adorec_lout : Z := 0x3387c.     (* [comment removed for export] *)
Definition adorec_lin : Z := 0x338bc.      (* [comment removed for export] *)
Definition adorec_after : Z := 0x338d4.    (* [comment removed for export] *)
Definition adorec_chk : Z := 0x33900.      (* [comment removed for export] *)
End CANSEC1.
Notation DOREC_FRAME := 112 (only parsing).
Notation DOREC_STACK := 1136 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition ehdr (L : alayout) (e : achunk * Z) : word := Z_to_bv 64 (qhdr L (fst e) (snd e)).

Lemma qhdrs_rev_combine : forall L chs ks, length ks = length chs ->
  map (Z_to_bv 64) (qhdrs L chs ks) = map (ehdr L) (rev (combine chs ks)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "p'0h03LENh12ksh23chsh31li001lh44__x1h54__x2h61kh73ks0h81xh92IHh:1Lh;4LEN0h<7__arithh=4__ffh>8__varmaph?5__with@2chhA4cstrhB5cstr0hC1yi011zp;1p;2p;4p;3p;8p;6p;5p;<p;7p-1R0p10000p4p710R1p8P0g000GR2p4p710p8P0p1000cp4p710p8P0P2p4p7210p8P0p1001Np4p710p8P0p1001oR3p4p710R4p8P0P3p4p7210p8P0g002LR0p4p710p8p1002iR3p4p710g003`R5p4p710R6p8P3p4p7210P6p8p1004>p4p710R3P6p8p1004[p4p710P6p8p1005Pp4p70R7P1p8P7p1006Gp4p710R1p8P7P3p8P7P6p8P7P4p8P7p1006cR4p4p710p8P7p1007<R3p4p710p8P7p1007\p4p710p8P7p1008IR8p4p710p8P7p1008`R9p4p710p8P7p1009<p4p710p8P7p1009UR7p4p710R:p8p1009iR;p4p73101R<p100:CR=p4p73110p8P<p100:\R>p4p73110p8P<p100;8p4p710p8P<p100;KR?p4p7201p8P<p100;]p4p7201p8P<P7p4p73110p8P<p100;oR7p4p73110p8P<p100<CR@p4p73110p8P<p100<]p4p7201p8P;p4p710R<P=p4p710p8P<P>p4p710p8P<p100=0R>p4p710R=p8P<P>p4p7210R>p8P<P:p8P<P7p4p710p8P<P@p4p710p8p100=IR@p4p710R<p100=]p4p710p8P<P=p8P<P>p8P<p100>;p4p73110p8P@p4p741110R@P9p4p73101p8p100>Mp4p7210P6p8g00?9R9p4p7210P6p8p100?Up4p710R<P1p8P<P6p8P4p4p741110R4P;p4p7511100R6p8P6P4p8p100@4p4p741110R4P;p4p76111100R6p8P6P4p8P3p4p741110R3P;p4p771111100R4p8P4P3p8P8p4p741110R8P;p4p7:1111111100R;p8P;P8p8P?p4p7200R?P@p8P@P?p8g00@LR?j1@Tg00@lj1:Tg00AQj1gTg00Aoj1`Tg00BRj1\Tg00C8j2YTg00CXj19TP2j40Tg00DPj1<Tg00E0j2=Tg00EJj31Tg00Ejj3BTg00F`j3LTP0j38Tg00GUj4PTg00H5j32j1ITg00HOR0j16Tg00Hoj2XTg00IRj3WTg00IoR2j1ATg00JNj1VTg00Jlj2?Tg00KIj4TTg00L0j1DTg00LUj2ETg00M1j1STg00MOj2RTg00N0j2HTg00NYj3UTg00OBj3sTg00Okj2rTg00PWj2qTg00Q5j1pTg00QSj4oTg00R1j1nTg00ROj1iTg00S:j2OTg00S]j2hTg00T@j3NTg00Tcj4MTg00UNj1fTg00V0j8eTg00VTj2bTg00W6j2aTg00Wbj3cTg00XAj4dTg00Y3j4_TP5j6CTP9j5JTg00Y^j5^Tg00Z@j2QTg00Z`j4jTg00[<j2kTg00[Tl<lTg00\9l<mTg00\^j7ZTg00]BR9f0R5'Qp=;g00]`R@/Q5p=5g00^[R8f1R;;25p=3f2R3P@P9P;P5Cj'kp=4f6R4P9f5R6f4R<f3R1?B3;C0;25p=7P9P3P;P5C0p=>P1P3P;P5C0926<p=]P9P<P1AB3;5C0p=[P8P9P5P0P;P3P1P<P6P4f7R>f8R=M<lp=GP8P8P9P9P2P0P0P1g00_:P3P;P5M<mp=FP;g00_^R0g00`=R2P2g00`]R7P5g00a=FZp=Kg00a]%@@R:P@%@9RA%;5RB%5;'3RCg00bWRD#:RE#:#:#:#:#:#gRF#`RG#@RHPG%\FRFP<P3P;1Y@9RIPG%9<RJA4I3;RKC0F7[]1X2:P?P9%<@RL#5RM,3BPHPGPFP<PLP;PIPGPJA4IL;C0F7[P5%<9RJ#;RN/3M%<G,=HROPHPGPFP1PLPJPIPG%91A4ILJC0F7eW0A19;5#;RP/3MPOPHPGPFP>PLA193;RMPIPG%9>RQA4ILMC0F7eW0X1AX69P;P5O2n10110000020020101100X7APHPGPFP6P3P;PIPG%96PKC0F7\C^1AP?P9A1@<1R?#5,3BPHPGPFP>A1@6<R<P;PIPGPQA4I<;C0F7[P5A1@13#5,3NPOPHPGPFP4P?PJPIPG%94A4I?JC0F7eW0A1@>4#5,3PPHf:RP?B>;R?9>GFROALP=3=19JRN9>GF58GPHP5PIPGf;R<#9RQA4I=3RBP@P9f9RCP1CP%<IRK51IRL58IE]X3HPHPIPG%9PRRA4I>;RSC0RTPIPGPRP@P9P=P3CP=1IKRKC058GRUPGPFP<P=P3D[AL<C1=19J9>GFRJ58G=2H5X3HPHPTA8G5JPIPGPQPBC0PIPGPQPLC058G52HX3H1=HUPOP4P;%;;R4%5>RO'3%64RU%6ORL529%I8RQ%I9RB%6;%6552913;51X;53WXC8X88R8P4PU1=9URJPOPL1=9LRTM9G%A4RV%AORW'3%VDRX,?U1?LX529RYPQPBP8PV1?5XRVX89R8PUO1P8P4PUPJCFPWP8PLO1P8POPLPTCFM9GP5CTPY%;3RY#Dg00c<RT%6Y'E%5CRC#D%6C,ETg00cZRC%SD,R9g00dFRY#A,H95U91H9Y5s9g00de'r%<C31%@CP91q93P;%p9Co%n9%i9RCP0P2P2P7P91O9DRD1h9XR05N9g00eQRY1O9ERE=N90CM,KC%f2P9PDPYPECM,KCGe1bC7P5P3g00f8RCg00fXR7'=1a53=2C7dAc9T;Cdb=b>b?X49X591?;X929VA29;3[^49^59P5%5<#6%;6#6P1O3b<bBbAb;C_O2ECPIPGPRA8ISKC0PIPGPRPSPKDJECA89?N9>GFP9PGPFP?PNDJECPHPGPFPPA1@=>R=PMPIPGPRA4I=MC0F7eW0X1AX69P;P5O2n10110000020021101100X7AW9X2:X@@P5D^W2W:o"). Qed.

(* [comment removed for export] *)
Definition esecs (es : list (achunk * Z)) : list achunk := List.filter is_sec (map fst es).
Lemma esecs_app : forall a b, esecs (a ++ b) = esecs a ++ esecs b.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h01ah11bh21lp;2p;1p;4p;3p;5p;6g00C8j2;Tg00@Lj15Tg001oj2:Tg000Gj40Tg002Lj31Tg00H5j34Tg00g8j49Tg00?9j58Tg003`j67Tg00gWj12Tg00hPj36Tg00]`R0g00hkR1f0R236p=3g00]BR3,;0R4#5R5%50R6P4P01:03R3f1R7C0R8P4P0P3P2C0R9510%32P4P0P3f2C0#3%38510546X26P0P1P8P9C9P4P0P3A1472R9C0P4P0P3P7P2D8E7%29%27%22510546eX15W0o"). Qed.
Lemma esecs_cons_prim : forall c n k es, esecs ((CPrim c n, k) :: es) = esecs es.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h01ch12esh21kh31np;2p;1g00C8j23Tg00@Lj10Tg00gWj12Tg00E0j21Tg00]BR0g00]`R1/30#0%01f0#2'1W1X20X30W0o"). Qed.
Lemma esecs_cons_sec : forall mb ms n k es, esecs ((CSec mb ms n, k) :: es) = CSec mb ms n :: esecs es.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h02esh11kh22mbh32msh41np;2p;1p;3g00C8j25Tg00@Lj10Tg00icj32Tg00gWj11Tg00EJj34Tg00E0j23Tg00]BR0g00]`R1/50#0%01f4f3f232f0#1541'3W0X10X40X30W2o"). Qed.
Lemma esecs_perm : forall a b, Permutation a b -> Permutation (esecs a) (esecs b).
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "p'0h01bi001bh11lh21Ph31ah42l'h51xh63IHPh74IHP1h84IHP2h92P1h:2P2h;3l''h<1yp;2p;1p;3p;5p;4p;6p;9g00C8j2DTg00@Lj19Tg000cj35Tg001oj2:j3@Tg00j^j1<Tg00DPj1;Tg00hkR0j17Tg00kIj56Tg00EJj33Tg00l4j4CTg00l_j2BTg00mMj6ATg00n<l9=Tg00gWj18Tg000Gj4>Tg00hPj3?Tg00]`R1f2R2P1f1R3f0R4C>7?0p=1A5134p=0g00]BR0=@14p=4A3134p=21D10R5#9R6A5534R7P51:10R0=153R8A1504'0X06X36%<1%;59150R9/09eA1502R9/08f4R8#4R:#7g00f8R;P;P;%91R<P4f6R=#4R>f5R?9150R@'2P@n0100000020000P;P<P4A1508RA,2>PAn0100000020000'0P4P1%4?R?PAf3R>9150RBP3D6P3n0110000020000b0A358>9150A35829150'0eW6X27X46X16X55%42#7R7P;P;P;P<%4>R8#7RCP;P<P412:9P9n0100000020000RD,28PDn0100000020000P;P<P4P;P<PC1289P9n0100000020000RC,2:PCn0100000020000'0P4P7P;P;P;P<P412?BRC,2:PCn0100000020000P;P<P412:BPBn0100000020000R<,2?'0P4P1P:P8P9CCP1P:P9P91B19R:D6n0110000020000b0P7P;P;10<<P4P1P8P9P9P:D6P:n0110000020000b0n0110000020000b0A352493539150A353493529150'0eX16X<5X55A552310B9A55>210ABP1A150=R=P@PAP2P4EA10=AeW8W:W7W9X;6X46X16P2P3P4M9=%82%83'0eW2X06W3o"). Qed.

(* [comment removed for export] *)
Definition secsT (R : qrconc) : list achunk := esecs (qentries (map fst (qr_tmp R)) (map snd (qr_tmp R))).
Definition inflight (R : qrconc) : list achunk := secsT R ++ esecs (qr_pend R).
(* [comment removed for export] *)
Definition csx (st : astate) (R : qrconc) : list achunk := sec_chunks_of st ++ inflight R.

(* [comment removed for export] *)
Definition qr_popr (R : qrconc) (b : abatch) (q : qbatchc) (T : list (abatch * qbatchc)) : qrconc :=
  mkQR (qr_loc R) (qr_glob R) (qr_ia R) T [qb_slot q] (rev (combine (b_chunks b) (qb_ks q))) (qr_qpend R).

Lemma qcoupled_rec_popr : forall L st X R b q T,
  qcoupled_rec L st X R -> qr_tmp R = (b, q) :: T -> qr_pendb R = [] -> qr_pend R = [] ->
  qcoupled_rec L st X (qr_popr R b q T).
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h01bh11kh21ch31Hh42CPh53CP1h62EBh72EPh82ETh91Lh:3LN1h;3LN2h<1Rh=1Th>1Xh?2_Hh@1qhA2stp;2p;1p;4p;3p;;p;5p;7p;<g00C8j2STg00@Lj1ITg00nij4ETg00ogj1LTg00GUj4YTg00EJj3WTg00H5j35Tg010_j1NTg00DPj1TTg011Yj1MTg012Rl;]Tg013Tj41Tg014Lj1DTg015Dj1RTg016=j1=Tg0176j1FTg0180j1GTg018jj24Tg001Nj37Tg019fj1:Tg01:aj1;Tg01;Wj1`Tg01<Lj1_Tg01=Dj1^Tg01>;R0j22Tg00LUj2\Tg01>Vj4JTg01?Qj2PTg01?mj26Tg001oj2[Tg000Gj4>Tg01@fj2ZTg01ACj1nTg01B>j1mTg00Z`j4lTg00[<j2kTg002Lj30Tg01C4j2jTg01Caj4hTg01DNj5QTg01E@j1gTg01F7R1j1dTg01Foj1KTg01Gij7VTg000cj3HTg00l_j2cTg00E0j2eTg01Hcl<fTg00Z@j2UTg01Ifj1bTg01J`j3XTg01K7j2aTg01KQj2iTg01KjR2f0R3'Up=Ag01LdR4/U3p=Cg00^[f1R5;53p=@f2R6%b5%K330p=9g01M_R7?X53p=<1253,26p=3f3R8?X651a73'ip=81P65/23p=BA0253p=?P2g00]BR9P1P3C>p=Og00a]g01NVg01OQg01PH1S42R1#IR:f6R;f5R<f4R=P8CE%L=P4P2P8P6CY=W1555:%I9%N<%T9R:35g00]`R>/S9R?#I%M;%T?35f:R@f9RAf8RBf7RCP;P<P=P8P6P5P3M;]P@PAPBPCP;P<P=C1CEP3f;R=P@PAPBPCP;P<C1CEP0PAPBPCP;C1R;#D#A%R=#C'@%=;#A%F=#C'@%G@14=;R857?1S99RDA9D8;%:;R;P9P3P@PAPBPCC1#:f<R8#;,<3g01QBRE%`3RFg01R:35%_3RGg01S2559%^3=595RH33RI'2X07C8^19PDP9P9P5P3CYRJf=RKP=P@PAPBC1RL'4=9DL%;K,<3g01T295EFA59G6;3HRH'2X07C8^19^29g00c</\3X19RG=79;335B93B33PKP8P=P@PAPBPCCJCEP3%DL#A%RK#C'@P8P=P@PAC1RL#=#Af>RC#F#C'@%GK14CLRB57?A9DBL%:LRLP9P3PKP8P=P@C1R@#:RBf?R;#;,<3/2IX07C8^19PDPJf@R6PCPKP8P=C1RF'4=9DF%;6,<3RE/2HX07C8^19^29A79GL335B95BD33P0%=@#A%F;#C'@%GC14;@R057?A9D0@,PDP9P3%:F12EIX07C8^19PDPJfAREP;PCPKP8C1RF'4=9DF%;E,<3/2HX07C8^19^29A79GB339B9B33PEP6P;PCPKP8P=CJCEP3%=F#A%FE#C'@%GEfBRFP6P;PCPKC1RK'4R=57?A9D=K,PD%:KRKP9P3PEP6P;PCC1R=#:R8fCRB#;,<3/2IX07C8^19PDPJfDRJPFPEP6P;C1RI'4=9DI%;J,<3/2HX07C8^19^29A79GK335B933PJPBPBPFP=PEP6P;PCCJRFPAP<P5P?%RBR<%DERA'6%FBRJ%=ERK'6RGP1P41[42R7PCC>P1P21Z42RHPCC>RI'6R0P>P9%n6%m;ClR6,k?R>50?R@50?A0?06RL90?GP?PGP@PLP?P0P>P6P?P6P>1j?6ChDQDQDQPAPK%gER0PC%d;=W9:R:P>%KEREFVR>#DR;,6<%=>RL,6JP1P4P7%L>R@C>P1P2PHP@C>R@'6%M>50?50?50?PAPKP0PCP:P6PEFVRE#DR6,6<%=ER<,6JP1P4P7%LER7C>P1P2PHP7C>R7'6%ME50?50?50?5H?e14BF14B=5H?e1?KI,?A#O=09:,c91?L@,?;#O%N>5091?<7,?6#O%NE5095H9e%:F=H98e%ID%K='eM<fW?W;P5P3O2n2001000000121000000W3W:P5P3O2n2001000000121000000b3b5W7W6W8W4W=X@2X04W<W>WAW9o"). Qed.

Lemma inflight_popr : forall R b q T, qr_tmp R = (b, q) :: T -> qr_pend R = [] -> length (qb_ks q) = length (b_chunks b) ->
  Permutation (inflight (qr_popr R b q T)) (inflight R).
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h01lh12EPh22ETh31Hh43LENh51Rh61Th71bh81qp;2p;1p;3p;4p;5p;6p;7g00C8j2CTg00@Lj1?Tg00ogj1:Tg00EJj39Tg00H5j38Tg011Yj16Tg00DPj1<Tg01B>j14Tg00Z@j2@Tg01ACj17Tg001oj2FTg01@fj2ETg00gWj10Tg00[<j2=Tg00E0j2XTg01Tjj3WTg01C4j2VTg01Caj4TTg01U\j3STg01VZj5RTg00mMj6LTg01WLj2KTg003`j65Tg006Gj6ITg002Lj3ATg01Wjj2JTg014Lj1HTg016=j1GTg01E@j1MTg01F7j1NTg01Foj1OTg01Gij7PTg01>Vj4QTg01Xgj1BTg00GUj4UTg000Gj4DTg01?mj2[Tg00Z`j4ZTg000cj3YTg01LdR0g01KjR1f1R2f0R3CUp=;f5R4P0f4R5f3R6CDf2R7P1P2P3CD'[p=3g00]`R8g00]BR9P2P3CZp=>AA823p=1AY823p=2g01PH1C01R:#?R;%:61;72=9:358;1C89R<#?R=%65%<<R>38g00^[%46,@9%75,@838P;1;45=9:6R?P:1F01R@P5P:1E01RAP5E3#0RBf6RC#7%44'>RD,=<RE#0RF'1RGP:P@P3P:PAP3E3#0f7RH#6#0'1'2X0;P=P>P:P@1;C4=9:5R;P:PAP;E3#0%03'1,2GX0=%?8R=%74%45'>R;#0P:P@P6P:PAP6E3RI#0RJ'1%0>R>,13,2GX0=1X=>%<8RK=8=>P=PKP:P@P4P:PAP4E3#0RL%7H%4C'>RH,=<#0'1RM%0H/1L/13'2X0=P=%0DRL/1BRH12M3X0=P8PG11FBPHAW8BFP8PFPLPBP<PDPE1V<DCT9SEDDREL11HK1K8HE5P>P3EIb3AA<;I#01J;IE51=<;R;#0,1JP:P@P?P:PAP?E3#0/1>'2e%6CR>P2E5%:CR2P7E5P:P@%HC%GC%MCP6%N5%<9599P;%OCFPR;#:R9P:PAP9E3#0%6;#0'1P:P@P2P:PAP2E3#0%0>'1'2ePCP4P5P6CQ#B%BC'2eW4W1W2W6X81X70W5o"). Qed.

(* [comment removed for export] *)
Lemma do_recycle_cons : forall {RT} st b bs (k : astate -> AM RT),
  do_recycle st (b :: bs) k = recycle_chunks st (rev (b_chunks b)) (fun st1 => cache_dealloc st1 K_BATCH_CLASS (fun st2 => do_recycle st2 bs k)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h02RTh11bh22bsh31kh42sth53st1h63st2p;1p;2p;4p200R0g004[R1p4p710p8P0g01YcR2p4p710p8P0g01ZcR3p4p710p8P0g01[dR4p4p710p8g00@Lj17TP1j16Tg01ACj10Tg00[<j21TP4j45TP2j42TP3j43Tg00E0j24Tg01NVR3g01LdR2%72f4R2#6R4\3P2f3R2g00]`f2R1#0'1f5f0R5g01S2f6P5P2P1C5X63C2X53C3,44W3W2W1W4X00o"). Qed.
Lemma recycle_chunks_prim : forall {RT} st c n l (k : astate -> AM RT),
  recycle_chunks st (CPrim c n :: l) k = cache_dealloc st c (fun st1 => recycle_chunks st1 l k).
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h02RTh11ch21kh31lh41nh52sth63st1p;1p;4p;2p200R0g004[R1p4p710p8P0g01YcR2p4p710p8P0g01ZcR3p4p710p8g00@Lj14TP1j13TP3j40TP2j41Tg00E0j22Tg01NVR2g00]BR3g00]`#4f5R1#3R4\2P1f4f3f6f0f2f1C0X62C1,24W2W3X43W1W5X00o"). Qed.
Lemma recycle_chunks_sec : forall {RT} st mb ms n l (k : astate -> AM RT),
  recycle_chunks st (CSec mb ms n :: l) k = large_dealloc st mb ms (fun st1 => recycle_chunks st1 l k).
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h02RTh11kh21lh32mbh42msh51nh62sth73st1p;1p;4p;5p;2p200R0g004[R1p4p710p8P0g01\aR2p4p710p8P0g01ZcR3p4p710p8g00@Lj14TP1j13TP3j40TP2j51Tg00E0j22Tg01NVR2g00]BR3g00]`#4f6R1#3R4\2P1f5f4f3f7f0f2f1C0X72D1,24W1W2X53X43W3W6X00o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AQdr_popr : forall R L st X m b q T,
  AQdr R 0 0 L st X m -> qr_tmp R = (b, q) :: T -> qr_pendb R = [] -> qr_pend R = [] ->
     AQdr (qr_popr R b q T) 0 0 L st X m
  /\ abatch_cells L m b q (qfirst L (map snd T))
  /\ Q_BATCH_BYTES <= b_size b /\ qnum_tmp (map fst T).
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h01Hh12NTh22TBh31bh41lh52BCh62CPh72EBh82EPh92ETh:2GLh;2IAh<1Lh=2MXh>2NBh?3NT'h@3NUMhA2QChB1RhC1ThD3TB'hE2TChF1XhG1mhH1qhI2stp&0p;1p;2p;6p;4p;3p;5p;7p;;g00@lj1FTg00AQj1dTg00Aoj1^Tg01]aj1lTg00C8j2eTg00@Lj1TTg01^Cj1WTg01_Aj1DTg015Dj1CTg014Lj1ATg01`=j1BTg01a<j65Tg001ok203Tg00ogj11Tg01@fj2|Tg00DPj1_Tg01>Vj46Tg00nij4GTg01b4j1ETg006Gj6jTg01bkj1NTg01cej2iTg0000j3hTg01d\j5OTg01eYj5gTg01fUk502Tg01g4k501Tg001Nk300Tg01>;R0j20Tg0176j1aTg016=j1VTg01gXj1`Tg01hXj4UTg01E@j1MTg01iQj2KTg01F7j1yTg00EJj3RTg01ACj1xTg01B>j1wTg00Z`j4vTg00[<j2uTg01Foj1tTg01Gij7rTg01jHl;qTg01kMj4PTg01khj7QTg01l^j3oTg000Gj4JTg00GUj4]Tg00H5j3STg010_j1nTg011Yj1mTg01m[j2bTg01nRj1cTg00LUj2\Tf4R1g00c<R2P2f3R3f2R4f1R5f0R6FQp=zAo622p=HP1P3g01oKR7%a4%V5%`6E5p=@P4g01LdR8P5P6CJp=2f5R9P1P3P4g01KjR:P5P6CJCUp=?f7R;#Mf6R<'KP9P1P3P4CG%E5%N6'0'0'0p==1056,04p=4%11P8P:P4P5C]=R365S9p=;%n5=S46p=>%m5=S46p=9P4P:P5P6CJ,b3p=<P4P8P5P6CJ#Np=3P<P9P1P3P4DOg020GR=%c5'\/06'0p=8P9P2P2P1P3P4P5FQ/06p=7P4P:P5P6CJp=:P1P3P4P5CU/06p=I%M;/K<P9P1P3P4CG%E5/06'0'0p=k%M5/K6p=[P9P1P3P4CG%E5/06'0p=Z%E5/06p=YP8P:P4P5C]=R36p=X%c6,\=p=fP;P<P9P1C6P2P2P3P4P5P6FQp=~P9P1P3P41b56DOp=}P1P3P7P4P5P6E5p={P<P9P1P3P4P5P6CPCPp=LP1P3P7P4%V5P6E5p=p%M4/K5/06p=sg01PHg00a]g01NVg01OQg00bW#F#F#FR7#F#F#F#d#^%d7#^#l[1e8:R7#TR=P;P<P9P1P3DzP0%W1%H1P;P1%D;%C<f8R>#A%B<E5P;P1P<P>P<D@P;P12038:R?%1>R@527RAP71|8:RBP@E?P>P1P;P<P9P>P<PAG=3434P=f9RAP7P1P3P4E;g00]BR@#TRCf:RD%_@RE3>g00]`RF/e@RG#TRHf;RI%_GRJ39f<RKP;P<P9C6PIPDPAP>PIP>P;P<PIP7PBP9C<P;A37?9F8E7[[[P6%W<%H;PDP;%DD%CA%AI%BAE5PDP;PAPIPAD@PDP;%1IRL927?RMP7PBPLE?PIP;PDPAP>PIPAPMG=3434P0%H>PIP>%DI%CD%AK%BDE5PIP>PDPKPDD@PIP>%1KRM927?RLA:7BMPKP>PIPDPAPKPDPLG=DI34P=f=RLP7P>P;P<E;f>R<=>CEf?R;=9HJf@RMPIPDPAC6P;P<PLPKP;PKPIPDP;P7PBPAC<PIA37?AF8E7[[[P6%HDP<PI%D<%CL%A;%BLE5P<PIPLP;PLD@P<PI%1;RN927?ROA:7BNP;PIP<PLPKP;PLPOG=DI34P0P;PK%D;%C<%AM%B<E5P;PKP<PMP<D@P;PK%1MRO927?RNP7PBPOE?PMPKP;P<PLPMP<PNG=34P=fARNP7PKPIPDE;fBRI=>CEfCRO=9HJfDRPP;P<PLC6POPIPNPMPOPMP;P<POP7PBPLC<P;A37?LF8E7[[[P6PNP<%DN%CM%AI%BME5PIP;PNPOPND@PIP;%1ORL927?RQP7PBPLE?POP;PIPNPMPOPNPQG=34P0POPMPIPPPID@POPM%1PRQ927?RLA:7BQPPPMPOPIPNPPPIPLG=DIP=fERLP7PMP;P<E;fFR<=>CEfGR;=9HJfHRQPOPIPNC6P;P<PLPPP;PPPOPIP;P7PBPNC<POA37?NF8E7[[[P6PLPIPPP<PPD@P<PO%1;RN927?RRA:7BNP;POP<PLPPP;PLPRG=DIP0P;PP%1QRR927?RNP7PBPRE?PQPPP;P<PLPQP<PNG=P=fIRNP7PPPOPIE;fJRI=>CEfKRO=9HJfLRRP;P<PLC6POPIPNPQPOPQP;P<POP7PBPLC<P;A37?LF8E7[[[P6PNP<%1IRL927?P7PBPLE?POP;PIPNPQPOPN%1O937?GkP01[RQPOPIPNPRPI%1R937?EZP=fMRLP7PQP;P<E;fNR<=>CEfOR;=9HJfPRQPOPIPNC6P;P<PLPRP;PRPOPIP;P7PBPNC<POA37?NF8E7[[[P61[<IP<PLPRP;PL%1;937?EZP0P;P<PLPQCG%1Q937?,Y<P=fQRNP7PRPOPIE;fRRI=>CEfSRO=9HJfTRSP;P<PLC6POPIPNPQPOPQP;P<POP7PBPLC<P;A37?LF8E7[[[P6PNPQP;PICG%1O937?,YNP0%EI%1S937?P=fURLP7PQP;P<E;fVR<=>CEfWR;=9HJfXRTPOPIPNC6P;P<PLPSP;PSPOPIP;P7PBPNC<POA37?NF8E7[[[P6%ES%1;937?P=PTP7POPIPNE;fYRN=>CEfZRC=9HJP=f[RJ#1PJPTA27?6RHP7PBP6E?X4=PMP7P<PLPSCXRIP4EjPCP;A27?IP7PBPIE?P=f\RI#1%NHX4=P1P7P;P<PLCXRLP3EjA37?LP0PIPNPTP;A:7B<R0,iI9h@2DOPIPNA27?<P0P2Dgf^R0PNPTP;C6f]R<PIPJPCP<PCPNPTP<P7PBP;C<PNA37?;F8E7P5P0PJPCPNA:7BT,i09h@2DOf_R;PIA27?NA:7BNP2DgP8%f6X38R2PIA27?CP1I02P2PIO1P8P2P<A27?JRJP9I01B0082JfcRJP0P<PIfbR2faR9f`R1P;G~RCP2P;P0P<P2A:7BIRNE}RL%f0R=A27?IRH#NRO'0RU'0%W;RV%H;RWP2P;%D2RX%C9RY%AJRZ%B9R[E5R\P2P;%a9R]%VJR^%`9R_D{R`P2P;PHPNCURN%MJRH/K;RaP2P9P1PZP^PHPI%y<=R@EPFP@%x0%w<Cv,uG%tJFrRGCGR@%E9RF/0ORE'0RH'0R^'0RZ'0Rb'0Rc'0PTPWPcPSP\PbPQP`PZPRPNP^P4PaPHPPP@PEP2P9P1PJP0P<PIPMPDPAP>M;qPFPOPKP6FLFLFLFLP2P;PXPY%AGP[E5P2P;P]PGP_DpP2P;%1GR2927?R?A:7B2%N?94@F9sG;DI3494VWePCePLPUP3P=POP5P6CPFLb?b>WDW5P5P6O2n2001000000121000000b1b2W8W7W9W1W@P5P6O2n2001000000121000000W0W6P5P6O2n2001000000121000000W0W;P5P6O2n2001000000121000000W0W2P5P6O2n2001000000121000000W0W:P5P6O2n2001000000121000000W0WEP5P6O2n2001000000121000000W0W=P5P6O2n2001000000121000000W0WAP5P6O2n2001000000121000000W0WCXH:X38WGWFWIW<WBo"). Qed.

Lemma AQdr_drop_sec : forall R L st X m mb ms n kk pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CSec mb ms n, kk) :: pend' -> AQdr (qr_drop R pend') 0 0 L st X m.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h01Hh12CPh22EPh32GLh42IAh51Lh62MXh72NTh83NUMh92QCh:1Rh;2TBh<2TCh=1Xh>2kkh?1mh@2mbhA2mshB1nhC5pend'hD2stp;1p;2p;6p;4p;7p;;p;3g00@lj1ATg00AQj1TTg00Aoj1PTg01]aj1XTg00C8j2STg00@Lj1]Tg01^Cj1ITg01_Aj1<Tg015Dj1;Tg014Lj1:Tg01`=j1?Tg01a<j64Tg001oj2`Tg00ogj10Tg01@fj2ZTg00nij4BTg01b4j1@Tg01bkj1=Tg0176j1LTg016=j1HTg01gXj1KTg01E@j1GTg01iQj2FTg010_j1VTg01Foj1UTg01Gij7gTg01>;R0j22Tg021Gl;fTg01kMj48Tg01khj7RTg01l^j3_Tg000Gj4JTg01hXj4QTg011Yj1\Tg00icj3^Tg00GUj4[Tg00EJj3aTg00H5j3bTg022Nj2cTf4R1g00c<R2P2f3R3f2R4f1R5f0R6FRp=YA_622p=DP1P3g01oKR7%L4%H5%K6E4p=9P4g01LdR8P5P6CJp=1f5R9P1P3P4g01KjR:P5P6CJCQp=>f7R;#Gf6R<'FP9P1P3P4CB%@5%=6'2'2'2p=51256,24p=3%\<g00]`R=g00]BR>A^134P5C[=a965b;p=71c91P2P2P3P4P5P6FRp=6P4P:P5P6CJp=EP1P3P4P5CQ/26p=C%G5/F6p=OP9P1P3P4CB%@5%=6'2'2p=N%@5%=6'2p=MP1P3P7P4P5P6E4p=WP1P3P7P4%H5P6E4p=e%G4/F5/26p=dg01PHg00a]g01NVg01OQg00bW#A#A#AR7#A#A#A#T#P%T7#P#X[1S=>R=#]R7f9R2f8R?P;P<P9DYP0%I<%D<P2P<%<2%;?f:R@#:%??E4P2P<P?P@P?D9P2P<1S8:RA1`8:RB%0@RC31RDPA1Z8:R:PCE>P@P<P2P?P;P@P?PDG53333P7f;RDP=P<P9P1P3P4G7f<R1P3PDP@P2P?E6[P6%I?%D2P1P2%<1%;Df=R3#:%?DE4P1P2PDP3PDD9P1P2%03R991ABRCPAP:P9E>P3P2P1PDP@P3PDPCG53333P0%D@P3P@%<3%;1f>RC#:%?1E4P3P@P1PCP1D9P3P@%0CR991ABR8AEA:9PCP@P3P1PDPCP1P8G5DC33P7f?R8P=P@P2P?P;P<G7f@R?P;P8PCP3P1E6[P6%D1P?P3%<?%;8fAR;#:%?8E4P?P3P8P;P8D9P?P3%0;R291ABR9AEA:2P;P3P?P8PCP;P8P9G5DC33P0P;PC%<;%;?fBR9#:%??E4P;PCP?P9P?D9P;PC%09R291ABREPAP:P2E>P9PCP;P?P8P9P?PEG533P7fCREP=PCP3P1PDP@G7fDR1PDPEP9P;P?E6[P6PEP?%<E%;9%:1%?9E4P1P;PEfERDPED9P1P;%0DR391ABR2PAP:P3E>PDP;P1PEP9PDPEP2G533P0PDP9P1fFR2P1D9PDP9%02R391ABRFAEA:3P2P9PDP1PEP2P1PFG5DCP7fGRFP=P9P;P?P8PCG7fHR?P8PFP2PDP1E6[P6PFP1P2P?P2D9P?PDfIR8#0R;91ABR3AEA:;P8PDP?PFP2P8PFP3G5DCP0P8P2fJR3#0R;91ABRGPAP:P;E>P3P2P8P?PFP3P?PGG5P7fKRGP=P2PDP1PEP9G7fLR1PEPGP3P8P?E6[P6PGP?%01RE91ABPAP:PEE>fMREP8P1PGP3PEPG%0E91ABG5P0fNRD/O3PEP1PGPDP1%0D91ABENP7fOR;P=P3P8P?PFP2G7fPR?PFP;PDPEP1E6[P61O?1P?P;PDfQRFP;%0F91ABENP0PFP?P;fRR8CB%0891AB,M?P7fSRHP=PDPEP1PGP3G7fTR1PGPHP8PFP?E6[P6PHP8PFP1CBfURG#091AB,MHP0%@1fVR0#091AB#=P7fWREP=P8PFP?P;PDG7fXR?P;PEP0PGP1E6[P6%@0fYR;#091AB#=P7fZR7P=PGP1PHP8PFG7%IERF%DER=P7PE%<7RI%;;RJf[RK#:RL%?;RME4RNP7PE%L;RO%HKRP%K;RQDWRRP7PE%0KRS91ABRTPAP:PSE>RU%GKRV/FERWP7P;P?PLPPPVPS%VKP8%UKFgRSCBRV%@;RP%=TRT'2RL'2RX'2RY'2RZ'2R['2R\'2PDP=P\P3PNP[P2PRPZP9PUPYPCPWPXP@PVPLP7P;P?PKP0PGP1PHP8P<P6M;fPPPTP4P5C8C8C8C8C8C8C8C8P7PEPIPJ%:SPME4P7PEPOPSPQDeP7PE%0SRQ91ABRBAEA:Q%=B93VP9dSEDC3393F=ePKP8P7P;P?PEE6eW2W7W8P5P6O2n2001000000121000000W0W1P5P6O2n2001000000121000000W0W4P5P6O2n2001000000121000000W0W;P5P6O2n2001000000121000000W0W3P5P6O2n2001000000121000000W0W<P5P6O2n2001000000121000000W0W6P5P6O2n2001000000121000000W0W9P5P6O2n2001000000121000000W0WCX>>XB>XA>X@>W?W=WDW5W:o"). Qed.

(* [comment removed for export] *)
Lemma AQdr_set_nsec : forall R L st X m v, AQdr R 0 0 L st X m -> AQdr R 0 0 L (set_nsec v st) X m.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "p'0h01Hh11bi001bh22CPh32GLh42Hbh52IAh61Lh72MXh82NTh93NUMh:2QCh;1Rh<2TBh=2TCh>1Xh?2b0h@1mhA1pi011phB2sthC1vi021xp;1p;6p;2p;4p;3p;8p;7g00@lj1ATg00AQj1YTg00Aoj1VTg01]aj1_Tg01^Cj1KTg01_Aj1;Tg015Dj17Tg014Lj1=Tg01`=j16Tg01a<j65Tg00C8j2fTg001oj2eTg00ogj11Tg01@fj2`Tg00nij4BTg01b4j1>Tg01bkj1@Tg0176j1ITg016=j1STg01gXj1HTg023Gj2QTg01>;R0j20Tg00@Lj1]Tg00H5j3CTg024Bj1[Tg01:aj1NTg01J`j3MTg01;Wj1dTg00E0j2ETg025@j4cTg026;j8bTg01khj7PTg01l^j3aTg000Gj4LTg01hXj4WTg01E@j1ZTg01iQj2OTg01kMj4XTf4R1g00c<R2P2f3R3f2R4f1R5f0R6FPp=\Aa622p=DP1P3g01oKR7%I4%S5%H6E5p=9P4g01LdR8P5P6CLp=2f5R9P1P3P4g01KjR:P5P6CLCWp=:f7R;#Zf6R<'OP9P1P3P4CB%>5%@6'0'0'0p=41056,04p=3P9P2P2P11Q34P5P6FPp=8P4P:P5P6CLp=GP1P3P4P5CW/06p=F%Z5/O6p=JP9P1P3P4CB%>5%@6'0'0p=U%>5%@6'0p=TP1P3P7P4P5P6E5p=R%>5/06p=^g00]BR7?C56p=?P<P9P1P3P4P5P6CXCXp=<g01PHg00a]g01NVg01OQg00bW#A#A#AR2#A#A#A#Y#V%Y2#V#_[P9P1P3P4P5D\P0%K4%D4P9P4%;9%71%=<%61E5P9P4P1P<P1D9P9P41f8:R21e8:R=%1<R>32R?P21`8:R:P>E:P<P4P9P1P3P<P1P?G43333P;P<P4P9P1P3E8P6%K1%D9f8R1P9%;1%7;f9R4#=%6;E5P1P9P;P4P;D9P1P9%14R?922=R>P2P:P?E:P4P9P1P;P<P4P;P>G43333P0%D<P4P<%;4%71f:R>#=%61E5P4P<P1P>P1D9P4P<%1>R?922=R@AG2:?P>P<P4P1P;P>P1P@G4DF33f;R@P>P<P4P1P;E8P6%D1f<R1P4%;1%7@f=R;#=%6@E5P1P4P@P;P@D9P1P4%1;R<922=R?AG2:<P;P4P1P@P>P;P@P?G4DF33P0P;P>%;;%71f>R?#=%61E5P;P>P1P?P1D9P;P>%1?R<922=RAP2P:P<E:P?P>P;P1P@P?P1PAG433f?RAP?P>P;P1P@E8P6PAP1%;A%7?f@R1#=%6?E5P1P;PAfAR@PAD9P1P;%1@R>922=R<P2P:P>E:P@P;P1PAP?P@PAP<G433P0P@P?P1fBR<P1D9P@P?%1<R>922=RBAG2:>P<P?P@P1PAP<P1PBG4DFfCRBP<P?P@P1PAE8P6PBP1P<fDR1P<D9P1P@fERA#1R?922=R>AG2:?PAP@P1PBP<PAPBP>G4DFP0PAP<fFR>#1R?922=RCP2P:P?E:P>P<PAP1PBP>P1PCG4fGRCP>P<PAP1PBE8P6PCP1fHR1#1RB922=P2P:PBE:fIRBPAP1PCP>PBPC%1B922=G4P0fJR</J>PBP1PCP<P1%1<922=EUfKR?P<P>PBP1PCE8P6fLRC/J1PCP?P<fMR1P?%11922=EUP0P1PCP?fNR>CB%1>922=,TCfORDP>P<P1PCP?E8P6PDP>P1fPR?CBfQRC#1922=,TDP0%>?fRR0#1922=#@fSR<P0P>PCP?PDE8P6%>0fURD#1922=#@%K0R?%D0R>PDP0%;DREfTRF#7RGfVRH#=RI%6FRJE5RKPDP0%IFRL%SHRM%HFRNDRROPDP0%1HRP922=R=P2P:PPE:RP1JH0R:PD1QCFRCP<PHCBR2%@=R=,^CRQ'0RR'0RS'0RT'0RU'0RV'0P1P>PVPBPKPUPAPOPTP@PPPSP;P:PRP4P2PQPDPFPCP<P<PHP9%]8R8?CGG1?JJR9AC8LLRQ1?NNR2%[FR4/?4RRg01M_R:%NF9M:6R;g01QBRSp-0RP%d5R@g027>RO%ND9M:5RAPAn011020003101010000[]1RA/0ARU'0RK'0RB'0RV'01E8GP9PV1E7JPQPB1E8LP2PK1E7NPRPU1E74PAPAP@PSPSPSPPP6POfW#N9M:3R3P3n011020003101010000P6g005Pg027ZWAP6O1P5P5n011000003101010000b?X4;X1:R:P:F<F<F<%7CR:=C8G%6CRG/?J%ICRJ=C8L%HCR8/?N%[C/?4/0U3333ePFPCP<P<CceGb%>FP=P5P6F<F<F<F<PDP0PEP:PIPGE5PDP0PJPMP8DR;3T93?>ePHPDPCP<P0D\eW8W9P5P6O2n2001000000121000000W0W2P5P6O2n2001000000121000000W0W5P5P6O2n2001000000121000000W0W<P5P6O2n2001000000121000000W0W3P5P6O2n2001000000121000000W0W=P5P6O2n2001000000121000000W0W7P5P6O2n2001000000121000000W0W:P5P6O2n2001000000121000000W0XC7W@W>WBW6W;o"). Qed.

(* [comment removed for export] *)
Lemma tmp_head_geo : forall R L st X m b q T, alayout_ok L -> awf L st X -> AQdr R 0 0 L st X m -> qr_tmp R = (b, q) :: T ->
  17594333495296 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "p'0h01Hh11zh22G5h32G4h41bh51lh61Ah72_Hh83_H0h93_H1h:3_H2h;3_H3h<3_H4h=1ah>2l'h?3ALOh@2CPhA2CbhB2EThC2HbhD2KbhE1LhF1RhG2SbhH1ThI2WFhJ1XhK3_H5hL2bbhM1ehN1mhO1qhP2sti001xp&0p;1p;2p;4p;7p;6p;3p;8g00@lj1?Tg00AQj1~Tg00Aok102Tg01]ak10MTg00C8k20ITg00@Lj1nTg0286k20>Tg0295k40<Tg01khk70:Tg01^Cj1{Tg01_Aj1VTg015Dj1^Tg014Lj1UTg01`=j1ZTg01a<j6TTg001ok20DTg00ogj17Tg01@fk20Ak30JTg00JNj1_Tg029hk109Tg00nij4eTg01F7j1HTg016=j1uTg002Lj3]Tg01J`j3>Tg02:^k204Tg02;8k40LTg00EJj3rTg00H5j3YTg00E0k20HTg02;Wk30GTg02<1k301Tg003`k60FTg02<Kk30ETg02=Ik70CTg01:aj1cTg01;Wj1bTg01<Lj12Tg01=Dj18Tg01>;R0j21Tg01K7R1k20@Tg02>Rj2mTg02?Nk80=Tg02@Nj2PTg02@jj2`Tg02A_j2=Tg02BVj24Tg02CNj2@Tg02DHj1ATg00Jlj23Tg02EKj1BTg02FHj1CTg02GHj19Tg02HAj1hTg00LUj20Tg02Hfj1WTg02Ifj3tTg006Gj6dTg01kMk407Tg01l^k306Tg0176k105Tg01gXk10BTg000Gj4oTg01hXj4yTg01E@k100Tg01iQk203Tg01b4j1pTg01bkj1sTg00GUj4qTf0R2#?#?p=[g00c<R3>0623p=kf4R4f3R5g01oKf2R6$05f1R7#u&0B2ETp=OP6g01LdR8P7P2Cop=:f5R9P4P5P6g01KjR:P7P2CoCyp=Xf7R;$00f6R<+03P9P4P5P6Ce%p7%s2'1'1'1p=D1172,16p=<%74P8P:P6P7Cq=r525Y9p=K%?2#?#?#?p=Q%h2#hp=I%H2,m7p=610451367/02'1p=5P6P:P7P2Cop=JP4P5P6P7Cy/12p=j&0070032p=zP9P4P5P6Ce%p7%s2'1'1p=x%p7%s2'1p=wP8P:P6P7Cq=r52p=vA>:72p=\P8P:P7P2Cqp>0Kg01QBg01R:7Y2p=ag00]BR=g01S2R>7Y2p=S%H29Y=7p=MAY=72p>0?%W2,37p=;1045g02J`R?,06'1g02K`R@,37g02L[RA,32'0'1p=G1394/051372,06'1p=N10;</1910451067/12'1'1p=F1056/17/12p>0;1067/12p=l10451067/12'1p=g1372,06p=R10;<10941356/07/12'1'1p=f10451167/12'1p=i1367/02p=E102?p=|137@132A'0p=}1356/07/12p>08At7>2p=Lg01PHg00a]g01NVg01OQg00bWRA#?#[R@#?#[R?#~$02%~@$02$0M[20I8:R@#nRBp,2rcRC00><PCP;P<P9H0<f9RDP3P3f8REP;P<P9K0:P0%{<%k<PDP<%VD%^Ef:RF#U%ZEETPDP<PEPFPEDOPDP<20D8:RG%7FRH5:@RIP@20A8:RJPHEXPFP<PDPEP;PFPEPIGD3<3<PBf;RIP@P<P9P4EK%[?#QR?#?RH#I#I#I#I#I#I#I#I#?#[#Q#Q#Q#_RK16I<R<P<%_HR<&09CRLD5[P2%{E%kDf<RMPD%VM%^If=RN#U%ZIETPMPDPIPNPIDOPMPD%7NRO9:@GRPP@PJPOEXPNPDPMPIPFPNPIPPGD3<3<P0%kFPNPF%VN%^Mf>RP#U%ZMETPNPFPMPPPMDOPNPF%7PRO9:@GRQAJ@JOPPPFPNPMPIPPPMPQGDDj3<PBf?RQP@PFPDPEEKPK16QFRFPFP<PLD5[P2%kMf@RFPN%VF%^QfARO#U%ZQETPFPNPQPOPQDOPFPN%7ORR9:@GRSAJ@JRPOPNPFPQPPPOPQPSGDDj3<P0POPP%VO%^FfBRS#U%ZFETPOPPPFPSPFDOPOPP%7SRR9:@GRTP@PJPREXPSPPPOPFPQPSPFPTGD3<PBfCRTP@PPPNPMEKPK16TPRQPQP<PLD5[P2PTPF%VT%^SfDRQ#U%ZSETPQPOPTfERRPTDOPQPO%7RRU9:@GRVP@PJPUEXPRPOPQPTPSPRPTPVGD3<P0PRPSPQfFRVPQDOPRPS%7VRU9:@GRWAJ@JUPVPSPRPQPTPVPQPWGDDjPBfGRWP@PSPOPFEKPK16WSRTPTP<PLD5[P2PWPQPVfHRTPVDOPTPRfIRU#7RX9:@GRYAJ@JXPUPRPTPWPVPUPWPYGDDjP0PUPVfJRY#7RX9:@GRZP@PJPXEXPYPVPUPTPWPYPTPZGDPBfKRZP@PVPRPQEKPK16ZVRWPWP<PLD5[P2PZPTfLRW#7RX9:@GP@PJPXEXfMRXPUPWPZPYPXPZ%7X9:@GGDP0fNR[/zYPXPWPZP[PW%7[9:@GExPBfORZP@PYPUPTEKPK16ZYR\P\P<PLD5[P2fPR\/zWP\PZP[fQR]PZ%7]9:@GExP0P]P\PZfRR^Ce%7^9:@G,w\PBfSR_P@P[PXPWEKPK16_[R`P`P<PLD5[P2P_P^P]fTR`CefURa#79:@G,w_PBfVRGP@P]P\PZEKPGPaP`fWRZ%H]P6PBP@P^P]P\CvfXRb#URc%ubRdAJ@J25]:5]:,\^X5Bg004>p4p710RB%n2Re%n7RfP0A]5679>52A>475A>476+04Rg[A>526A>527+04A]4569>47[RhA]9459>96\gP5P6P7P2H0LP2n2001000000120000000X=6W>W5W6RgPh^=6^>f^5e^6BRBP2P:PcP@P_P^P]Cv9J@J9]:dRdP^1\^c1\^dPgPBP2P:fYRB#uRg20K`_Rd=r@^9J@JRcP_1\_g1\_cB0J8:d=Y:_AJ@J^,\_20H:_40G401O5b0401O5b0%7ZP2J0F:0EZ]K0Cg01M_RJ%ca9>J2%b2#aR@%22#SRd%82Rc/M^'13<X4J+0@P1PJ%cG9>J2%H_R_-0?c,1d7<@X4JPK1mb_R_P_P<PLD5P2%cb9>J21Mca,1d7<@P0%cB9>J7%b7#a%27#S%87/MG3<PKf\R@/6ZRZPZP<PLD5P2f[RZ#c9>J5%b4#a%24#S%84/MB3<P0%b9#a%29#S%89fZR4'M'1PKf`Rd/6ZRcPcP<PLD5P2%b;#a%2E#S%8Ef]RE'M'1P0%2D#S%8Df^'MPKfdR;f_Rc'6R_P_P<PLD5P2%2I#S%8Mfa'MPCfgRCffRMfePdPcPNPDL0=%_ARA%2NRDg02MZRc,PDP3%8NRd1`MD,Pd1=CDRd14CNRN1;NDRI1@MDRD#ARM,3d%BCR_PdPM%CDRDPDPdP_DGPKPNPIPL%9CR_%_?R?PNPIP_%?H#[#Q#h#?#[#h#Q#Q#Q#_RHENGFGFH0;P0%2PR_1P_c5lAP3%8PRI1`C_,PIfhRI/=_RN14IPRP1;P_Rd1@C_R_#ARC,3N%BIRDPNPC%C_R_P_PNPDDGPKPPPdPL%9IRDP?PPPdPDPHENGFGFPKfi/6;R;P;P<PLD5P2%2FRF1PFc5lAP3%8ORAfjRF%2ORc'`,PAfkRA/=cR;14AORO1;OcRD1@FcRc#ARF,3;%BARdP;PF%CcRcPcP;PdDGPKPOPDPL%9ARdP?POPDPdPHENGFGFP0%8SRd%2SRD,`A,Pd5l3flRd/=DRO14dSRS1;SDR;1@ADRD#ARA,3O%BdRcPOPA%CDRDPDPOPcDGPKPSP;PL%9dRcP?PSP;PcPHENGFDgPKfmRc/6IRIPIP<PLD5P2%8QRI%2Q,`c,PI5l3foR3%2RRI'=Rc143RRR1;RIRQfn/@IRI#AR;,3c%B3RSPcP;%CIRIPIPcPSDGPKPRPQPL%93RSP?PRPQPSPHENGFDgP0fpRS%2VRQ'=RR14SVRV'01;VQRc1@3QRQ#AR3,3R%BSRI/0RP3%CQRQPQPRPIDGPKPVPcPL%9SRIP?PVARcIHGfDiPKfq/6dRdPdP<PLD5P2frRd%2T'=14dT'0fsRT/4URI%2URU';Rc1=TURV1@dURU#ARd'3%BTRR/0VPd%CURUPUPVPRDGPKPIPcPL%9TRRP?PIARcRHGfDiP0ftRR/4YRc%2YRY';RI1=RYRV1@TYRY#ART3R%BRRUPVPT%CYRYPYPVPUDGPKPcPIPL%9RRUP?PcPIPUPHENGFPKfuRU/6SRSPSP<PLD5P2fvRS/4W%2WRW#W1=SW1@UW#A'33EfwRW#BRU%2XRI,=WRc1@SIRS#A%CSRSPSPcPUDGPK14WXRX1;XIRIPL%9WRUP?PXPIPUPHENGFP0fxRU#BRI%2[RX,=URc1@WXRW#A%CWRW'0%|W1}cIDiPK14U[Rc1;cXRXPL%9URIP?PcARXIHGfPKfyRI/6RRRPRP<PLD5P2fzRR#BRX%2\Rc,=RRR1@IcRc#A%CcRc'0%|c1}RXDiPKf{RR/4]RX%2],;XR]PL%9RRRP?PXAR]RHGfP0f|RR/4^R],0K%2^,;]R^PL%9RRX/3?P]AR^XHDgPKf}/6URUPUP<PLD5P2f~/4`,0Kp+01@R`/4aRU%2a';RaPL%9`R`/3?PUARa`HDgP0p+01AR0/4GR`%2G';RG/0L%90RaP?P`PGPaPHENPKp+01B/6RRRPRP<PLD5P2p+01CRR/4b%2b#W;ELp+01DRb#9RaP?14bBR?%2B#W13aH5E?H08P=%24p+01FR?%8ZRZ7t2,0KX1=P9P>P[Edp+01ER9%84'L,0KP=PZp+01GRZ/L2,0KX1=P2%H0R0P[Ed1L?0,0KP=%2@p+01HR0%8ERE7t2%W2;ELX1=P5P>P\Ed%8@,LZ%W>R>;ELP=PEp+01IRE/L2?E>LX1=P2%HRRRP\Ed1L0R?E>LP=P>p+01JR>%H9R9'LRR?E2LX1=P2P<g02NZEd%Hb,LE?E<L10KRAER<LP5P2H07PK1m>9R9P9P<PLD5eb2b2b2b3b3W<W2P7P2O2n2001000000121000000W0W3P7P2O2n2001000000121000000W0W;P7P2O2n2001000000121000000W0W:P7P2O2n2011000000121000000W0W9P7P2O2n2011000000121000000W0W8P7P2O2n2011000000121000000W0W7P7P2O2n2011000000121000000b0WDWAP7P2O2n2001000000121000000W0WGP7P2O2n2001000000121000000W0WCP7P2O2n2001000000121000000W0XLJP7P2O2n2001000000121100000bMWBWKW@P7P2O2n2001000000121000000W0W<P7P2O2n2001000000121000000W0W;P7P2O2n2001000000121000000W0W:P7P2O2n2001000000121000000W0W9P7P2O2n2001000000121000000W0W8P7P2O2n2001000000121000000W0W7P7P2O2n2001000000121000000W0WIW?WHXO:X48WNWJWPWEWFo"). Qed.

(* [comment removed for export] *)
Lemma live_sec_in' : forall st (p : aptr) mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> In (CSec mb ms n) (sec_chunks_of st).
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h01Ah11Ph21fh31lh41xh51Hh62Lph72mbh82msh91nh:1ph;2stp;1p;4p;6p;3p;2p;5p;@g01]aj1`Tg00=Ij4_j3KTg006cj4Qj3GTg02O\j14Tg02PUj6^Tg00icj32Tg02Pij2TTg00H5j38Tg00@Lj1LTg00hPj36Tg01J`j30Tg01>;R0j2;Tg02QKj4]Tg02Qij1WTg00hkR1j1VTg00C8j2<Tg01@fj2=Tg008Ij4Uj3DTg02Rcj59Tg000Gj43Tg015Dj1STg0176j1PTg002Lj3OTg02S@j4NTg02S]j3HTg00@4j3FTg007<j3Ij4RTg02T4j3JTg02TKj3ETg009<j3MTg02Tcl@CTg00GUj4?Tg02UGj4BTg02Ucj55Tg00EJj3:Tg000cj3ATg007\j6\Tg00E0j2>Tg02;Wj3@Tg02V7j6XTg02Vcj5YTg01kMj4ZTg02WAj1[Tg00f8R2f0R3g00fXR438p=7g005PR5g00]`R6f2R7f1R8P3D9p=1g01NVg00]BR9%`6P5P6g02X@R:g02X^R;g02Y7R<P6C_R=P:P;P<P6CQf3R>f4R?#4E^A2783,T638g02YUp4p710R@P2\3RA%L7RBP0A6>7390>8A0?78P>P7O1#7';R0[A0>83P7P8O1#7';A6?>890?7[RCf5RDA6D?770>\0P>P7P8P3C]P3n2001000000120000000W3X48W2W0PC^3B^48^2A^0@P3P6P1A2?>7R1f6R@#WRAA061ARA%V1#7P61<:6RBP61=:6RCP:P6P=P:P;P<P6CUR0%4@RED9C3RFg01LdRGP6g01AC%S@%P@5OGCNRGP1A061FA061GP5AK:;<AH:;<AG:;<AF:;<AI:;<AJ:;<AE:;<AD:;<P;AM:;<P6PEPDP1P8M@C1<56RGP5P6PDP1C?P5P=P5P6P=P:P;P<P6CRCBR<PDPED591=05:GA1=0E3APGP61=56REP5P6P@A2D?>C?P5P=P<P@f7R;#4R1D591=05:GRFA1=01R1P3E\PGP6PEPFC3PGP6PEP1C35A6P6A2@D?R@PGP6PEP5P=P<P;f8#4R;D591=0C3R<5:6PBP6PCP:P6P=P0P;D9C3P@P3A86@@A06@<1>6@3@EXb1b13@DYPAe1>24CZO5b5A2>78%[D506eW6X99X89W7X:5W;o"). Qed.

Lemma achunk_eq_dec' : forall c1 c2 : achunk, {c1 = c2} + {c1 <> c2}.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "p'0h01Hh11ni001nh21eh37map_begi017map_begh42H0h56absurdh61ci021ch75diseqh88map_sizei038map_sizeh91sh:1xh;1ai041ah<2a0h=2c1h>2H1h?2a1h@2c2p;1p;2p;3p;6p;5g02Z1j10Tg02ZJj24Tg02Zjj22Tg00E0j2>Tg02[ej3=Tg02\Ej39Tg02\ej2<Tg02]Ej6:Tg00icj31Tg006Gj6?Tg02]gj2CTg02^Fj5BTg00H5j3;Tg003`j6ATg02_Cj6@Tg00]`R0f1R1f0R23;p=3g00]BR3?;12p=6P3f4R4f3R5f2R6P1P2EAp=7P0P3P5P6P1P2E@p=5A1561=;02p=81312R7%07'4^:0X=0P01256R7/32R8%08'4P2f6R8/61R9%09R:149:R;f7R</281261R='3R>%0>R?'4W9P9P:f8R@/2<RA/37RB%0BRC'4X9;P5122@1245R;'3RDX63P61242/3;X131>07P<P2D7P@P1D79=BCX<9P5%0DX63125</37RDP1P0P3P2P2f<REn0110400022010210030101103100X20RF124@P;P2C516@5RGf9RH/64RIP2W0P2O1b0O1W5%0DeP@P1D799BCX7:1<81RCE:X;9P1P0P3P2P1PEn0110400022010210030101103100X20PAP7P2C5PGPF12H@RFP;P1C5PGf;RG/68P2W4X0IP2O1b0P2O1b0O1X5>P?e99>?X7:PCE:X13X63P1P2O2A1612,3ARA%0ARCP0PFP0p-0RFP2g027>R:g02_`R?n0110400022010210030101103100X20g027ZR>A1561RIP2E?P?1C?2R;b4X0APCe39X13X83X33P6P1P2O3n0110400022110210030101103100X:0X13X63P0A1456RC/32RA%0A'4P2P<P8f5RA1212C8R7%07R9P0A1@<8P0PFP2P?P:n0110400022010210030101103100X20P>P=P2E?P?P;b4X07P9e39X13X63P1P2O216H6R9%09R71497R;f:R?PHP@PIC8RI%0IR@'4W9P9P7A1G?HR=/3CR>%0>R:'4X9;P9P7A1EG?RFA1A45RB'3RD%0DRJ'4X9;PAP2PEPGA18A4R;C8RKX33P4P8P2PGP;C8RLX83P5P8PAP2P;C8X131>0BP?P2D7PGP1D7PEP6D79=DJX?9PA%0KX33P4%0LX83PAP4P?PBC8RLP1P0P3P2f>RKP2n0110400022010210030101103100X20R5A18AGP;P2C516G4RM16EARNP2W0P2O1b0O1W5%0LePGP1D7PEP6D799DJX771<H6RJE:X<9P4P2PGP?PBC8#0X33P4P?PHPCC8R4P1P0P3P2PKP1n0110400022010210030101103100X20RDA1AG?PBP2C5PMP5A18EGP;P1C5PM16K<R<P2W4X0NP2O1b0P2O1b0O1W5%04ePGP1D799>:X77PJE:X;9P1P0P3P2PKP6n0110400022010210030101103100X20P=PCP2C5PMPDPFPBP1C5PMP5f=?1EGP;P6C5PMf@/6HP2W>X4<X0NP2O1b0P2O1b0P2O1b0O1X5IP@e99I@X77PJE:X13X83X33P6P1P2O3n0110400022010210031101103100X:0X13X83X33P1P2DBX@0X=0o"). Qed.

(* [comment removed for export] *)
Lemma nodup_range_len : forall (l : list Z) (N : nat), List.NoDup l -> Forall (fun k => 0 <= k < Z.of_nat N) l -> (length l <= N)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h01xh11kh24__p1h34__x1h44__x2h51lh61nh71yh81Ah91Bh:1Hh;2H0h<1Nh=7__arithh>4__ffh?4__p2h@8__varmaphA5__withB4__x3hC4cstrhD1fhE3lenhF5starthG2z0hH2HFhI2HkhJ2NDhK1Rp&0p;1p;2p;3p;4p;6p;5p;<p;7p;8p;Bg00@Lj1QTg01?Qk20:Tg00HOR0j15Tg02@NR1j22Tg01>;R2j20Tg001Nj3LTg02`=j2:Tg00Z@j2GTg02`YR3j2FTg000Gj4CTg01J`j31Tg02a3j3aTg02aUk609Tg00H5j3=j1xTg01K7j2\Tg02b0k502Tg02bOR4j1XTg02boj2>Tg02cLj1rTg00E0j2;Tg00[Tl<HTg00L0j1STg02cjj2[Tg00LUR5j2?Tg02:^j2DTg00Ioj1BTg00N0j2@Tg00M1j1cTg00MOj2bTg00NYj3RTg00DPj1`Tg00PWj2_Tg00Q5k108Tg00QSj4^Tg00R1k107Tg00ROk106Tg00S:j2NTg00@lk103Tg00S]k201Tg00UNj1~Tg00VTj2|Tg00W6j2{Tg00Wbj3zTg00XAj4yTg00Y3j4WTg02dLj2JTg02dcR6j2ITg02e;j3wTg00JlR7j2UTg02eVj6nTg02HAj1mTg00T@j3lTg01kMj4sTg02f?j4tTg02fYj3uTg02g2j5vTg02gXj4jTg006Gj6ZTg02h7j2iTg00\9l<TTg00OBj3hTg00Okj2}Tg00EJj3gTg02hVk600Tg00Tcj4PTg00\^j7fTg02i:j7eTg02i^k704Tg00V0j8dTg02jBmB05Tg00c<R8f0R9'?p=<g00]BR:f1R;;=9p=4P:g00^[R<P:P:P4f4R4P0f3R=g02jhf2R>P;P9M<Tp=VP<P:P:P:P0P0f5R?P4P=P>P;P9M<Tp=kA=:98p=OAh:;9p=6g00de,}9p=9g00cZR@?g;9p=7P;g00_^RAg00`=RBPBg00`]RCP9J00p=]P:P;g00eQP9CPp=MP;PAPBPBPCP9g00a=Ffp=3P>PAPBPBPCP;P9Fep=8P:P;g02kUP9CPp=AP>PAPBPBPCP;P9K04p=YP=PAPBPBPCP>P;P9Gdp=EP<P:P3P0P5g02l<g00dFR5P8P=P>P;P9M<Hp=qP<P<P<P:P:P:g02l^P0P0P0P7g02m>P5P8P=P>P;P9NB05p=pP<P:P6P0P1g02maP?P4P=P>P;P9M<Hp=oP:P;g02nCP9CPp=K%Q:20::;%<9R1%5>,29'0X1:=L:>P<1:5>R6,G<R71G:4/F9R3X<<P<P<P:P0P6CCRA,G:P3X6<P:P=PAP;A1:94%5?,29,01X1:R3=L:?f7RD91:9f8RE#5,29,01X1:P;O1[^0:[f6RF91:9%5DRG,29,01X1:P;O1[^0:%5FRH,29,01X1:=L:F[Aa:3?P>P;P9J09P3P;O1g02njR3p4p710R1P3p4p7210R3P;\;RI%Q>RJP2P4P=P>P;CC91=9P4P9O1==?>A1F9='0X0?,\?RK[P=P9O1==4;A1?9>'0X04,\4P?P4P=P>CC914;[RLPFP?P4P=CC91?>\KP4P=P>P;P9I02P9n2001000000120000000X7>W5WDW9W8PL^7>^5J^DI^93^81P9P<P:P01:5FR1P=P<%59R3/441:5D91<9'0X0<%X=RI%5IRJ/4=RLA1<I1PL1>8=RL/4=P:P:%x:R1P9X0:RKP114;9#rX7:X0:PJPLPKPK1;:3X0<PIPLPK1>89X0:RLP=P=1;:=RIDVEkP=P=PIM<H%SF%<H1[8412841>84RH/44'01?48%OH'0'D1>8?RIP:p-0R3%B5RJ#BR1,@:RM1@:J1@:5RJ'6RN'6RO#9%B1R1,@:RPg00bWRQ#c,b:RR=R:M/6JRM'6#9%9M%`@RM'7'7'7%Q@R@P:1_:>RSP;&08:C^&07:RT&06:RU1]U41N:QRV&03Q,N:RW'M,3URX58U201:8RY,AW,3U1MVY,3URZ58U5YU%~BRBPU1AYW,3U1]U?R[58UPBPXCECE1|UCRCP9P>g00f8RXg00fXR\';1{9>==X\dAz:8;CyR\b>b@bAX3:X4:X23W?149;,0>1?;8%O9RX'0'D%<>R]/0414>=[[^3:^4:^23^?3P9f:#5,2D128DPDP;P>P?O6b=bGb;bCCWP21:;>91<91F>;1J>=,I;'0R2[1F;91J;>,I9'01:>=91<;[R^1:=491<>\2Aw>;9P9n2001000000120000000X6<XF<XE<P^^6<^F<^E<P9PDP5%X4R^1F5^R21J5DR_,I^R`'0%<HRa1U8GRb,2HRc'0P2P`PaPc1;:8RcP^PHPKPLP4P41;:4DVR4CqP^PHP4P_PbPcPDPG1;:GCpEoEn%SD%<G1[8?128?14I?'01??8%OI'0'D1>8FP:16PO#9AR:RP/6JRJ#9%B1,@:/6J#916PN#9/7M'7'7'7P@P:PSP;1_:=C^PTPU%mQ,N:RQ,KY,3U1MVQ,3U58UA8U[Z5YUPBPU1AYQ,3U1KQW,3U58UPB1AYV,3UAl:YW,KV,3U58UCECEPCP\b>b@bAX3:X4:XB:X23128>149>'010=X'D%<=12=>'01U8=,2>,0][[^3:^4:^B:^23P91?E8PEf;#5P;P>PFO6b=bGb;bCCWO4b:CsCtO6b:bKWIX1:Au:=AeDvP7P<P:P0P6CjEZP>1i>5EZWHWJX<<W5o"). Qed.

(* [comment removed for export] *)
Lemma tmp_len_bound : forall R L st X m, alayout_ok L -> awf L st X -> AQdr R 0 0 L st X m -> Z.of_nat (length (qr_tmp R)) < 2^32.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "p'0h01kh11bh21Hh31ch41zh53LENh61nh72G1h82G2h94__p1h:4__x1h;4__x2h<4__x3h=4__x4h>1xi001xh?2KRh@2_HhA3_H0hB3_H1hC3_H2hD7__arithhE4__ffhF8__varmaphG5__withH1AhI2G3hJ1PhK3_H3hL3_H4hM4__p2hN4__x5hO1lhP3ALOhQ2BShR2CPhS2CbhT2H3hU2HbhV2HkhW2KbhX1LhY4LEN0hZ3NDBh[1Rh\2Sbh]2WFh^1Xh_3_H5h`2bbha4cstrhb5cstr0hc5cstr1hd5cstr2he1ehf1mhg2sthh2z3p%0p&0p&1p;1p;2p;4p;7p;6p;3p;8p;Bp;<g00@lj15Tg00AQk10VTg00Aok10eTg01]ak11VTg0286k21ETg0295k417Tg01khk70}Tg01^Ck10gTg01_Aj1uTg015Dj1]Tg014Lj1?Tg01`=k103Tg01a<j6nTg00C8k20[Tg001ok21ATg00ogj16Tg01@fk214Tg00JNj1VTg02oGk20yTg00nik40:Tg0176k106Tg0180j1wTg018jj2dTg001Nj3MTg01?Qj2RTg019fj14Tg01;Wk10?Tg01<Lj11Tg01=Dj1<Tg00GUk41@Tg00H5j3YTg01>;R0j20Tg01Fok101Tg02HAj1kTg02bOR1k10{Tg00@Lk10hTg01J`j3UTg02a3k30zTg00HOR2j1CTg02aUk40xTg02?Nk80wTg02@Nj2[Tg02A_j28Tg02BVj2ATg02CNj2;Tg02DHj17Tg00JlR3j23Tg02EKj1>Tg00LUR4j22Tg02FHj1=Tg029hk10vTg02GHj1JTg02Hfk10FTg02odj2mTg006Gj6OTg02@jk20aTg00Iok104Tg00N0j2|Tg030Ak21UTg030jk31TTg00Okk20uTg00DPk11STg00EJk30tTg00PWk20_Tg00Q5k11RTg00QSk40;Tg00R1k11PTg00ROk11OTg00S:k205Tg00S]k20BTg00UNk11NTg031Sk31MTg00Tck40KTg00VTk21ITg00E0k200Tg00W6k21HTg00Wbk31GTg00XAk41FTg0326k21DTg003`k61CTg032Tk41BTg02`YR5k20@Tg016=j1vTg010_j1^Tg002Lj3zTg02dLj2GTg033Wk30ZTg02gXk40pTg00Z@j2_Tg02bok20jTg00KIk41<Tg00L0k10MTg02cjk219Tg02:^k20nTg02i^k718Tg0346k31:Tg01l^k315Tg01gXk11?Tg000Gk40LTg01hXk40mTg01E@k10rTg01iQk20lTg01b4k10`Tg01bkk10XTg01Ifk10NTg01:ak10kTg01K7S00k20PTg01KQk20QTg00OBk313Tg00\^k70sTg02i:k71JTg00T@k31KTg02hVk61LTg00V0k811Tg02jBmB10Tg00\9m<1QTg00[Tm<0~Tf0R6#5#5p>0Dg00c<R7>1567p>0Gf4R8f3R9g01oKf2R:$06f1R;#v&1?6Enp=fP:g01LdR<P;P6H0Lp=Bf5R=P8P9P:g01KjR>P;P6H0LH0mp>02f7R?$0rf6R@+0lP=P8P9P:H0:&0`;&0X6'0'0'0p=S10;6,0:,09,08p={%6;,_:#C/[6p=DP:P>P;P6H0Lp=TP8P9P:P;H0m/06p>0H10;6,0:p=H&0r;00l6p>0fP=P8P9P:H0:&0`;&0X6'0'0p>0d&0`;&0X6'0p>0c1_>6p=@1_<6p=yg00^[RA?Y;6p=t%v6,_>p=b&0N;&0165z:p>0Cg00]BRB/R6p=xg01QBRCg01R:7Y6p>0Ag01S2RD9YB6p=qAYB;6p=Xg01M_RE&0k;7U:/06p=:AUB:;20PE6+0Qp=N1d9:$0N&01;5z89U@=20PE6+0Qp=L1276p=IAMB;6,0:,09p=a&0k69UE;p=j1RB;/06p>0O20PE6p>0^&0N:&01;5z99U=800Q6p>12AMB;6p>0R1d:;$0N=z96p>0WAU9:;20PE6+0Qp>0|AMB;6,0:p>0i%56#5#5#5#5#5#5#5p>0>1[;6,0:p>0J%469UB;p>0U127:1[;6'0p=PAYB;6,0:p>0I20a;6,[:p=Z&0F6,3;p=F1289g02J`RF,2:'0g02K`RG,3;g02L[RH,36'2'0p=\%56#5#5#5p>0<%k6#kp=g13;6,2:p=912?@12=8139:/2;/06'0'0p=E128910:;/06'0p=p108912:;/06'0p>0T129:/0;/06p>0912:;/06p=i127;/06p>08128912:;/06'0p>0b139:13;6'2p=h%7;/26p>0713;G136H'2p=l12;F,0:/06p>0S126Fp=~PBP9P:P;PDP6EOp>0E1;6Dp=r1m;6,3:p=s186Dp=WB13B;6p=eP:g00_^S01g00`=RFPFg00`]RHPBP;g02kUP6H0Kg00a=RGK0sp=QP:Q01PFPFPHP;P6K1Jp>0=B1KB;6p=}P;Q01PFPFPHP6J1Lp>0]P;Q01PFPFPHP6PGK0sp>0\P9Q01PFPFPHP:P;P6L11p=`1_B6p=KAz>;6p=oP>PBg01F7S02P6H0Lp>0q1G:;00@6p=c%66,_;p>0oPAPAPAPBPBPBg02l^P2P2P2P3g02m>P=P8P9P:P;P6NB10p>0YPBPAPBPBP1P8P2P9g02jhP:P;P6N<1Qp>1>PAPBP5P2P4g02l<P=P8P9P:P;P6N<0~p>1=13:;/26p>1;1_;6#Cp>16g01PHg00a]g01NVg01OQg00bWR4#5R2#5S03#5R5$0DS04#5R1$0V$0e&0V5$0e$1V[p,2rcR501E9P5P8P9P:H17P@P7P7P=P8P9P:K0}P0&0g9&0G9P@P9%u@%]=%??&03=EnP@P9P=P?P=DfP@P920[<>R321A<>RG%6?RI3BRJP3214<>R<PIJ02P?P9P@P=P8P?P=PJGSD{f8RJ%V2S05Q04#V+0yRI5D3P6&0g=&0G@f9RKP@%uK%]Jf:RL#?&03JEnPKP@PJPLPJDfPKP@%6LRM9B3GRNP3P<PMJ02PLP@PKPJP?PLPJPNGSD{P0&0G?PLP?%uL%]Kf;RN#?&03KEnPLP?PKPNPKDfPLP?%6NRM9B3GROAT3<MPNP?PLPKPJPNPKPOGSI0H3Hf<RO=D3IP6&0GKf=RMPL%uM%]Of>RP#?&03OEnPMPLPOPPPODfPMPL%6PRQ9B3GRRAT3<QPPPLPMPOPNPPPOPRGSI0H3HP0PPPN%uP%]Mf?RR#?&03MEnPPPNPMPRPMDfPPPN%6RRQ9B3GRSP3P<PQJ02PRPNPPPMPOPRPMPSGS3Hf@RS=D3IP6PSPM%uS%]RfARQ#?&03REnPQPPPSfBRTPSDfPQPP%6TRU9B3GRVP3P<PUJ02PTPPPQPSPRPTPSPVGS3HP0PTPRPQfCRVPQDfPTPR%6VRU9B3GRWAT3<UPVPRPTPQPSPVPQPWGSI0HfDRW=D3IP6PWPQPVfERUPVDfPUPTfFRX#6RY9B3GRZAT3<YPXPTPUPWPVPXPWPZGSI0HP0PXPVfGRZ#6RY9B3GR[P3P<PYJ02PZPVPXPUPWPZPUP[GSfHR[=D3IP6P[PUfIRY#6R\9B3GP3P<P\J02fJR\PXPYP[PZP\P[%6\9B3GGSP0fKR]00fZP\PYP[P]PY%6]9B3GJ0dfLRZ=D3IP6fMR^00fYP^PZP]fNR]PZ%6]9B3GJ0dP0P]P^PZfOS06H0:Q06#69B3G-0c^fPR_=D3IP6P_Q06P]fQR`H0:fRRa#69B3G-0c_P;PaP`P_fSS07H0:P0fTRG#?#@%]a#y't%bG&06a#y'tg00]`00[BRb%w`1daGRc3M20[BBRdB0CdcG'R%4GRc#xfURe#4Q07&0?6Rf$0ARg%16Rh#qRi%<6Rj/X;Rk3HRl5:6X1E5N6^0BPdPBPBP;P6H1@RmPdPGfVRnPng01T29YCf1Xh:;HkRk9:6GX1EFL^0B^3B%I6S08X0BRhPcCaD{AD3eIP6%?n#@%]G#y'tfWRc#b&06e#y't%wG1decRf5MbB0Cdfc,Rd%4cRf#xfXRC#4RoA:6nlX1E5N6^0BPdPmPdPcfYRpPp1j6cRq/0kX1EFL^0B^3BPhPfCaD{P0%bC&06n#y't%we1dnCRf5MbB0CdfC,Rd%4p10qlX1E5N6^0BPdPmPdPCfZRqPqA:6CkX1EFL^0B^3BPhPoCa-0Oo3HAD3pIP6%bq&06C#y't%wCf[Ro,dpRf5MbB0Cdfo,Rd%4oRff\Rr#4RsA:6qlX1E5N6^0BPdPmPdPof]RtPt1j6oRu/0kX1EFL^0B^3BPhPfCa+0O3HP0%wp1dqrRf5MbB0Cdfr,Rd%xs%4t10ulX1E5N6^0BPdPmPdf^Ru,drRfPuA:6rkX1E$0^J12^0B^3B20RhsD{AD3tIP6%wo=MbfPdPtf_Rf&01fH0W,Rd%4fRb#xf`Rs#4RvA:6ulX1E5N6^0BPdPmPdPffaRwPw1j6fRx/0kX1EFL^0B^3B20RhbD{P0PdPuPs&01sH0W,Rd%4w10xlX1E5N6^0BPdPmPdPsfbRx&01xH0WRbA:6skX1EH0|^0B^3BPhPvCa-0OvAD3wIP61RdbfcRb#4RwfdRv#4RyA:6xlX1E5N6^0BPdPmPdPbfeRxPx1j6bRz/0kX1EFL^0B^3BPhPwCa+0OP0%xy%4x10zlX1E5N6^0BPdPmPdPvffRzPzA:6vkX1EFL^0B^3BPhPyCaAD3xIP6%4z#xfhRy#4RwA:6zlX1E5N6^0BPdPmPdfgR{fiR|P|1j6{R}/0kX1EFL^0B^3BPh%4{CaP0%4|10}lX1E5N6^0BPdPmPdPyfjR}P}A:6ykX1EFL^0B^3B@0ihwAD3|IP6fkRw#4R}A:6|lX1E5N6^0BPdPmPdPwfmRlPlA:6wkX1EFL^0B^3B@0ih}P0PdPmPdflR}fnRwPwA:6}kX1EFL^0B^3B%4}-0RhAD3lIP6PdPmPdPwfpRdPdA:6wkX1EFL^0B^3Bfo#4-0Rh%4dS09%k4S0:#k$0>$0>S0;#VRd$0{RhPKg034Yp4p710Rwp-0Rk\6Rm&0h;RlP0AM:;6AU86:P8P;O1[^>9R}[AU96;P9P;O1[^>:AM9:;[R~AM89:\}B0z:;6P6n2001000000120000000WOWJWHP~^Ol^Jm^HwP6PBQ08%ChRw80J6X0BfqRm#4frRl-0U6fsR~-0U;1Xj99Hgi9:6lX1ES0<$0^[1Xj:9Hgi9:6mX1E$0^S0=ftR}-0U:[PJP;O1P6H0xQ0=Q00PEQ0<%I9S0<@0J9wP61Xj=9Hgi9:6}P0fuRi,j;&0?;$0A%1;#q%<;/X@3HAP??wP6fwS00,j9&0?8$0A%18#q%<8/XK3HP0&0?=$0A%1=#q%<=<0ILAPNNwP6&0??$0A%1J#q%<J<0IMP0%1K#q%<K/XPAPRRwP6%1N#q%<O/XQP5p+01DROp+01CRNp+01Bp+01@f~RRPMPKL0w%V4S0=%1MRLg02MZS0>,[L%<MRg#IAZgNL18OLRg1AOMRM1FMLRj1;NLRL#7RN,3g%>OS0?/2gPN%=LRLPLPgQ0?D\&0D1$0<R1#5S0?#g#g#g#g#g#g#g#g#5$0D$0<$0>#VRgPMPj&0v5R5%JORL%V1R1PMQ0?#5$0D$0<#k#5$0D#k$0<$0>#VRM99jLGEDpI0TH09P0Q0=%1PRLQ0>,[L3i%<PRj#IAZjOLp+01ERj/8LRN1AjPS0@Q0@/FLS0A1;OLRL#7RO,3N%>jS0B/2NPO%=LRLPLPNQ0BD\PgQ0@Q0AP5%JjRjP1Q0@Q0A?9jMGEDpI0TAPWWwP6Q0=%1SRSQ0>,[S3i%<QRS#Ip+01GRj%1QRN5ZSp+01HRS/8NRL1ASQRQ1FQNRO1;jNRN#7Rj,3L%>SS0=/2LPj%=NRNPNPLQ0=D\PgPQPOP5%JSRLP1PQA9OLMGEDpI0TP0%<TRL%1TRO9ZLS+08p+01IRL/8ORQ1ALTRT1FTORN1;SORO#7RS,3Q%>LRjPQPS%=OROPOPQPjD\PgPTPNP5%JLRLP1PTA9NLMGEH09I0bAP[[wP6%<WRLp+01J%1W5ZL+08p+01LRL%1URW'8RN1ALURU1FUWRTp+01K/;WRW#7Rj,3N%>LRQPNPj%=WRWPWPNPQD\PgPUPTP5%JLRQP1PUA9TQMGEH09I0bP0p+01MRQ%1XRT'8RU1AQXRX'21FXTRN1;LTRT#7RL,3U%>QRW/2UPL%=TRTPTPUPWD\PgPXPNP5%JQRQP1PXA9NQMGEDpAPZZwP6p+01ORQ%1['81AQ['2p+01PRN/AYRX%1YRY'FRW18NYRU1;QYRY#7RQ'3%>NRT/2UPQ%=YRYPYPUPTD\PgPXPWP5%JNRTP1PXA9WTMGEDpP0p+01QRT/A\RW%1\R\'FRX18T\RU1;N\R\#7RN39%>TRYPUPN%=\R\P\PUPYD\PgPWPXP5%JTRTP1PWA9XTMGEH09AP__wP6p+01SRT/AZ%1ZRZ$0F18TZp+01R/;Z#7Chp+01TRZ#>RX%1^RW,8ZRY1;TWRT%=TRT+071lYX80STPg1AZ^R^1F^WRWP5%JZRTP1P^A9WTMGEH09P0p+01URT#>RW%1]R^,8TRY1;Z^RZ%=ZRZ+07%~Z1lYWDpPg1AT]RY1FY^R^P5%JTRTP1PYA9^TMGEAPGGwP6p+01WRT#>R^%1_RY,8TRWp+01V/;YRY%=YRY+07%~Y1lW^DpP0p+01XRW#>R^%1`RY,8WRW'21;TYRY%=YRY+071lW^80SYPgp+01YRY/AaRW%1a,FWR^P5%JYRYP1PWA9^YMGEAPCCw[P6p+01ZRY#>Q07#1,8Y'2%1GRG,;YRY%=YRY+07p+01[R^/8G%>^'l80SYP0%1eRe,;^R^#7%=^R^%~^3ip+01\R^/8e%>^'lPgp+01]R^/AnRe%1n,FeRnP5%J^R0P1PeA9n0MGEAPrrw[P6%1c,;^R^#7%=^R^%~^3ip+01_R^%1C'8%>^'lPgp+01`Rg/ApR^%1p,F^RpP5%JgR5P1P^A9p5MGE%1qp+01aRq/;6R5#7%=5R5%~53iX4BP:P]H0E%rgRg#7%=gRg%~g3i%1op+01cRg/86R]%<rR5&0F6Rp3sPpP]p+01bR]/;6#7ChX4BPPQ06H0E%W]R]%<o&0FDRo3sPoP]%rq#7Ch%1rp+01dRr/86Rq%<tR]/mp79qX4BPVP_H0E%WgR_1m5o79_%1t%<uRuAZur6+08X4BP[P`H0EAZ]gD-08]PBPup+01fRu#WR]1m6oRg'3PoP]p+01eR[#r#7ChX4BP:PbP`EO%W[R[?sboPoP[%rr#7ChPB%<fp+01gRf#WRr?9rgX4BP:PvPaEO1mvo99]]PB%<sQ0820afD80J6X4BP:PxQ07EOAZxuD-08xPBPop+01i#WRx?s{6P6Pxp+01hRu#r#7ChX4BP:Q0?#VRsg02NZR]EO%WuRu?szsPsPu%rf#7ChPBPop+01jRo#WRf1my679fX4BP:PsP]EO1m{s99xxPBPdAP||6X4Bg00cZRxg00dFR{$04R]$04Rf$04Ry$04Ru,|BRz1|ByRy1|BfRf21UBs1|B{R{61TB'e'e'eg00deRv+0u&1SxRa40t&0hxRrPBPB20_B9P8&1RBRgH0;P;PB20_B8P:PgH0;R[H0;&1PBRb&1OBR`Q03-05BRt%k2-05BR_5Q`Q0;#5$0<$0>#VR5-0BB9Q`_60=`&1NFRVP`Q0:-05BRq205B4R420BBsRp61MB'}/}p1}qt5Q`PVP`20BB7Rp=Q`4RP20]`@60=`PVPBP4g02nCRM20BBdR^H0K-0\`:0=`PC`C`C`21I`HRPP6P:g00f8R1g00fXRC+0021H6:=Y1CdB1GB7;H1FRCbEbFbGX:BX;BX<BX=BX9k12959i:9As:;sPsP:P9Ch%I:Rs/0@Q0<@0J9d[[[^:B^;B^<B^=B^9kP6AZ|oD%roRo#=%7op+01k#WP|PKP:P9O8bDPwPaPrPgPbAQ`p^PPPCbEbFbG%IdP6bD-1DdJ1Cb7b8b?b7b8b?b7b8bIWCWBWIP;P6O2n2001000010121000000W2WAP;P6O2n2001000010121000000W2P;P6O2n2001000000121000000W2W8P;P6O2n2011000000121000000W2W7P;P6O2n2011000000121000000W2W?P;P6O2n2011000000121000000W2W@P;P6O2n2011000000121000000b2WWWSP;P6O2n2001000000121000000W2W\P;P6O2n2001000000121000000W2WUP;P6O2n2001000000121000000W2X`EP;P6O2n2001000000121100000beWVX0BO4b2H1BQ09#K00@hPA%?m%vm%6m9T3<'o'o$0qRE%^mRm5zB#K20@6hX6AP6%KE%Km'GRwB0ZBEmEO20@whPA%?l%vl%6l9T3<'o'oRw$0q#K%^~#KRm=c6hX6AP6%@wREP>PBQ02PwH0pEO%^l#K=cEhPA%?~RE%v~%6~9T3<'oR~'o#@%^}#KRl=c6hX6AP6%@E%@~'GRwB0Z>E~EOAcwmhPA%v}Rw%6}9T3<Rm'o#@%?i#@R~/G6%^i#KRE;chX6AP6%@w%@m'GRKB0Z>wmEO%?}#@/GK?clhPA%6iRl9T3<#@fvRK#?#@R}%bKRm/G6'G%^K#KRw;chX6AP61_3lRAP3P>P<PlH0pEO%bi/GA,G~?cEh20o3KRK,GmRE,G}R~/GwRA00@h%C}Ri%CmRl%CKR<'3R>'3R|%CwRo'3RD20j7dR5'2R1PAPDP~P|P}Pi200BiPEP>PmPl200BlPKP<200B<J0YJ0YPwPo200BoJ0YPh20j76X>BRhPdO1P6X>BPhPdPd200BdI1>J1=P6H1<P1Q00#^#KR1$0M%C1#Ifx-0o3R1$0M%C1#Ify#bR1$0M%C1#Ifz#?#@R1$0M%C1#I2197d1[7dR1@0I5d12d7RhAYB57'0+0nP5PB&04u,|B1|B]/e{,ef,ey,ez'e00uv>0txaPrPBP[P;PB20_B=P9PgH0;H0;PbP`P`Q01PFPFPH20]`?PBP_g00eQP^H0K-0\`60=`AQ`^p20]`J60=`K18PVP`205B2R29Q`pPVP`AQ`pqPVP`AQ`ptPVP`1}q4,}2/}t=Q`_PVPBP4PMQ05-0BBQ04$0V61:BH0K-0\`C`C`C`C`C`PPPCbEbFbGX:BX;BX<BX=BXNBX9kXMkB0I=8d10h@+0n%I8%I@13@8,3=@1;?J1[=I[[[\s[^:B^;B^<B^=B^NB^9k^MkP6AYB;7P1P;%^R#K#C%bR#C%?R#@#C%6R-163P:P9P8P@P?O<bDbhbTbdbcbbbabYb5b5b5b5b5b5WLWKP;P6O2n2001000000121000000W2WQP;P6O2n2001000000121000000W2WZP;P6O2n2001000000121000000W2WCP;P6O2n2001000000121000000W2WBP;P6O2n2001000000121000000W2WAP;P6O2n2001000000121000000W2W@P;P6O2n2001000000121000000b2W_WRP;P6O2n2001000000121000000W2WLP;P6O2n2001000000121000000W2WKP;P6O2n2001000000121000000W2WCP;P6O2n2001000000121000000W2WBP;P6O2n2001000000121000000W2WAP;P6O2n2001000000121000000W2W@P;P6O2n2001000000121000000W2W]WPWfW^WgWXW[o"). Qed.

(* [comment removed for export] *)
Lemma AREP_reqs : forall AQ AQ' AS AS' ADp AFp L st X m,
  AREP (mkAHoles AQ AS ADp AFp) L st X m -> AQ' L st X m -> (AS L st X m -> AS' L st X m) -> AREP (mkAHoles AQ' AS' ADp AFp) L st X m.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h01ch11Hh22A1h33A10h43A11h53A12h62A2h72A3h82A4h92A5h:2A6h;2A7h<2A8h=2A9h>3ADph?3AFph@2AQhA3AQ'hB2AShC3AS'hD2HQhE2HShF1LhG1XhH1mhI2sthJ1xhK2x0hL2x1hM2x2p;1p;4p;6p;2p;3p;5g00@lj1ATg00AQj1MTg00Aoj1KTg01]aj1PTg00@Lj1UTg0356j40Tg035nj66Tg0295j4ITg036bj2BTg037Yj3=Tg038Rj4;Tg00JNj1OTg00LUj2NTg02@Nj2TTg01>;R0j21Tg039Ij5:Tg03:Ej42Tg03;Bj5<Tg03<9j5ETg03<oj3FTg03=gj1CTg03>]j1?Tg03?Uj1>Tg01kMj4HTg03@Mj5QTg03ACj5RTg03B=j4STf5R1f4R2f3R3f2R4f1R5DQf0R6'1p=8P1P2P3P4P5DR/16p=7P2P3P4P5CS/16p=9f6R7?F12%C3%?4%>6,15'1'1'1p=3P1P2P3P4P5DE/16p=5P1P2P3P4P5D</16p=@1156,14p=4%>6,15p=G%C4%?5/16'1p=J%?4%>6,15'1p=LP7P1P2P3P4P5P6CHCHp=Dg00a]R8g01NVR9g01OQR:g00bWR;#A#A#AR<#A#A#A#M#K%M<#K#P[R<p-0R=[R>[[[R?P=^M<^L:^K9^J8R=P>\8g03C:#UP>[\8p,2rcR>f9R@f7RAP1P2C0P3P4P5P6E6P0P>P2P3P4CI1B25A=235P2P3P4P5C;g00]BRB%O;/N6g02MZ,T6'1R;P7P1P3P5P7P1P2P3P5P7P1P2P3P5P7P1P2P3P5D:E8E7D9[]0f:RCf8RDP7P1C0REP2P3P4P5PEP2P3P4P5PEP2P5P5P5P7P1P3P5C2\;^0BP5F3E5E@3434PCP1P2P3P4O4PCP7P1P2P3O4PCPAP7P1P2O4[P>f<REPCP@PDC0PAP7P1P2E6[[P6P>P7P1P2CI1BA2A=A72PAP7P1P2C;P@PDP7P5P@PDPAP7P5P@PDPAP7P5P@PDPAP7P5D:E8E7D9\;^0Bf=RFf;RGP@PDC0RHPAP7P1P2PHPAP7P1P2PHPAP2P2P2P@PDP7P5C2\;^0BP2F3E5E@3434P01BD1A=DA1PDPAP7P1C;PCP@PAP5PCP@PDPAP5PCP@PDPAP5PCP@PDPAP5D:E8E7D9\;^0Bf>R2PEPCP@C0RHPDPAP7P1D<PHPDPAP7P1PHPDP1P1P1PCP@PAP5C2\;^0BP1F3E53434P2P@PDPAP7O4P2PCP@PDPAO4P2PGPCP@PDO4[P>f@R7P2PFPEC0PGPCP@PDE6[[P61BCAA=GCDPGPCP@PDC;PFPEPCP5PFPEPGPCP5PFPEPGPCP5PFPEPGPCP5D:E8E7D9\;^0BfAR1f?RHPFPEC0RIPGPCP@PDD<PIPGPCP@PDPIPGPDPDPDPFPEPCP5C2\;^0BPDF3E53434P0A=EG@PEPGPCP@C;P2PFPGP5P2PFPEPGP5P2PFPEPGP5P2PFPEPGP5D:E8E7D9\;^0BfBRDP7P2PFC0RIPEPGPCP@PIPEPGPCP@PIPEP@P@P@P2PFPGP5C2\;^0BP@F3E5E@34PDPFPEPGPCO4PDP2PFPEPGO4PDPHP2PFPEO4[P>fDRCPDP1P7C0PHP2PFPEE6[[P6A=2FGPHP2PFPEC;P1P7P2P5P1P7PHP2P5P1P7PHP2P5P1P7PHP2P5D:E8E7D9\;^0BfER@fCRIP1P7C0RJPHP2PFPEPJPHP2PFPEPJPHPEPEPEP1P7P2P5C2\;^0BPEF3E5E@34P0P7PHP2PFC;PDP1PHP5PDP1P7PHP5PDP1P7PHP5PDP1P7PHP5D:E8E7D9\;^0BfFREPCPDP1C0RJP7PHP2PFD<PJP7PHP2PFPJP7PFPFPFPDP1PHP5C2\;^0BPFF3E534PEP1P7PHP2O4PEPDP1P7PHO4PEPIPDP1P7O4[P>fHR2PEP@PCC0PIPDP1P7E6[[P6PDP1P7PHC;P@PCPDP5P@PCPIPDP5P@PCPIPDP5P@PCPIPDP5D:E8E7D9\;^0BfIRFfGRJP@PCC0RKPIPDP1P7D<PKPIPDP1P7PKPIP7P7P7P@PCPDP5C2\;^0BP7F3E534P0PEP@PIP5PEP@PCPIP5PEP@PCPIP5PEP@PCPIP5D:E8E7D9\;^0BfJR7P2PEP@C0RKPCPIPDP1PKPCPIPDP1PKPCP1P1P1PEP@PIP5C2\;^0BP1F3E5E@P7P@PCPIPDO4P7PEP@PCPIO4P7PJPEP@PCO4[P>fLRDP7PFP2C0PJPEP@PCE6[[P6P2PJP@P5P2PJPEP@P5P2PJPEP@P5P2PJPEP@P5D:E8E7D9\;^0BfMR1fKRKPFP2C0RLPJPEP@PCPLPJPEP@PCPLPJPCPCPCPFP2PEP5C2\;^0BPCF3E5E@P0fNRCPDP7PFC0RLP2PJPEP@D<PLP2PJPEP@PLP2P@P@P@P7PFPJP5C2\;^0BP@F3E5PCPFP2PJPEO4PCP7PFP2PJO4PCPKP7PFP2O4[P>fPREPCP1PDC0PKP7PFP2E6[[P6PEPCPDPKC0P7PFP2PJD<fQRJfOR@P1PDC0RLPKP7PFP2PLPKP2P2P2P1PDP7P5C2\;^0BP2F3E5P0fRR2PEPCP1C0RLPDPKP7PFDEPLPDPFPFPFPCP1PKP5C2\;^0BPFF3P2P1PDPKP7O4P2PCP1PDPKO4P2P@PCP1PDO4[P>fTR7P2PJPEC0P@PCP1PDE6[[P6P7P2PEP@C0PCP1PDPKDEfURFfSRLPJPEC0P@PDPDPDPJPEPCP5C2\;^0BPDF3P0fVRDP7P2PJC0?FE1P2PJP@P5C2\;^0B/G19J11PDPJPEP@PCO4PDP2PJPEP@O4PDPLP2PJPEO4[P>fXRCPDPFP7C0PLP2PJPEE6[[P6PCPDP7PLC0?F2@PFP7P2P5C2\;^0B/GE9JEEP0%CJPDPFPLP5C2\;^0B=LJJfZRJPFP7PLP2O4PJPDPFP7PLO4PJfWR2PDPFP7O4[P>f\REPJfYR1PCC0P2PDPFP7E6[[P6%CLP1PCPDP5C2\;^0B=L77P0%?FPJP1P2P5C2\;^0B/GFf^RFP1PCP2PDO4PFPJP1PCP2O4PFf[RDPJP1PCO4[P>f`R7PFf]RMPEC0PDPJP1PCE6[[P6%?2PMPEPJP5C2\;^0B/GCP0PFPMPDP5C2\;^0B%>1fbR1PMPEPDPJO4P1PFPMPEPDO4P1f_RJPFPMPEO4[P>fdR0P1faRCP7C0PJPFPMPEE6[[P6P7PJPMP5C2\;^0B%>EfeREP7PJPFPMO4PEPCP7PJPFO4PEP1PCP7PJO4[P>P1PCP7CI1B1JR>A=1CJRFP1PCP7PJC;RMP0fcRNPCP5P0PNP1PCP5P0PNP1PCP5P0PNP1PCP5D:E8E7D9\;^0BROfgPEP0PNC0REP1PCP7PJD<RPPEP1PCP7PJDER7AFE1JRE%CJR1%?JRQP0PNPCP5C2\;^0BRB%>JRJ'1R;'1RC'1RN'1R0'1RR'1RS'1RT'1RU'1RV'1PDP>PVP2PFPUPLPMPTP@POPSPKPPPRP5P7P0P6PIO1PEPNPHP1PCPGPQP;PAPBPJP3P4CHFDFDFDFDFDWEWDW5W4P5P6O2n2001000000121000000W1W3P5P6O2n2001000000121000000W1W=P5P6O2n2001000000121000000W1W<P5P6O2n2001000000121000000W1W;P5P6O2n2001000000121000000W1W:P5P6O2n2001000000121000000W1W9P5P6O2n2001000000121000000W1W8P5P6O2n2001000000121000000W1W7P5P6O2n2001000000121000000W1W6P5P6O2n2001000000121000000W1W2P5P6O2n2001000000121000000W1XH<XG:XI9XF8W?W>XC=XB?WAW@o"). Qed.

(* [comment removed for export] *)
Lemma high_fake : forall L iv, alayout_ok L -> ATOP <= fst iv ->
     (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
  /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
  /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
  /\ (snd iv <= 0xb14e0 \/ 0xb14e0 + 8 <= fst iv) /\ (snd iv <= 0x5ea908 \/ 0x5ea908 + 16 <= fst iv)
  /\ (snd iv <= 0x5ea918 \/ 0x5ea918 + 8 <= fst iv) /\ (snd iv <= 0x5ea938 \/ 0x5ea938 + 8 <= fst iv)
  /\ (snd iv <= 0x149531 \/ 0x149531 + 1 <= fst iv) /\ (snd iv <= 0x147418 \/ 0x147418 + 4 <= fst iv).
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"] "h04__p1h14__p2h24__x1h34__x2h47__arithh54__ffh68__varmaph75__with84__x3h94__x4h:4__p3h;4__p4h<4__p5h=1Hh>2H0h?2H1h@3H10hA2H2hB2H3hC2H4hD2H5hE2H6hF2H7hG2H8hH2H9hI4__p6hJ6__sat0hK6__sat1hL4__x5hM4__x6hN1zhO3ALOhP2ARhQ3H11hR3H12hS3H13hT2HIhU1LhV2ODhW2OFhX2SFhY2ivhZ1qh[2q0h\2q1h]1rh^2r0h_2r1p%0p&0p;2p;1p;3p;4p;6p;7p;8g00C8k20RTg0286k20QTg029hk10CTg00LUj20Tg03D3k30KTg03Dmj14Tg00@lj11Tg02HAj16Tg03Eek301Tg03F\k30MTg03GVj1?Tg00JNj1STg03HPk10GTg01>;j22Tg03INj2@Tg00Jlj23Tg03Ikk10@Tg03Jdj2\Tg02Z1j1xTg02odj2OTg03KEj25Tg03Kej2^Tg02@Nj27Tg03LLj2dTg03M3j2eTg03MYj2[Tg00Ioj1TTg00M1k10PTg00MOk20OTg00NYk302Tg030Ak20NTg00N0k200Tg030jk30LTg00Okj2mTg00DPk10JTg00EJj3lTg00@Lk10ITg00R1k10HTg00ROk10FTg00S]j2}Tg00Tcj4cTg00UNk10DTg03N?k60BTg031Sj3|Tg00S:j2{Tg00VTk20?Tg00E0k20>Tg00W6k20=Tg00H5j3sTg00Wbk30<Tg00XAk40;Tg03Ncj2rTg03OXj2qTg03PMk10:Tg003`j6yTg03QKj1fTg03RCk109Tg03S@j2vTg03T1j2zTg00Q5k108Tg01kMj4MTg001ok307Tg00OBk306Tg00PWk205Tg00QSk40ETg00\^j7iTg02hVk604Tg02i:j7kTg00V0j8nTg00T@j3~Tg01@fk303Tg02:^j2oTg02i^j7uTg00]BR0f0R18070p=V%61#1p=>%11#1p=D%11#6p=B%11#1#1#1#1#1#1#1p=L%11#1#1#Sp=G%61#6#6#6p=:%11#1#1#1p=b%61#6p=`f2R2f1R3'3/01p=9g00c<R49s01p=FAs031p=C1041p==20001p=ZB06031p=H20501p=WP0P2P3P1H0Ep=E1}01p=8P3g00_^R5g00`=R6P6g00`]R7P1g00a=R8Fip=h1{01p=XP0P3g02kUR9P1Ccp=YP3P5P6P6P7P1J04p=If3R:P5P6P6P7P2P5P6P6P7P3P8FiP1Fkp=NP:P5P6P6P7P2P3P1Gnp=gP0P3g00eQP1Ccp=tA~031p=QP2P5P6P6P7P0P3P9P1CcP8Fip=AP2P5P6P6P7P3P1Fkp>0AP0A~023P9P1Ccp=Pf4R9P5P6P6P7P:P2P5P6P6P7P3P1FkFkp=af6R;P5P6P6P7f5R<P9P:P5P6P6P7P2P3P1GnGnp=<1023/21p=R1231,22p=_B03001p=]1023/o1p=;%61#6#1#1p=w%11#6#1#6p=jP<P5P6P6P7P9P:P2P5P6P6P7P3P1FuGnp=p1031,o2p=JP:P5P6P6P7P2P3P5P6P6P7P1P8FiFup=U10:2/o3/21p=Kg00a]20R00p,2rcR800Q3&0C8R=%V3'0B0K8:3%4:g00bWR>#1R?#6R@#>#D#B#D#>#L#GRA6018B0M892%?9%1?RB#1RC#1RD#LRE#SRF6018&0G8%6>R8#6RG#:#:#:RH#1#:#:#b#L#L#GRI/0=RJ%6HRH#:#:#b#L#L#GRK,0=RL'2P0%4;RM%SCRC'@g03TmRN'3RO&0@ARP%1E#`#:#:#B#:#b#L#GRE591XN0P01@ACRQf7RR#4RS/@CRT/3N?91EXN01\MC%FCRN#xRU1OCT15SC'3,CS[1^SC174CRTf8RV#4RW/5CRX#=17XC'2[1dWC17C4RXf9RY#4RZ/5CR[,7C10[4'2[1eZCf:R[#4R\/@C#F\N1[\Cf;R\#4R]/5C/C]\N1@]CP0f<R]#4/5CP01\AC1OCQ15ACR^'3,CA\U1^AC%=^17^C'2\T1dAC17C^10^4'2\X1eAC%FQ\N1[AC1C^A\NPQP0P^P0fDR^#4RX/\F%FFRU#xR_fER`#4Ra1@aF,OF15aF'3'C[1^aF174FRbfFRc#4Rd/5FRe#=17eF'2[1ddF17F4RffG#4Rg/5FRh,7F10h4'2[1egFfHRg#4Rh/@F#F\U1[hFfI#4Rh/5F/Ch\U1@hFP0fJ#4/5FP0p-0Rhg00cZRig00dFRj#TRk#TRl#TRm#TRn#TRo#T#Z&0P>-0O0Rp%Zo6020%Zn%ZmRm:020p%ZlRl%ZkRk20N0C2000jRj60L0'H'H'H'H'H'Hg00deRp'm&0JiRn3l&0IiRo%W:Rq%W<7E2%W9Rr%W;7E;7E3&0H0Rs&0F0RtPtP01}04Rug02nC%8CRvCc,htRw&0D6RxPtPt%XGRG,Yu1ItVS00CNCgPxPtPtPtP5P6P6P71tvu,htJ0BR6Px%8AR5%X?R?9|0v/QG't,htCgPxPtPtPwPxPtPt%18#XRw,Yu1ItYS01CNCgPxPtPtP6Px%XBR61{0>Ru9|0v/Qw't,htCgPxPt1It[S02%X@R@%8K5At60AtPxPtPt1It\Pt1It]PtPtAP65@f=Ry,ItCNDaPx%bH#L#GRH#8,Qu/Q?%8ERu5AtF<F<F<20?t7R7P1P2g00f8Rzg00fXR{+0>20=12=sz{dB0<043H0;R{b5b6b7X20X30X80X90XL0XM0X0hX1hX:hX;hX<hWI%=;/2R\Tg02_`\NRN1OC:/3R,CA[%=R/2[\T1OC9/3V,C;\N10RK,2]f>RKf?RN13RAf@RT7RV3_13;H?9RE[[[[[[^20^30^80^90^L0^M0^0h^1h^:h^;h^<h^IhP1fL#4RH/rA1qHA'210FH%F3PJ17NC17VCPVPNP=PHPYPTPyPKP^P`PcPgOBb4b_b\bSbRbQb@bHb^b[bGbFbEbDbCb]bZbBbAb?b>b=A9OQEePP&0:AEy%fMRQ&09MEyA9QPE%];RQ%V;RM99SA7;S%fSROA9OPM5;QS03%?RROA9OFM5;QS04%B>#>#D#>#>#B#w#GRO13OCRg/0M5;QS05%1>#:#B#j#D#>#D#B#GRH%SDS06,3HRD/0M5;QS07%1>#:#B#j#D#>#D#`#GRJ13JCRz/0M5;QS08%1>#:#B#j#D#>#B#`#GR|13|CRC/0M5;QS09%B>#D#>#B#j#D#w#B#SR}%S>S0:,3}R~/0M5;QS0;%1>#>#D#`#>#>#b#`#GR>%SBS0<,3>RB/0M5;QS0='2S0>'2S0?'2S0@'2S0A'2S0B'2S0C'21vSFS0D%=S%=FRS15ZF#=[[S0E%?VRZ/vFS0F%=Z%?[R[/5FRZ#=\S[S0G%?Y/\FS0H1@[F,OF/3Z,C[\_S0I1^[FS0J%?\R[/5FRZ#=17ZF'2\bS0K1d[FS0L%?]R]/5FR[,7F10[4'2\fS0M1e]FS0N%?yRy/@F#F\US0O1[yFS0P%?KRK/5F/CK\US0Qg027ZRy1zKFRKeS0RPK%4N/\FS0S%4TRT1@TF,OF15TF'3'C\_S0T1^TFS0UfART#4R_/5FRN#=17NF'2\bS0V1d_FS0WfBR_#4Rb/5FRN,7F10N4'2\fS0X1ebFS0YfCRb#4Rf/@F#F\US0Z1[fFS0[15XF/CX\US0\Py1zXFRXeRyPX1HkjRj,HlRl/mp=linRkPo&080RU9Eq3RfAEU2r7E9PsPtPt1It;R;Pt%8FRN=AtG1ItRRGDaPxPtPtQ00PtAAtN?R4PtPt1Q?5R5/Y6Q01CNDaPxPt%X8R89At6R]PxPtQ02AAt58EpF<P7P{b5b6b7X20X30X80X90X0hX1hX:hX;hX<h10F:=_9<10F3133A?R:V5_R109:R513:A=J\9[[[^20^30^80^90^0h^1h^:h^;h^<hP1%]`R[/0d1rdA1qdA'2RZ%FeRe%?cRc/3F1rcF1qcF'2RY7R=15cF#FRSPcP=%V`RQPdPTP_PbO<b4%]^RM%V^R^99aA7;aeb@bHbGbFbEbDbCbBbAb?b>b=bJbKQ03Q0C1Hml/mp=linPoAEr2U9Ef9PsPt1Q?8Rf=AtuPxPtPtPt%8IRu/Y@P;CNPxPtAAt@6PxPtPGAAtf6EpF<P7P{b5b6b7X20X30X80X90X0hX1hA913EARI9<10<913:9=JV<[[[^20^30^80^90^0h^1hP1%]RRE%fWRW'0PLP=%VRRfPPPWP3P2P<O9b4Q04Q0BQ0DQ0EQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RPKQ0SQ0TQ0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\PyPX1Hmj/mp=linPoAEq3r%W2Rr7E9PsPtPtP;PtP4PtPt1Q?NR4/Y6PGCNDaPxPtPtQ00PtAAtNwQ01DaPxPtP]PxPtQ02AAt48EpF<P7P{b5b6b7X20X30X80X90X0hX1hX:hX;hX<h10F1131F?R2<5_910F9=_RV13:F=J\9\5[[^20^30^80^90^0h^1h^:h^;h^<hP110[c13dA?R=ZPePYPSPdP=PQPcPTP_PbO<b4%?`R`A9`F^5;Meb@bHbGbFbEbDbCbBbAb?b>b=bJbKQ05Q0APkPo%W3?E2rRrPsPtPtPt1Yu81It9CNRuPxPtAAt8?R8PxPt1It<RMPt%8O?Pv?CUF<P7P{b5b6b7X20X30X0hX1hARI32RI1023R3AJ<g2[[^20^30^0h^1hP110EOPLP=PfP2P<O6b4Q07Q0@PkPoPrPsPtPuPxPtP8PxPtPMPt%8HQ06#8;P?CUF<P7P{b5b6b7X20X30X0hX1hAJ<D2\3\I^20^30^0h^1hP110EHPLP=PfP2P<O6b4Q08Q0?PkPoPrPsPtPuPxPtP8PxPtPMPt%8J?Pv?CUF<P7P{b5b6b7X20X30X0hX1hAJ<z2\3\I^20^30^0h^1hP110EJPLP=PfP2P<O6b4Q09Q0>PkPoPrPsPtPuPxPtP8PxPtPMPt%8|?Pv?CUF<P7P{b5b6b7X20X30X0hX1hAJ<C2\3\I^20^30^0h^1hP110E|PLP=PfP2P<O6b4Q0;Q0=PkPoPrPsPtPuPxPtP8PxPtPMPt%8}Q0:#8;P?CUF<P7P{b5b6b7X20X30X0hX1hAJ<~2\3\I^20^30^0h^1hP110E}PLP=PfP2P<O6b4PkPoPrPsPtPuPxPtP8PxPtPMPt%8>Q0<#8;P?CUF<P7P{b5b6b7X20X30X0hX1hAJ<B2\3\I^20^30^0h^1hP110E>PLP=PfP2P<O6b4CMCMCMCMCMCMCMCMbXbP%]9R2%4<Rf%V9R999fAP2%ffRfA9fP9P2%?<R<A9<F9P2PO10g9P2PH10D9P2PJ10z9P2P|10C9P2P}10~910B99;2>CKCKCKCKCKCKCKCKebVbWWTWOWYWUo"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DoRec.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
          (RSEC : list achunk -> footprint -> Prop).
Let AHr := ARecyc1P.AHr ASECc AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).
Hypothesis SREC : srec_stmt ASECc RSEC.
(* [comment removed for export] *)
Hypothesis ADD : forall L m m' W, AD L m -> munch W m m' ->
  Forall (fun iv => forall a, fst iv <= a < snd iv ->
     ~ (0x189848 <= a < 0x5d9890) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W -> AD L m'.
Hypothesis AFD : forall L LB m m' W, AF L LB m -> munch W m m' -> fake_untouched L W ->
  Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AF L LB m'.     (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Hypothesis ASECc_wf1 : forall cs L st X m, ASECc cs L st X m -> Forall (sec_wf1 L) cs.
Hypothesis ASECc_disj : forall cs L st X m, ASECc cs L st X m -> sec_disjoint cs.
Hypothesis ASECc_nres : forall cs L st X m, ASECc cs L st X m -> 0 <= a_nres st /\ 8 * a_nres st <= 8388608.
Hypothesis RSEC_app : forall a b RNG, RSEC (a ++ b) RNG <-> RSEC a RNG /\ RSEC b RNG.
Hypothesis RSEC_perm' : forall a b RNG, Permutation a b -> RSEC a RNG -> RSEC b RNG.
Hypothesis RSEC_mono' : forall a RNG RNG', fp_le RNG RNG' -> RSEC a RNG -> RSEC a RNG'.
Hypothesis RSEC_arng : forall L RNG st, arng L RNG st -> RSEC (sec_chunks_of st) RNG.

Lemma SHO : forall R, srec_holes_ok (AQdr R 0 0) AD.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"; "DoRec"] "h01Lh11Rh21Wh31Xh42X'h51mh62m'h72sth83st'p;3p;1p;7p;4p;?g01khj3;j77Tg00@lj10Tg00AQj11Tg00Aoj12Tg01]aj1:Tg00@Lj19Tg03Ugj34Tg03V[j35Tg025@j46Tg03W[l?3Tg03XXj48Tg01PHf0R0g00c<R1;;1p,2ADg00a]g01NVR2g01OQR3g00bW#0#0#0R4#0#0#0#1#2%14#2#:[R4g03Yd#9f8R5P1P1f7R6f6R7f4R8f2R9F7f1R:f3R;;49f9R<?579P<P5P6P7C6f<P1P1f;f:P<P5P6P7f5P8P;P9P:P0M?3UUUUW2X64W5X43W3X82W7W0p,3ADDC8W1o"). Qed.

(* [comment removed for export] *)
Variables (L : alayout) (lo TMP HI : Z) (LB : list ablock) (cbs : word) (RNG0 : footprint) (m0 : amem) (st0 : astate).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Let SP : Z := bv_unsigned sp + -112.
Hypothesis ALO : alayout_ok L.
Hypothesis CEIL : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - DOREC_STACK.
Hypothesis SP47 : bv_unsigned sp <= 2^47.
Hypothesis TMPLO : bv_unsigned sp <= TMP.
Hypothesis TMPHI : TMP + 32 <= 2^47.
Hypothesis HHI : TMP + 32 <= HI.
Hypothesis RSTK0 : rng RNG0 lo (bv_unsigned sp - lo).
Hypothesis RTMP0 : rng RNG0 TMP 32.

(* [comment removed for export] *)
Definition dr_frame (junk8 : list byte) : list cell :=
  [CB 8 junk8; C8 (Z_to_bv 64 (al_t L + 208)); C8 cbs; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition st_keep (st : astate) : Prop :=
     a_live st = a_live st0 /\ a_next st = a_next st0 /\ a_qloc st = a_qloc st0 /\ a_qloc_bytes st = a_qloc_bytes st0
  /\ a_qglob st = a_qglob st0 /\ a_qglob_bytes st = a_qglob_bytes st0 /\ a_nres st = a_nres st0 /\ a_ptr_array st = a_ptr_array st0
  /\ a_space_beg st = a_space_beg st0.

(* [comment removed for export] *)
Definition drinv (R : qrconc) (st : astate) (X : aconc) (RNG : footprint) (m : amem) : Prop :=
     arng L RNG st /\ AREP (AHr R (csx st R)) L st X m /\ ablocks L st X LB /\ AF L LB m
  /\ RSEC (inflight R) RNG /\ mem_inv asegs m /\ stk asegs m lo SP /\ fp_le RNG0 RNG
  /\ munch [(0, bv_unsigned sp); (TMP, TMP + 32)]%Z m0 m /\ cpres L HI LB m0 m /\ st_keep st.

Lemma drinv_rngs : forall R st X RNG m, drinv R st X RNG m -> rng RNG lo (bv_unsigned sp - lo) /\ rng RNG TMP 32.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"; "DoRec"] "h01Hh13FLEh21Rh33RNGh41Xh52_Hh63_H0h73_H1h83_H2h93_H3h:3_H4h;3_H5h<3_H6h=1mh>2stp;1p;5p;3p;2p;6p;4g00@lj19Tg00AQj1ITg00Aoj1BTg01]aj1LTg03ZVj5TTg03[Oj3DTg03\Ej2>Tg035nj6=Tg03]<j5:Tg01Xgj15Tg00C8j2KTg03^5j2JTg00GUj4?Tg00JNj1STg00Jlj2RTg00DPj1QTg00EJj3CTg03^_j2PTg03_<j2;Tg03`2j3<Tg03`ej6@Tg01kMj4OTg03a_j6MTg03bWj1NTg01>;R0j24Tg03Ugj3GTg03cRj4HTg03dDj2ETf6R1f5R2f4R3f3R4f2R5f1R6EMf0R7#N'4p=0AG456/47p=1g03e8R8P2P3P4CH1;56/47'4p=21E86/47p=81467,45p=3A<234A<567'4p=61E87p=7P8P5P6P7CHp=A1;23AG456/47'4p=Fg01PHg01NVg01OQg03emg00bW#9#9#9R8#9#9R9#9#IR:#B%I8#B#L[P3P4P5P6P7DTP0p,1LR8?D53p,2rcR;p,3AHrR<P21>32O2P8P3P4P6E=P;P8P3P4p,2LBR=D:p,2AFR>P8P=P6O3p,4RSECR?%52P5O2P6p,2loR@p,2SPRAp,4RNG0RBP5g00]BR5/K5RCP5P5g00c<p,2sp,J:R:C?P5P5p,3TMPR5%S9R9,R5C?%QC5CC3CRCp,2m0RDP6P;P8p,2HIREP=PDP6P3F0C1E2,863333P4P@1P:@R:P4P5P9E6P7AD831P;P<f8R4f7RF/>4O2P8PFP1P3E=P;P8PFP1P=D:P>P8P=P3O3P?%54P2O2P3P@PAPBP2PCPDP3P;P8PEP=PDP3PFF0C1E2,833333P0P;P<f9R31>43O2P8P4PFP2E=P;P8P4PFP=D:P>P8P=P2O3P?%53P1O2%72P2P@PAPBP1PCPDP2P;P8PEP=PDP2P4F0C1E23333PFP@P:PFP5P9E6P7P;P<f;R<f:R2/><O2P8P2P3PFE=P;P8P<P2P=D:P>P8P=P4O3P?f<RF#5P3O2%74P4P@PAPBP3PCPDP4P;P8PEP=PDP4P<F0C1E23333P0P;P8PFP<P=D:P>P8P=P3O3P?f=R4#5P2O2P3P@PAPBP2PCPDP3P;P8PEP=PDP3PFF0C1E2,8333P<P@P:P<P5P9E6P7P;P8f>R<P4P=D:P>P8P=PFO3P?f@R3#5P4O2PFP@PAPBP4PCPDPFP;P8PEP=PDPFf?R2F0C1E2,8F33P0P>P8P=P4O3P?fARF#5P<O2%74P4P@PAPBP<PCPDP4P;P8PEP=PDP4P3F0C1E233P2P@P:P2P5P9E6P7P>P8P=P2O3P?fDR2#5PFO2%73P3P@PAPBPFPCPDP3P;P8PEP=PDP3fCR3F0C1E233P0P?fER>#5fBR4O2PFP@PAPBP4PCPDPFP;P8PEP=PDPFP2F0C1E2,8FP3P@P:P3P5P9E6P7P?fGR?#5P2O2P2P@PAPBP>PCPDP2P;P8PEP=PDP2P?F0C1E2,82P0%7>P>P@PAPBfFPCPDP>P;P8PEP=PDP>fHR>F0C1E2P?P@P:P?P5P9E6P7%7?P>P@PAPBfIR?PCPDP>P;P8PEP=PDP>fKR>F0C1E2P0AA?@APBfJPCPDP?P;P8PEP=PDP?fLR?F0EFP>P@P:P>P5P9E6P7AA>@APBfMR>PCPDP?P;P8PEP=PDP?fOR?F0EFP0fN,;BPCPDP>P;P8PEP=PDP>fPR>F0C1P?P@P:P?P5P9E6P71;B>PCPDP>P;P8PEP=PDP>fSF0C1fRR>?<@:A<>59PBP>P@P:P6p,5RSTK0E@PBP>P5P9P6p,5RTMP0E@COW<W1P6P7O2n2001000000120000000W0W;P6P7O2n2001000000121000000W0W:P6P7O2n2001000000121000000W0W9P6P7O2n2001000000121000000W0W8P6P7O2n2001000000121000000W0W7P6P7O2n2001000000121000000W0W6P6P7O2n2001000000121000000W0W5P6P7O2n2001000000121000000W0W=W3W4W>W2o"). Qed.

(* [comment removed for export] *)
Definition thdr (T : list (abatch * qbatchc)) (tb : word) : list cell :=
  [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (qfirst L (map snd T))); C8 (Z_to_bv 64 (qlast L (map snd T))); C8 tb].

(* [comment removed for export] *)
Definition ms_in (pc : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (B cnt i : Z) (m : amem) : machine_state :=
  MS (mkR rax (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 TMP) (Z_to_bv 64 738072) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 738136) (Z_to_bv 64 738760) (Z_to_bv 64 B) (Z_to_bv 64 137438953472) (Z_to_bv 64 cnt)
          (Z_to_bv 64 (B + 152 + 8 * i)) (Z_to_bv 64 (16 + cnt)) (Z_to_bv 64 (16 + i)) s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Definition batch_ok (R : qrconc) (kb : Z) (all : list (achunk * Z)) (T : list (abatch * qbatchc)) : Prop :=
  qr_tmp R = T /\ qr_pendb R = [kb] /\ Z.of_nat (length all) <= Q_BATCH /\ 0 <= kb.

(* [comment removed for export] *)
Lemma live_vs_inflight : forall st L X m A Bk mb ms n,
  ASECc ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk) L st X m ->
  forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> mb' + ms' <= mb \/ mb + ms <= mb'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"; "DoRec"] "h01Hh11Ah21ah32cih42cjh51Dh63INlh71lh82l'h92Bkh:2DJh;1Eh<2HSh=3IN1h>3IN2h?2L0h@2LphA2NDhB2NEhC1XhD1mhE2mbhF3mb'hG2mshH3ms'hI1nhJ2n'hK1ohL1phM1shN2stp;1p;3p;4p;6p;2g00@lj1:Tg00AQj1GTg00Aoj1DTg01]aj1ATg00@Lj1@Tg00icj31Tg00=Ij4PTg006cj4KTg02O\j1ITg02PUj6HTg02Pij2TTg00H5j3>Tg01?Qj2?Tg02Z1j1ETg03ffj17Tg02:^R0j29Tg01>;R1j2STg03g^j6RTg02WAj1<Tg002Lj3=Tg01J`j36Tg02;8j4QTg02;Wj38Tg00E0j2OTg02<1j3CTg006Gj6JTg03h^j6LTg00EJj3MTg03iAj1NTg00Jlj2BTg00LUj2FTg00]`R2f1R3#<f0R43=p=3AM234p=4A=234p=2A6234p=0f2R5%N3'B/F4p=51B53/F4p=;g01NVg00a]g01OQg00bW#:#:#:R6#:#:#:#G#D%G6#D#A[%@2R6g00]BR7p,5ASECcf8R8f4R9'3A1534R:f3R;'4'2f7R<P8f6R=f5R>O5g02X@R?%A2P?P2P?g02X^R@g02Y7RAP2CPP?P@PAP2CKP;f=RA#IEH1T2:3>p,:ASECc_disjf>R:f:R@'3A18<=R?f9RB'4'2RCPAP:f<RDf;REP>O61?2Cf@RC/3DA1@B8RF/4E'2,03fARG/3AA1E@BRH/4D'2RI,03RJA>2;5#E%79RK%7;RL759A5L;K'9[RL[[^42^32'SP1f?RK/3EA1B8<RM/4@'2,?2fBRN/3:A1DE@RO/4A'2,03PL[\J^42^32A;>9@A;@B>'9P41?2IfDRI/3CA1:ADR@/4K'2RJ,03fERP/3GRQA1K:ARR/4CRS'2RT,03PL[[^42^32fCRLPBP8P<P=P>ER%<L,0?g004>p4p710R?%@4R<%@3R8P1A=;5396;4A693;A6935'9R1[A6;45A6;43'9A=9;59693[RBA=>9;96>5\1P;P5P3P4CQP4n2001000000120000000X25W8W7W1R1PB^25^88^7<^1?R?P4P2PQPSPF10FQ10FSP1P?P4P2fFRS#<RFPNPH10HF10HN;85O5b038O5b010MJP1P?P4P212FNRFA1CK:RJ/4GRMPJ10JF10JMA>2JJ10JG1O2J383CO5b010RTA>2HJRJP2POfH#<RH,04X22P;A1GCKR;P4EJfG#<,0;P212HIPLA1NGCRCP=P1P?P4P2fI/3PRPPIA1LNGRG10GP10GIP1P?P4P2fJ#<R2PSA1ILNR?10?210?S;85O5b038O5b0ELb6W;%EJRJePJP9POP;P5P3P4O5%7OR5%7;R975OA59;5'9P0A1ADERE#7RD%7CR075EA50CDA;:ALA;LN:'9P4%7@RN%7GRA75@A;K:IR:A;ILKRL;84W5P4O1A5AGNAC:L4W5P4O1n200100000021000010000bKbBb>b=b6W:WAP3P4O2n2001000000121000000bMW@XJ7XH7XF7WLW<XI7XG7WEX96W1WDWCW?WNo"). Qed.

Lemma live_vs_hl : forall st L X m A Bk mb ms n hl,
  ASECc ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk) L st X m ->
  ((mb <= hl /\ hl + 8 <= mb + ms) \/ (exists lms ln, In (CSec (hl - 24) lms ln) ((sec_chunks_of st ++ A) ++ Bk) /\ sec_wf1 L (CSec (hl - 24) lms ln))) ->
  forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> hl + 8 <= mb' + SEC_UOFF \/ mb' + ms' <= hl.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"; "DoRec"] "p'0h01Hh14__x1h24__x2h34__x3h43IN1h53INlh62Lph72lnh87__arithh94__ffh:8__varmaph;5__with<1Ah=3lmsh>1Dh?4__x4h@1ai001ahA1lhB2l'hC2cihD2cjhE1ei011ehF3INhhG3MSBhH2_HhI3_H0hJ3_H1hK3_H2hL4__p1hM3mb'hN3ms'hO2n'hP1ohQ1si021shR2BkhS2DJhT1EhU2H1hV2H2hW3HINhX2HShY3IN2hZ2L0h[3MSEh\2NBh]2NDh^2NEh_3NPRh`3SWhha1Xhb3_H3hc3_H4hd3_H5he3_H6hf3_H7hg2hlhh1mhi2mbhj2mshk1ni031nhl1phm2sthn1zi041ci057map_begi068map_sizei071xp%0p&0p;1p;2p;3p;4p;6p;?p;9p;7p;8g00@lj1;Tg00AQj1kTg00Aok104Tg01]ak10CTg00@Lj1pTg00JNj1@Tg00Jlj20Tg02HAj1=Tg03j9j3RTg01>;R0j22Tg02:^S00j2KTg00=Ik40XTg006ck40VTg02O\j1^Tg00icj35Tg00H5j34Tg01?Qj2xTg02Z1j1hTg03ffj1XTg03iAj1`Tg03g^k60FTg02WAj1:Tg002Lj3HTg01J`j3DTg02;8k40_Tg02;Wj3bTg00LUj21Tg03k2m?0\Tg00Iok10>Tg00N0j2~Tg00OBk30=Tg00Okk20ZTg00DPk10YTg00EJj3|Tg00PWj2nTg00Q5k10WTg00QSj4{Tg00R1k10UTg00ROk10RTg00S:j2lTg00UNk10QTg00VTk20PTg00E0k20OTg00W6k20NTg00Wbk30MTg00XAk40LTg02<1j3iTg03^_j26Tg03l6k20KTg02ZJR1k20JTg03m8k30:Tg003`l9vk60DTg03m[j3gTg029hk10ITg03nPj13Tg02@Nj2NTg03oOj3wTg00Tck405Tg0346k30@Tg02oGk202Tg040Jk30GTg041Hj1dTg042Bj1>Tg03KEj2ZTg043Aj19Tg02hVk60STg01K7R2k20TTg02PUk60dTg02Pik20cTg00T@k30bTg00\^k70BTg00V0k80aTg00S]k20`Tg02_Ck60^Tg044?k10ATg02i:k70]Tg03INk201Tg02odk200Tf0R3#;#;p=rg00]`R4f3R5f2R6f1R735;|3p=B%:6=H47=H43p=e1073,16p=c1167/23p=Q1656?573p=?%:6=H47=H439D45p=Og00]BR800T3p=Vg02X@S01P4P5P6P7P3J0dp=Y20c43p=\A|473p=yAD473p=C%`3,07p>07f4R9/151067/13'Kp>03f6R:f5R;'01095'11067/13'Kp=8%:7=H43p=uAH4739D46p=tA5567=D43p=U11561173'2p=_%;3#;#;#;p=L1067/13p=71067,15/K3p=q10;9/151067/13'Kp>0[10951067'1/K3p>0?B0b873p=]P6g00_^S02g00`=R<P<g00`]R=P8P7g02kUP3H05g00a=R>K0Bp=FP5Q02P<P<P=P6P7P3L0ap=W20`83p=[A5;95AH467=H435D4p=TP4P8P5P6P7P3J0^p=zA4873p=E1Z73g00c<R?548p=ag045<,13p=Jg00f8R@&0A5g0464RA34Aw673'2p=MA48951267/23'2p=S1273,26p>09%339487p>081N56/27/23p>0;1N67/23p=o&0A3=4@Ap>06P7Q02P<P<P=P3P>K0Bp>0HP6Q02P<P<P=P7P3K0]p=}201670003p=P10670013p=I1Z;9=48?11561173'2'2p=<10:;/191067,15'2/23p=Af7R>10:;54820056/079489/23'2p=G1256A487?/23'2p=jA4895A4867/23'2p=s1Z67=48?/23p=f1067,15,29/23p>0E10739486p=m10;900150006/07948:/23p>0<g01NVg00a]g01OQg00bWRA#;RB#;S03#;RC#;#rS04#k$04%kC$04$0C[%p4S05Q05p,5ASECcf9RDP5P6P7P9CB7e;f8REPDP>P:O5%@CRC,07RF?c959Q97P5%=ARG#;#rRH#@RIP7P3C?RJf<RKPEP>COp,2rcRLf;RM;RJ'2X78#VX=8#V'KQ01&0C4RJQ01g02X^RNg02Y7ROP4H0XRPQ01PNPOP4H0VROP5f?RN#^CYA5673#\34p,:ASECc_disjf@RQf:RR?5DERS/yM7eKRTPNPQf>RUf=RVP:O61x4TP7fBRTPUPKPMPRPVCBCOfCRWPVPKPMPUCB7eNRX,C7RYA4456#h%X9RZ0079%X5R[P[%`5PZI03[RZ[[^D4^C4'2P0fAR[A5MRDR\/yK7eV,x4P7fDR]PQPUPVPKPNCBCOPZ[\Y^D4^C4PDPCP;g046TS06P;P9PDF8P31x4XfFRXPQPNPUP[CB7eTRY,C7fGR^/uWR_P[PQPNPTCBR`5t7PZ[[^D4^C4fERZPDPEP>P:P;J0FPEP>P:%:ZCUg004>p4p710Ra%p3Rb%p7RcP0AH5679D53AD975AD976'KRd[ReAD536AD537'KAH9569D97Rf[RgAH;959D;6\dP5P6P7P3H0_RdP3n2001000000120000000X@6WBWAW<RhPg^@6^Bc^Ab^<aRiP3P4P_P`PS1CS_1CS`PhPiP3P4fHR`#:RSP]P\1C\S1C\];b6O5b03bO5b0PDPEP>PYCUQ00P[PU10UCS0710[QRYC_PQPIP7P3C?R\fIRSPZP]COARL`\'2X78#VX=8#V10NCR\PM%LH#L#@RHA7MRNCqPKPTPNP\10T[R\C_P011WQ10WTR_97QCP[PCPVPHPVPKP[F8RjP311ZT10XZ97WCfMRkfLRlfKRmfJRnPSP`P^PXPZPWP[PQPNPUPVN?0\PQPNP^P^PXPQJ0[Q0011Y`A7`^[PXPCPTPH11\XI0?P311\S10WH97^CR\11_^R_g00cZRog00dFRp$0>Rq$0>,~81~8q1~8p60=860=8g00de+0Z&0YoS083|S09%poRoP8P81n89P6&0W8C{P71n85S0:C{Rp&0U8Rq&0R8Rr1l8ARs1l8BRt']S0;Q03,l8Ru5Fr&0Q<RvPr1l8GRw9FruPvQ0;=FrwS0<CWCW20Pr=RxP3P6g00fXRy-0O@20N36=4@ydB0M8?7H0LR?b9b:b;X18X28X38X?81037S0=/1511951065Ry/19[[^18^28^38^?8P3PmP`PWP]P7P;O6b83iW>P3O1A7S`TQ09PoPpPqPr1]wuRu=FrtPvPr%[C,]sRp=FruPv%[HS0>,]t9FrpS0?CWCWPxP?b9b:b;X18X28X38X?811y7AcF59105H976CS0@[[^18^28^38^?8P3PnPmP]P`P7P9O6b89b\_W>P3O1n200100000021100011000bPWVWUP7P3O2n2001000000121000000W0P3O1P[PIP7P3C?R_PnPXPZCOARLS_'2X78#VX=8#VP2P8PTPIP7P3C?R_PmP^PXCOARLn_'2X78#VX=8PjP3P]PIP7P3C?RjPkPSP`COARLlj'2X78#VP2P8PZPIP6P3C?R2fNRjPnPSCOARLk2'2X78PZPCP[PH11YZI0?P3P^PIP9P3C?RYfPR2PlPmCOfOR_=RLY'2P0P`PIP;P7C?RYfQR\PkPlCOARL2YPSPCPZPHPZP]PSF8P316nIP>P5fSRY#:P_PjETPmPIPEP9C?9RLYP0PePgAD;69AD;65'K\fPdP7n2001000000120000000X@6XBcXAbX<aPe^@6^Bc^Ab^<aP3P4fVRafRRb'uRcP\PkPIPRP:C?ReP6O51Cec1Ce\'KPhPiP3P4fXRifTRh'uRcPbP\P2PYCBP_PIPKPEC?REQ001CEc1CEY162IRc?5VDRdfYRf#:fURg3tRFPYPbP\PhCB,Cd'KP7P\PIPUPRC?RyfZRu#:;taR@A5hYbRz/yg,CyR{;b3X0FP3O11CdhA44zy1Cyg;i39i@{W0P3O1n200100000021000010000O5b0bFb016lIPDP;%:gP\P_PjPkP2CBETA5S`^R{00KeA44{eR{%h{+0JP1A5nS`PjPIPMP>C?544R>%h>P_PCPmPHPmPnP_F8P3A5mnS=44ES0AP4P8P3PkP3n0110000022010410330105106103XE4A5lmnPdP3Cz1EnDP4P8P3P_P7n0110000022010410330105106103XE4A5klmPyP7Cz1ElUP4P8P3P\P6n0110000022010410330105106103XE4A5jkl16bIR4?5NMP6Cz1Ej416YIRN,E_P816hIRMPPPOPbf^Ry#^CYA532_#\54JP7P\P2f_Rd#:RECUP6PbP\f`R>#:f\R1PuPfPif[R{CBET1EYZ1EYTPuPCP;PHP;PgPuF8[[]4]5]6XM8PPPOP\f]RT#^CYA5M_j#\54J16gIP2P_%:yCU16aIRjP\P2PEP{PfPifWS0BPuCBET1Eb]P8PZPPPOPafbRE#^CY16fIRe?53Y#\54J16uIS0CP7PhfcR@#:RzPdPTP1P{PyCBET16{IS0DP6PgfdRF#:CU1EaZ10TCS0E16TIR|PHA7|9TCq[]5]4]6XN8PPPOPgfaR}#^CY16iIS0F?5Zb#\54JPePXPY%:EPyP1P{PuPTCBETQ0CP^PhPzCU1Eg]P8PZPPPOPuffRz#^CYA5|n3#\54J16yIS0GPmP7fgS0H#:S0ICU16dIRePlP6fhR~#:PFPEP}P>P@CBETP>PC16>IS0JPHQ0JPkP>F8]4]5]6XO8PPPOPffeRO#^CY161IS0K?5SZ#\54JP|PnPX%:zCUQ0GPmP^Q0IP@P}P>PdPECBET10eH97dCA7eldQ08Po1n87S0IPq%[IRn:0:8sS0GQ0>']9FrpPxP?b9b:b;X18163IS0>/0H973C^18P3P>O1b83bW4W5W6PaP3P5P7P6M9vW0W5W4W6PYP3P5P7P6M9vW0W4W5W6P2P3PkP^PXM9vW0P3O1b0P3O1b0P3O1b0WTP3O1Q0A#hP0Q04#;#LRX#;RY#@Rp,ac10cVR|9gLc&0ILRJ,1|PV%3D%=GRG#=#=#=R|#r#L#L#@RP/ND%JDPDPiPcPVCMDS409P\PCPkPHPkPlP\F8P91a4p10NQR49gLN114JPQ%3K1NPK%JKPKP{PNPQCMDS409P010M[RN9gLMP[%3V1NPV%JVPVP1PMP[CMDS9QNJPgPCP\PHP\P2PgF8P310jW9gLjQ0B/6IRj/0]P]%3Q1NPQ%JQPQPdPjP]CMDS7QJP0Q0F?7ZJPZ%3[1NP[%J[P[P>Q0FPZCMDSPfPCPgPHPgPhPfF8P3Q0C?7^JP`%3]1NP]%J]P]P@Q0DP`CMDSP0208SZPPPZ%JZPZPFQ0KPSCMH0;Q0EPfPHA7fiTCqP3208m^PPP`%J`P`Q0HPePlCMH0;P0%JS9oPSPSP~Q0JPkCMP}PCPTPHPTP1P}F8P3%Jm9oPmPlfk16@IP2CMP0&06kflRk16FI;w\POPCP}PHP}P>POF8P3&06_foQ0H/6I;whQ08PoQ0IPqPrP8%[Pg02nCPsH05-0Hr%@BR_#[R2%;G#=R@#k60@8%=B#;RB#k:0@82']9FrsR25}rPv%@ARA#[=Frs=}r2CWPxP?b9b:b;X18%@@-02_%@B-02_'0R_,139oP3PAP7P7P_C_[^18P3PbP:O2b8%J\9QA\e>0G\7%d\%@XRX%>\RA%@GRG,0\R:?PCC11\A11A:1ZAC%9\R:PAPp%3\RA%=|#=#=#=#=#=R|#@R_=I:pPpPpP:PpPAPAP:%=|#@R|PAPpQ03#=#;#L#L#L#@R:PAPA%rY#=#;#=#L#L#L#@RYE<FAGGCjDs9oP\P01NPb%dbPX%>bR\10bGRA?PCC11b\11\A1Z\C%9bRAP\Pp%3bRbAIA_pPpPpPAPpPbPbPAP|PbPpP:PbPbPYE<FAGGCjDsfjRbPCPzPHPzPOPbF8P31NPh%dgPX%>gRP10gGRh?PCC11gP11Ph1ZPC%9gRhPPPp%3gRgAIh_pPpPpPhPpPgPgPhP|PgPpP:PgPgPYE<FAGGCjDsP0%da/EX%>aRg10aGRh?PCC11ag11gh%9aRhPgPp%3aRaAIh_pPpPpPhPpPaPaPhP|PaPpP:PaPaPYE<FAGG9fgCDSfnRgPCPbPHPbfiRaPgF8P3%di/EX%>fRX10fGRi?PCC11fX11Xi%9fRiPXPp%3fRfAIi_pPpPpPiPpPfPfPiP|PfPpP:PfPfPYE<FAGG9fXCDSP0%>uRX10uGRf?PCC'E11uX11Xf1ZXC%9uRfPXPp%3uRuAIf_pPpPpPfPpPuPuPfP|PuPpP:PuPuPYE<FAGGCjfrRuPCPgPHPgfmRfPuF8P3%>1101G?PCC'E%>TR1,1TP1PTPG%9TRXP1Pp%3TRTAIX_pPpPpPXPpPTPTPXP|PTPpP:PTPTPYE<FAGG9f1CI0EP0%>yR1Ac1yG5Qy%9yRTP1Pp%3yRXAIT_pPpPpPTPpPXPXPTP|PXPpP:PXPXPYE<FAGG9f1CfvR1PCPuPHPufqRXP1F8P3%>>RTAcT>G5Q>%>}R>%9}RTP>Pp%3}R}AIT_pPpPpPTPpP}P}PTP|P}PpP:P}P}PYE<FAGG7fCP0%>ER}/aC%9ERTP}Pp%3EREAIT_pPpPpPTPpPEPEPTP|PEPpP:PEPEPYE<FAGGfzREPCP1PHP1fuRTPEF8P3%>F/aC%9ORF%>OPp%3OROAIF_pPpPpPFPpPOPOPFP|POPpP:POPOPYE<FAGGP0%9zRO%>z;mp%3zRzPOP_PpPpPpPOPpPzPzPOP|PzPpP:PzPzPYE<FAK0<f~RzPCPEPHPEfyROPzF8P3%9~%>~;mp%3aR~%9aRaP_PpPpPpPaPpP~P~PaP|P~PpP:P~P~PYE<FAK0<P0%3bR~%9bRb/0_?Ppp;mpPbPpP~P~PbP|P~PpP:P~P~PYE<FAp+01CR~PCPzPHPzf}RzP~F8P3%3k%9k/0_?Ppp;mp%9fR_Pp%3fRfPfP_P|PfPpP:PfPfPYE<FAP0%9gRf/0p%3gR_Ac_f|3QP_PpP:P_P_PYE<p+01GR_PCP~PHP~p+01BP_F8P3fpRf#9Rk/0p%3fRfAcfk|3Q%3XRfPpP:PfPfPYE<P0%3uRu/apP:PuPuPYC_p+01KRuPCP_PHP_p+01FPuF8P3ft#3/apP:%3TRTPTPYC_P8%31P:P3P3PYC_Xn8P3PEPyJ0DP:PEPEPYC_P~p+01JR~p+01I55uREp+01ORyPIf{fwC?R1p+01APXPgO5%XERg007E%X1REPE%`1PgI03Q00p+01LRg?5u~R~#XR1%`~p+01PPIf|fxC?R~#XRE37%`~=7E1p+01QREPCp+01MR1PHP1PgPEF8P3A51guRg#XRu%`gPEPIPzPOC?RO#XRz37p+01RREp+01NRg/0H77CRCA7g1EREQ08PoP81n86P7Q0:C{R1PqPrQ0;B0:8wn5FrPvQ0<CWPxP?b9b:b;X18X28X38Q0=166I'1A7765[^18^28^38P3p+01SRIPgPyP7O4b83iW>P3O1%`O=7zup-0RzQ09PoP1PqPrQ0G/]w=FrtPvPr%[:=FrwPrQ02P<P<P=P;J0S5}rPvQ0?CWCWPxP?b9b:b;X18X28X38WLQ0>?767AQ:59Q0@[[^18^28^38^LzP3p+01@Rz/1YPzPyPIP7P9O6b89bCEW>P3O1n200100000021000011000bPbGWGWfP7P3O2n2001000000121000000W0WeP7P3O2n2001000000121000000W0WdP7P3O2n2001000000121000000W0WcP7P3O2n2011000000121000000W0WbP7P3O2n2011000000121000000W0WKP7P3O2n2011000000121000000W0WJP7P3O2n2011000000121000000W0WIP7P3O2n2011000000121000000W0WHP7P3O2n2011000000121000000b0WKW_P7P3O2n2001000000121000000W0W\P7P3O2n2001000000121000000W0W[P7P3O2n2001000000121000000W0WJP7P3O2n2001000000121000000W0WIP7P3O2n2001000000121000000W0WHP7P3O2n2001000000121000000W^P3O1n200110200021110111103bQbYW`WFP7P3O2n2001000000121000000W0X78P7P3O2n2001000000121107000W0X=8P7P3O2n2001000000121107000W0P3O1n200100000021100011000Q07PRQ06A7RDUCqeb4b5WSW]P7P3O2n2001000000121000000bQW6XO8XN8XM8WlWWWXXg8Xk8Xj8Xi8WRW<WhWaWZWmo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dr_inner : forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (es : list (achunk * Z)) (K : astate -> AM RT)
    (R : qrconc) st X RNG m (kb : Z) (all : list (achunk * Z)) (T : list (abatch * qbatchc)) (i : Z) (tb : word) junk8
    rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  drinv R st X RNG m -> batch_ok R kb all T -> qr_pend R = es -> es = skipn (Z.to_nat i) all -> es <> [] -> 0 <= i ->
  rw_cells asegs m SP (dr_frame junk8) -> rw_cells asegs m TMP (thdr T tb) ->
  u64arr asegs m (abatch_addr L kb + 24) (map (ehdr L) all) ->
  (forall st1 X1 RNG1 m1 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_drop R []) st1 X1 RNG1 m1 ->
     rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr T tb) ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (ms_in adorec_after rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (abatch_addr L kb) (Z.of_nat (length all)) (Z.of_nat (length all)) m1)) ->
  implS asegs RNG (aembed ATOP (recycle_chunks st (map fst es) K)) (epostF Q)
        (ms_in adorec_lin rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (abatch_addr L kb) (Z.of_nat (length all)) i m).
Proof.
  intros RT Q es. induction es as [|e es IH]; intros K R st X RNG m kb all T i tb junk8 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    INV BOK EP ES NE I0 FR TH ARR KONT; [congruence|].
  pose proof INV as (ARNG & AR & BL & HF & RS & MI & ST & FLE & MU0 & CP0 & SK). destruct (drinv_rngs _ _ _ _ _ INV) as [RSTK RTMP].
  destruct BOK as (ET & EB & ALLB & KB0).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. (try pose proof atop_range as ATR). unfold Q_BATCH in ALLB.
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  assert (IL : i < Z.of_nat (length all)).
  { destruct (Z.lt_ge_cases i (Z.of_nat (length all))) as [H|H]; [exact H| exfalso]. rewrite skipn_all2 in ES by lia. discriminate. }
  assert (NTH : nth_error (map (ehdr L) all) (Z.to_nat i) = Some (ehdr L e)).
  { rewrite nth_error_map. replace (nth_error all (Z.to_nat i)) with (nth_error (skipn (Z.to_nat i) all) 0) by (rewrite nth_error_skipn, Nat.add_0_r; reflexivity).
    rewrite <- ES. reflexivity. }
  set (B := abatch_addr L kb) in *.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & _).
  destruct (pendb_busy L st X R m kb ltac:(destruct AR as (_ & _ & _ & _ & _ & HQ & _); exact HQ) EB) as (nb & bb1 & bctx & bl1 & bl2 & XBB).
  pose proof (busy_slot_geo L st X ALO WF (bany BBatch K_BATCH_CLASS kb nb bb1 bctx) ltac:(rewrite XBB; apply in_app_iff; right; left; reflexivity)) as BG.
  unfold xb_alloc in BG. cbn [xb_class xb_slot bany] in BG. rewrite size_of_class_24 in BG. unfold abatch_addr in B. fold B in BG.
  destruct BG as (_ & _ & BG1 & BG2 & (BG3a & BG3 & BG3b) & BG4 & BG5 & BG6 & BG7).
  pose proof (u64arr_read asegs m (B + 24) _ i (ehdr L e) (wa (B + 152 + 8 * i + -128)) ARR NTH I0 ltac:(f_equal; lia)) as RDV.
  assert (RB24 : rng RNG (B + 152 + 8 * i + -128) 8).
  { destruct ARNG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RCLS & _).
    destruct (RCLS K_BATCH_CLASS (K24)) as (R1 & _). eapply rng_sub; [exact R1| |]; clear -BG1 BG2 BG3 I0 IL ALLB; lia. }
  unfold ms_in, adorec_lin. iprefix.
  step.                                     (* [comment removed for export] *)
  clear RDV RB24.
  zstep.                                    (* [comment removed for export] *)
  step.                                     (* [comment removed for export] *)
  apply evtF_done.
  (* [comment removed for export] *)
  pose proof FR as CBC. unfold dr_frame in CBC. rw_split CBC 1%nat CB8 CBC. rw_split CBC 2%nat CBC CBR. clear CB8 CBR.
  (* [comment removed for export] *)
  assert (POSTK : forall stX X' RNG' m' (W : list (Z * Z)) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    fp_le RNG RNG' -> munch W m m' -> mem_inv asegs m' -> stk asegs m' lo SP ->
    (forall iv, In iv W -> (lo <= fst iv /\ snd iv <= SP) \/ (forall b, In b (x_busy X') -> xb_st b = BBatch -> xb_alloc L b + size_of_class (xb_class b) <= fst iv \/ snd iv <= xb_alloc L b) /\ 0 <= fst iv /\ snd iv <= ATOP) ->
    np_fp L HI LB W -> fake_untouched L W -> (AF L LB m -> AF L LB m') ->
    AREP (AHr (qr_drop R es) (csx stX (qr_drop R es))) L stX X' m' -> arng L RNG' stX ->
    (forall b, In b (x_busy X') -> In b (x_busy X)) -> (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')) ->
    a_live stX = a_live st -> a_next stX = a_next st -> a_qloc stX = a_qloc st -> a_qloc_bytes stX = a_qloc_bytes st ->
    a_qglob stX = a_qglob st -> a_qglob_bytes stX = a_qglob_bytes st -> a_nres stX = a_nres st -> a_ptr_array stX = a_ptr_array st -> a_space_beg stX = a_space_beg st ->
    RSEC (inflight (qr_drop R es)) RNG' ->
    implS asegs RNG' (aembed ATOP (recycle_chunks stX (map fst es) K)) (epostF Q)
          (MS (mkR (Z_to_bv 64 211144) (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0' t1' t2' (Z_to_bv 64 TMP) (Z_to_bv 64 738072) a0' a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 738136) (Z_to_bv 64 738760) (Z_to_bv 64 B) (Z_to_bv 64 137438953472) (Z_to_bv 64 (Z.of_nat (length all)))
                   (Z_to_bv 64 (B + 152 + 8 * i)) (Z_to_bv 64 (16 + Z.of_nat (length all))) (Z_to_bv 64 (16 + i)) s10 s11 t3' t4' t5' t6')
              F (ret_pc (Z_to_bv 64 211144)) fc None m' (seg_rom asegs))).
  { intros stX X' RNG' m' W t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'.
    intros FPLE MU MI' ST' WK NP FU HF' AR' ARNG' XS XL L1 L2 L3 L4 L5 L6 L8 L9 L10 RS'. (try pose proof atop_range as ATR).
    replace (ret_pc (Z_to_bv 64 211144)) with (Z_to_bv 64 211144 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    pose proof AR' as AR1. destruct AR1 as (WF' & _ & _ & _ & _ & HQ' & _). cbn [ah_quar AHr ARecyc1P.AHr] in HQ'.
    destruct (pendb_busy L stX X' (qr_drop R es) m' kb HQ' EB) as (nb' & bb1' & bctx' & bl1' & bl2' & XBB').
    assert (INB : In (bany BBatch K_BATCH_CLASS kb nb' bb1' bctx') (x_busy X')) by (rewrite XBB'; apply in_app_iff; right; left; reflexivity).
    (* [comment removed for export] *)
    assert (DJF : disjoint_from W SP 112).
    { apply ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(_ & _ & HI')]; [left; exact H2| left; clear -HI' CEIL LO SPE; lia]. }
    assert (DJT : disjoint_from W TMP 32).
    { apply ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(_ & _ & HI')]; [left; clear -H2 TMPLO SPE; lia| left; clear -HI' CEIL LO TMPLO SPE; lia]. }
    assert (DJB : disjoint_from W (B + 24) (8 * Z.of_nat (length (map (ehdr L) all)))).
    { rewrite length_map. apply ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(HB & _ & _)].
      - right. clear -H1 BG5 CEIL LO SPE ALLB. lia.
      - specialize (HB _ INB eq_refl). unfold xb_alloc in HB. cbn [xb_class xb_slot bany] in HB. rewrite size_of_class_24 in HB. fold B in HB.
        clear -HB ALLB. lia. }
    pose proof (cells_frameD _ _ _ _ _ FR MU DJF) as FR'. pose proof (cells_frameD _ _ _ _ _ TH MU DJT) as TH'. pose proof (u64arr_frameD _ _ _ _ _ ARR MU DJB) as ARR'.
    assert (INV' : drinv (qr_drop R es) stX X' RNG' m').
    { unfold drinv. split; [exact ARNG'|]. split; [exact AR'|].
      split; [eapply ablocks_mono; [exact BL| exact XL| intros p mb ms n Hp; rewrite L1; exact Hp]|].
      split; [exact (HF' HF)|]. split; [exact RS'|]. split; [exact MI'|]. split; [exact ST'|].
      split; [intros b j Hb; apply FPLE, FLE, Hb|].
      split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx. cbn [outside] in Hx. destruct Hx as (Hx1 & Hx2 & _).
               apply outside_of_In. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(_ & HZ & HI')]; [clear -Hx1 H1 H2 CEIL LO SPR SPE; lia| clear -Hx1 HZ HI' CEIL LO SPR SPE; lia]. }
      split; [eapply cpres_trans; [exact CP0| eapply cpres_of_munch; [exact MU| exact NP]]|].
      destruct SK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9). unfold st_keep. rewrite L1, L2, L3, L4, L5, L6, L8, L9, L10.
      repeat (split; [assumption|]). exact K9. }
    iprefix.
    zstep. zstep.                           (* [comment removed for export] *)
    setreg 25%Z (Z_to_bv 64 (16 + (i + 1))) ltac:(f_equal; clear; lia).
    setreg 23%Z (Z_to_bv 64 (B + 152 + 8 * (i + 1))) ltac:(f_equal; clear; lia).
    step. if_cases KB; zify_cond KB.        (* [comment removed for export] *)
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KB by (clear -I0 IL ALLB; lia).
      assert (NE' : es <> []).
      { intros ->. apply KB. assert (LEN1 : length (skipn (Z.to_nat i) all) = 1%nat) by (rewrite <- ES; reflexivity). rewrite length_skipn in LEN1. clear -LEN1 IL I0. lia. }
      apply evtF_done.
      eapply (IH K (qr_drop R es) stX X' RNG' m' kb all T (i + 1) tb); try eassumption;
        try lazymatch goal with
        | |- batch_ok _ _ _ _ => unfold batch_ok; rewrite <- ET, <- EB; unfold qr_drop; cbn; repeat split; try reflexivity; assumption
        | |- qr_pend _ = _ => reflexivity
        | |- es = _ => replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by (clear -I0; lia); rewrite <- skipn_skipn, <- ES; reflexivity
        | |- 0 <= _ => clear -I0; lia
        end.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KB by (clear -I0 IL ALLB; lia).
      assert (E0 : es = []).
      { destruct es as [|e2 es2]; [reflexivity| exfalso].
        assert (LEN1 : (2 <= length (skipn (Z.to_nat i) all))%nat) by (rewrite <- ES; cbn; lia). rewrite length_skipn in LEN1. clear -LEN1 IL I0 KB. lia. }
      subst es. cbn [map recycle_chunks].
      apply evtF_done. replace (i + 1) with (Z.of_nat (length all)) by (clear -KB; lia).
      eapply KONT; [exact INV'| exact FR'| exact TH']. }
  (* [comment removed for export] *)
  destruct e as [ch kk]. destruct ch as [c n| mb ms n]; cbn [map fst]; [rewrite recycle_chunks_prim| rewrite recycle_chunks_sec].
  - (* [comment removed for export] *)
    eapply arecyc1; try lazymatch goal with
      | |- forall R0 cs0, ahole_laws _ => exact HL
      | |- alayout_ok _ => exact ALO
      | |- arng _ _ _ => exact ARNG
      | |- AREP _ _ _ _ _ => exact AR
      | |- qr_pend _ = _ => exact EP
      | |- mem_inv _ _ => exact MI
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); exact ST
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -LO CEIL SPE; lia
      | |- rw_cells _ _ _ _ => exact CBC
      | |- bv_unsigned _ <= _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear; lia
      | |- _ + 16 <= _ => clear -SP47 CEIL LO SPE; lia
      | |- rng _ lo _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -CEIL LO SPE; lia]
      | |- rng _ _ 16 => eapply rng_sub; [exact RSTK| clear -CEIL LO SPE; lia| clear -CEIL LO SPE; lia]
      | |- @eq word _ _ => reflexivity
      end.
    intros stX X' RNG' ms' RET.
    destruct RET as (FPLE & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & mfa' & -> & MU & WM & MI' & ST' & MFB & AR' & ARNG' & CIN
                     & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & GC & MU1 & AU1 & XS & XL).
    rewrite unsigned_lit in MU, ST' by (clear -SPR CEIL LO; lia).
    pose proof AR as AR1. destruct AR1 as (WF0 & _).
    destruct (pend_head_busy L st X R m c n kk es ltac:(destruct AR as (_ & _ & _ & _ & _ & HQ & _); exact HQ) EP) as (b1 & ctx & l1 & l2 & XB).
    pose proof WF0 as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC c (proj1 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0))) as (_ & _ & _ & _ & A5 & A6 & _).
    eapply (POSTK stX X' RNG' m' _ t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6');
      [exact FPLE| exact MU| exact MI'| exact ST'| | | | | | exact ARNG'| exact XS| exact XL| exact L1| exact L2| exact L3| exact L4| exact L5| exact L6| exact L8| exact L9| exact L10|].
    + (* [comment removed for export] *)
      intros iv Hiv. destruct (rec_W_cases L st X SP c kk n b1 ctx l1 l2 _ _ mfa' iv ALO WF0 XB A5 (proj1 A6) ltac:(split; [exact (proj1 MFB)| exact (proj2 MFB)]) Hiv) as [E|[SL|LP]].
      * left. subst iv. cbn [fst snd]. clear -CEIL LO SPE. lia.
      * right. split; [| split; [destruct (busy_slot_geo L st X ALO WF0 _ ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & _ & _ & G4 & _); unfold xb_alloc in G4; cbn [xb_class xb_slot bany] in G4; clear -G4 SL; lia|]].
        -- intros b Hb Sb. pose proof (XS b Hb) as HbX.
           assert (NEQ : c <> xb_class b \/ kk <> xb_slot b).
           { destruct (Z.eq_dec c (xb_class b)) as [EC|NC]; [right| left; exact NC]. intros EK.
             apply (In_X_g X BQuar c kk n b1 ctx l1 l2 XB) in HbX. destruct HbX as [Hl| ->]; [| cbn in Sb; discriminate].
             exact (key_fresh_g L st X BQuar c kk n b1 ctx l1 l2 XB WF0 b Hl (eq_sym EC) (eq_sym EK)). }
           destruct (busy_slot_geo L st X ALO WF0 b (XS b Hb)) as (CLB & KBb & _).
           pose proof (slots_sep_any L st X c kk (xb_class b) (xb_slot b) ALO WF0 (proj1 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0)) CLB
                         (proj2 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0)) KBb NEQ) as D.
           unfold xb_alloc. clear -D SL. lia.
        -- destruct (busy_slot_geo L st X ALO WF0 _ ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & _ & _ & _ & G5 & _).
           unfold xb_alloc in G5. cbn [xb_class xb_slot bany] in G5. clear -G5 SL. lia.
      * right. split; [| exact (conj (proj1 LP) (proj1 (proj2 LP)))]. intros b Hb _. exact (lowpiece_vs_slot L st X c b iv ALO WF0 (proj1 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0)) (XS b Hb) LP).
    + (* [comment removed for export] *)
      eapply (np_rec_W L st X LB HI lo SP c kk n b1 ctx l1 l2); [exact ALO| exact WF0| exact BL| exact XB| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia| clear -HHI TMPLO SPE; lia].
    + eapply (rec_W_fake L st X lo); [exact ALO| exact WF0| exact XB| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia].
    + intros HF0. eapply (hf_frame _ (HL R (csx st R)) L LB m m'); [exact HF0| exact MU| exact WM|].
      eapply (rec_W_fake L st X lo); [exact ALO| exact WF0| exact XB| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia].
    + (* [comment removed for export] *)
      replace (csx stX (qr_drop R es)) with (csx st R); [exact AR'|].
      unfold csx, inflight, secsT, qr_drop. cbn [qr_tmp qr_pend]. rewrite EP, esecs_cons_prim, (sec_chunks_of_eq st stX L1 L3 L5). reflexivity.
    + unfold inflight, secsT, qr_drop in RS |- *. cbn [qr_tmp qr_pend] in RS |- *. rewrite EP, esecs_cons_prim in RS. eapply RSEC_mono'; [exact FPLE| exact RS].
  - (* [comment removed for export] *)
    pose proof AR as AR1. destruct AR1 as (WF0 & _ & _ & _ & _ & HQ0 & HS0 & _). cbn [ah_quar ah_sec AHr ARecyc1P.AHr] in HQ0, HS0.
    assert (CSE : csx st R = (sec_chunks_of st ++ secsT R) ++ CSec mb ms n :: esecs es).
    { unfold csx, inflight. rewrite EP, esecs_cons_sec, app_assoc. reflexivity. }
    pose proof (ASECc_wf1 _ _ _ _ _ HS0) as WF1. rewrite CSE in WF1. apply Forall_app in WF1. destruct WF1 as [_ WF1]. pose proof (Forall_inv WF1) as SW.
    pose proof (ASECc_nres _ _ _ _ _ HS0) as [NR0 NR1].
    rewrite CSE in AR, HS0.
    assert (RSC : RSEC ((sec_chunks_of st ++ secsT R) ++ CSec mb ms n :: esecs es) RNG).
    { apply (proj2 (RSEC_app _ _ _)). split; [apply (proj2 (RSEC_app _ _ _)); split; [exact (RSEC_arng _ _ _ ARNG)|]|];
        unfold inflight in RS; rewrite EP, esecs_cons_sec in RS; apply (proj1 (RSEC_app _ _ _)) in RS; destruct RS as [RS1 RS2]; [exact RS1|].
      exact RS2. }
    eapply (SREC (AQdr R 0 0) AD AF (sec_chunks_of st ++ secsT R) (esecs es) _ (fun st1 => recycle_chunks st1 (map fst es) K) Q L RNG);
      try lazymatch goal with
      | |- srec_holes_ok _ _ => exact (SHO R)
      | |- alayout_ok _ => exact ALO
      | |- arng _ _ _ => exact ARNG
      | |- RSEC _ _ => exact RSC
      | |- AREP _ _ _ _ _ => exact AR
      | |- mem_inv _ _ => exact MI
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); exact ST
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -LO CEIL SPE; lia
      | |- bv_unsigned _ <= 2 ^ 47 => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -SP47 SPE CEIL LO; lia
      | |- 4096 <= bv_unsigned _ => rewrite unsigned_lit by (clear; lia); clear; lia
      | |- rng _ lo _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -CEIL LO SPE; lia]
      | |- @eq word _ _ => reflexivity
      end.
    intros st' RNG' ms' SR. unfold srec_ret in SR.
    destruct SR as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & hl & -> & STE & HLOK & HLIN & MU & MI' & STK' & AR' & FS & ARNG' & RS').
    rewrite unsigned_lit in MU, STK' by (clear -SPR CEIL LO SPE; lia). subst st'.
    pose proof (fstepS_le _ _ _ _ FS) as FPLE.
    assert (AR'' : AREP (AHr (qr_drop R es) (csx (set_nsec (a_nsec st - 1) st) (qr_drop R es))) L (set_nsec (a_nsec st - 1) st) X m').
    { replace (csx (set_nsec (a_nsec st - 1) st) (qr_drop R es)) with ((sec_chunks_of st ++ secsT R) ++ esecs es).
      2:{ unfold csx, inflight, secsT, qr_drop. cbn [qr_tmp qr_pend]. rewrite (sec_chunks_of_eq st (set_nsec (a_nsec st - 1) st) eq_refl eq_refl eq_refl), app_assoc. reflexivity. }
      unfold AHr, ARecyc1P.AHr. eapply AREP_reqs; [exact AR'| | intros HS1; exact HS1].
      destruct AR' as (_ & _ & _ & _ & _ & HQ1 & _). cbn [ah_quar] in HQ1. eapply AQdr_drop_sec; [exact HQ1| exact EP]. }
    pose proof (live_vs_inflight st L X m _ _ mb ms n HS0) as DJ. pose proof (live_vs_hl st L X m _ _ mb ms n hl HS0 HLIN) as HLS.
    destruct HLOK as (HK1 & HK2 & HK3).
    eapply (POSTK (set_nsec (a_nsec st - 1) st) X RNG' m' _ t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6');
      [exact FPLE| exact MU| exact MI'| exact STK'| | | | | exact AR''| exact ARNG'| intros b Hb; exact Hb| intros b p Hb _; exact Hb
      | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity|].
    + intros iv Hiv. destruct (srec_W_pieces L st X lo SP mb ms n (a_nres st) hl iv ALO WF0 SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv) as [WK _].
      destruct WK as [WK|(WB & WZ & WC)]; [left; exact WK| right]. split; [intros b Hb _; exact (WB b Hb)| exact (conj WZ WC)].
    + eapply (np_srec_W L st X LB HI lo SP mb ms n (a_nres st) hl); [exact ALO| exact WF0| exact BL| exact SW| exact DJ| exact HK1| exact HK2| exact HK3| exact HLS| exact NR0| exact NR1
        | atop_facts; exact CEIL| clear -LO SPE; lia| clear -HHI TMPLO SPE; lia].
    + apply fake_untouched_of. intros iv Hiv.
      exact (proj2 (srec_W_pieces L st X lo SP mb ms n (a_nres st) hl iv ALO WF0 SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv)).
    + intros HF0. eapply AFD; [exact HF0| exact MU| |].
      * apply fake_untouched_of. intros iv Hiv.
        exact (proj2 (srec_W_pieces L st X lo SP mb ms n (a_nres st) hl iv ALO WF0 SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv)).
      * apply Forall_forall. intros iv Hiv. exact (srec_W_t48 L st X lo SP mb ms n (a_nres st) hl iv ALO SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv).
    + unfold inflight, secsT, qr_drop. cbn [qr_tmp qr_pend]. apply (proj1 (RSEC_app _ _ _)) in RS'. destruct RS' as [RS3 RS4].
      apply (proj1 (RSEC_app _ _ _)) in RS3. destruct RS3 as [_ RS3]. apply (proj2 (RSEC_app _ _ _)). split; [exact RS3| exact RS4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ms_out (pc : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6 : word) (m : amem) : machine_state :=
  MS (mkR rax (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 TMP) (Z_to_bv 64 738072) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 738136) (Z_to_bv 64 738760) xs4 (Z_to_bv 64 137438953472) xs6 xs7 xs8 xs9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma dr_after : forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (KK : astate -> AM RT)
    (R : qrconc) st X RNG m (kb : Z) (T : list (abatch * qbatchc)) (tb : word) junk8
    rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 xs7 xs8 xs9 t3 t4 t5 t6,
  drinv R st X RNG m -> qr_tmp R = T -> qr_pendb R = [kb] -> qr_pend R = [] ->
  rw_cells asegs m SP (dr_frame junk8) -> rw_cells asegs m TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_unbatch R) st1 X1 RNG1 m1 ->
     rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr T tb) ->
     implS asegs RNG1 (aembed ATOP (KK st1)) (epostF Q)
           (ms_out adorec_chk rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (abatch_addr L kb)) xs6 xs7 xs8 xs9 t3' t4' t5' t6' m1)) ->
  implS asegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS KK)) (epostF Q)
        (ms_out adorec_after rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (abatch_addr L kb)) xs6 xs7 xs8 xs9 t3 t4 t5 t6 m).
Proof.
  intros RT Q KK R st X RNG m kb T tb junk8 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 xs7 xs8 xs9 t3 t4 t5 t6 INV ET EB EP FR TH KONT.
  pose proof INV as (ARNG & AR & BL & HF & RS & MI & ST & FLE & MU0 & CP0 & SK). destruct (drinv_rngs _ _ _ _ _ INV) as [RSTK RTMP].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. (try pose proof atop_range as ATR).
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  pose proof AR as AR0. destruct AR0 as (WF & _ & INST & _). pose proof (proj1 INST) as ISB. change (AINSTANCE + 32) with 738104 in ISB.
  pose proof (alayout_space L ALO) as (SB1 & SB2 & _ & SB4).
  set (B := abatch_addr L kb) in *.
  (* [comment removed for export] *)
  destruct (pendb_busy L st X R m kb ltac:(destruct AR as (_ & _ & _ & _ & _ & HQ & _); exact HQ) EB) as (nb & bb1 & bctx & bl1 & bl2 & XBB).
  pose proof (busy_slot_geo L st X ALO WF (bany BBatch K_BATCH_CLASS kb nb bb1 bctx) ltac:(rewrite XBB; apply in_app_iff; right; left; reflexivity)) as BG.
  unfold xb_alloc in BG. cbn [xb_class xb_slot bany] in BG. rewrite size_of_class_24 in BG. unfold abatch_addr in B. fold B in BG.
  destruct BG as (_ & _ & BG1 & BG2 & (BG3a & BG3 & BG3b) & BG4 & BG5 & BG6 & BG7).
  assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; clear; lia).
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  assert (RI8 : rng RNG 738104 8) by (destruct ARNG as (R1 & _); eapply rng_sub; [exact R1| clear; lia| clear; lia]).
  pose proof FR as CBC. unfold dr_frame in CBC. rw_split CBC 1%nat CB8 CBC. rw_split CBC 1%nat CBC CBR. clear CB8 CBR.
  unfold ms_out, adorec_after. iprefix.
  step.                                                    (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear -BG4 BG5 SB4 CEIL; lia); [exfalso; clear -K1 BG1 BG3a; lia|].   (* [comment removed for export] *)
  zstep.                                                   (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear -BG4 BG5 SB1 SB2 SB4 CEIL; lia); [exfalso; clear -K2 BG2 BG3 BG3b; lia|].   (* [comment removed for export] *)
  step.                                                    (* [comment removed for export] *)
  zstep. zstep. zstep.                                     (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 K_BATCH_CLASS) ltac:(f_equal; replace (B - al_space_beg L) with (24 * 4294967296 + (B - aregion L K_BATCH_CLASS)) by (clear -ER24; lia);
                                          symmetry; unfold K_BATCH_CLASS in *; apply class_of_offset; [clear; lia| change (2^32) with 4294967296; clear -BG1 BG2 BG3; lia]).
  step. step.                                              (* [comment removed for export] *)
  step.                                                    (* [comment removed for export] *)
  apply evtF_done.
  eapply acdealloc24; try lazymatch goal with
      | |- forall R0 cs0, ahole_laws _ => exact HL
      | |- alayout_ok _ => exact ALO
      | |- arng _ _ _ => exact ARNG
      | |- AREP _ _ _ _ _ => exact AR
      | |- qr_pendb _ = _ => exact EB
      | |- qr_pend _ = _ => exact EP
      | |- mem_inv _ _ => exact MI
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); exact ST
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -LO CEIL SPE; lia
      | |- rng _ lo _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -CEIL LO SPE; lia]
      | |- @eq word _ _ => reflexivity
      end.
  intros stX X' RNG' ms' RET.
  destruct RET as (FPLE & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & mfa' & -> & MU & WM & MI' & ST' & MFB & AR' & ARNG' & CIN
                   & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & GC & XS & XL).
  rewrite unsigned_lit in MU, ST' by (clear -SPR CEIL LO; lia). (try pose proof atop_range as ATR).
  replace (ret_pc (Z_to_bv 64 211200)) with (Z_to_bv 64 211200 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & A5 & A6 & _).
  assert (WK : forall iv, In iv (cd_W L SP K_BATCH_CLASS (c_num_freed (get_cls st K_BATCH_CLASS)) (c_mapped_free_array (get_cls st K_BATCH_CLASS)) mfa') ->
                          (lo <= fst iv /\ snd iv <= SP) \/ (0 <= fst iv /\ snd iv <= ATOP)).
  { intros iv Hiv. destruct (cd_W_cases L SP K_BATCH_CLASS _ _ mfa' iv ALO (K24) A5 (proj1 A6) ltac:(split; [exact (proj1 MFB)| exact (proj2 MFB)]) Hiv) as [->|(P0 & P1 & _)];
      [left; cbn [fst snd]; clear -LO SPE; lia| right; exact (conj P0 P1)]. }
  assert (DJF : disjoint_from (cd_W L SP K_BATCH_CLASS (c_num_freed (get_cls st K_BATCH_CLASS)) (c_mapped_free_array (get_cls st K_BATCH_CLASS)) mfa') SP 112).
  { apply ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|[_ H2]]; [left; exact H2| left; clear -H2 CEIL LO SPE; lia]. }
  assert (DJT : disjoint_from (cd_W L SP K_BATCH_CLASS (c_num_freed (get_cls st K_BATCH_CLASS)) (c_mapped_free_array (get_cls st K_BATCH_CLASS)) mfa') TMP 32).
  { apply ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|[_ H2]]; [left; clear -H2 TMPLO SPE; lia| left; clear -H2 CEIL LO TMPLO SPE; lia]. }
  pose proof (cells_frameD _ _ _ _ _ FR MU DJF) as FR'. pose proof (cells_frameD _ _ _ _ _ TH MU DJT) as TH'.
  assert (INV' : drinv (qr_unbatch R) stX X' RNG' m').
  { unfold drinv. split; [exact ARNG'|].
    split. { replace (csx stX (qr_unbatch R)) with (csx st R); [exact AR'|].
             unfold csx, inflight, secsT, qr_unbatch. cbn [qr_tmp qr_pend]. rewrite EP, (sec_chunks_of_eq st stX L1 L3 L5). reflexivity. }
    split; [eapply ablocks_mono; [exact BL| exact XL| intros p mb ms n Hp; rewrite L1; exact Hp]|].
    split. { eapply (hf_frame _ (HL R (csx st R)) L LB m m'); [exact HF| exact MU| exact WM|].
             eapply (cd_W_fake L lo); [exact ALO| exact (K24)| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia]. }
    split. { unfold inflight, secsT, qr_unbatch in RS |- *. cbn [qr_tmp qr_pend] in RS |- *. rewrite EP in RS. eapply RSEC_mono'; [exact FPLE| exact RS]. }
    split; [exact MI'|]. split; [exact ST'|]. split; [intros b j Hb; apply FPLE, FLE, Hb|].
    split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx. cbn [outside] in Hx. destruct Hx as (Hx1 & Hx2 & _).
             apply outside_of_In. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|[HZ H2]]; [clear -Hx1 H1 H2 CEIL LO SPR SPE; lia| clear -Hx1 HZ H2 CEIL LO SPR SPE; lia]. }
    split. { eapply cpres_trans; [exact CP0|]. eapply cpres_of_munch; [exact MU|].
             eapply (np_cd_W L st X LB HI lo SP); [exact ALO| exact WF| exact BL| exact (K24)| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia| clear -HHI TMPLO SPE; lia]. }
    destruct SK as (K1' & K2' & K3 & K4 & K5 & K6 & K7 & K8 & K9). unfold st_keep. rewrite L1, L2, L3, L4, L5, L6, L8, L9, L10.
    repeat (split; [assumption|]). exact K9. }
  iprefix. apply evtF_done.
  eapply KONT; [exact INV'| exact FR'| exact TH'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma map_fst_combine : forall {A B} (l : list A) (l' : list B), length l' = length l -> map fst (combine l l') = l.
Proof. induction l as [|x l IH]; intros [|y l'] LEN; cbn in *; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.

Lemma qlast_cons_ne : forall q (qs : list qbatchc), qs <> [] -> qlast L (q :: qs) = qlast L qs.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"; "DoRec"] "p'0h01ah12NEh21li001lh31qi011qh43Heqh53IHlh62q'h72q0h82qsh93qs'p;1p;3p;2p;6p;4p1047NR0p605311001R1g000GR2p4p710R3p8P1P2p4p7210p8P1p1003`p4p710p8P1p1001oR4p4p710p8P1g00Y^R5p4p710p8P1p100Z@p4p710R6p8P1p1048QR1p4p710p8P0p6054111000R0P3p8P0P4p4p7210p8P0P6p8P0P1p4p7210p8g00@LR1j1<Tg00DPj1:Tg00H5j35Tg02Z1j18Tg01F7j14Tg02>Rj23Tg00E0j27Tg02]gj2=Tg00EJj39TP5j6@Tg048kj2;TP2j4?Tg049aj3>Tg01KjR2g00]BR5f1R0f0R6C?p=6A9506p=1g00c<9>56p=0A5506p=2%<2R4%:2R39546#8R7P1P2p,1LR1f4#4'3R8%46,31R9X32R:/60R;'1#0%0;R;'2^17P0A5433R7#81743P716:3R7,18#0%07'2P0P6O1'=b4W1A9206=543#8%<5R3P5f;#4,311160R7'1#0%07R8'2^05X23%:5,16#0,75X05f<#4,31/17#0/28^05f3f2R8'1,16#0,75X05W5X23X05P6P0E@W2X05%48,31P9X72/60O2f7#4,31A9280R8,6:R:'1#0%0:R:'2eW1X94X62P0P6O2n10110000020020101100P6O112:;e1;181;10'2eW1W8X32o"). Qed.

Definition qr_done (R : qrconc) : qrconc := mkQR (qr_loc R) (qr_glob R) (qr_ia R) [] [] [] (qr_qpend R).

Lemma dr_outer : forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (T : list (abatch * qbatchc)) (K : astate -> AM RT)
    (R : qrconc) st X RNG m (tb : word) junk8 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6,
  drinv R st X RNG m -> qr_tmp R = T -> qr_pendb R = [] -> qr_pend R = [] -> T <> [] ->
  rw_cells asegs m SP (dr_frame junk8) -> rw_cells asegs m TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 junk8' (tb' : word) rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' xs4' xs6' xs7' xs8' xs9' t3' t4' t5' t6',
     drinv (qr_done R) st1 X1 RNG1 m1 ->
     rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr [] tb') ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (ms_out 0x33908 rax' t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' xs4' xs6' xs7' xs8' xs9' t3' t4' t5' t6' m1)) ->
  implS asegs RNG (aembed ATOP (do_recycle st (map fst T) K)) (epostF Q)
        (ms_out adorec_lout rax t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length T))) a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6 m).
Proof.
  intros RT Q T. induction T as [|[b q] T IH]; intros K R st X RNG m tb junk8 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6
    INV ET EB EP NE FR TH KONT; [congruence|].
  pose proof INV as (ARNG & AR & BL & HF & RS & MI & ST & FLE & MU0 & CP0 & SK). destruct (drinv_rngs _ _ _ _ _ INV) as [RSTK RTMP].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  pose proof AR as AR0. destruct AR0 as (WF & _ & _ & _ & _ & HQ & HS & _). cbn [ah_quar ah_sec AHr ARecyc1P.AHr] in HQ, HS.
  (* [comment removed for export] *)
  destruct (AQdr_popr R L st X m b q T HQ ET EB EP) as (HQ1 & BC & SZB & NTT).
  destruct BC as (CC & EC & JC & CCNT & CLEN & CRNG).
  set (R1 := qr_popr R b q T) in *.
  set (B := abatch_addr L (qb_slot q)) in *.
  set (all := rev (combine (b_chunks b) (qb_ks q))).
  assert (LALL : Z.of_nat (length all) = b_count b) by (subst all; rewrite length_rev, length_combine, CLEN, Nat.min_id; lia).
  assert (MALL : map fst all = rev (b_chunks b)) by (subst all; rewrite map_rev, map_fst_combine by exact CLEN; reflexivity).
  rewrite (qhdrs_rev_combine L _ _ CLEN) in EC. fold all in EC.
  assert (PCS : Permutation (csx st R) (csx st R1)).
  { unfold csx. apply Permutation_app_head. apply Permutation_sym. subst R1. apply inflight_popr; [exact ET| exact EP| exact CLEN]. }
  assert (AR1 : AREP (AHr R1 (csx st R1)) L st X m).
  { unfold AHr, ARecyc1P.AHr. eapply AREP_reqs; [exact AR| exact HQ1| intros HS'; eapply ASECc_perm; [exact PCS| exact HS']]. }
  assert (INV1 : drinv R1 st X RNG m).
  { unfold drinv. split; [exact ARNG|]. split; [exact AR1|]. split; [exact BL|]. split; [exact HF|].
    split; [eapply RSEC_perm'; [| exact RS]; apply Permutation_sym; subst R1; apply inflight_popr; [exact ET| exact EP| exact CLEN]|].
    split; [exact MI|]. split; [exact ST|]. split; [exact FLE|]. split; [exact MU0|]. split; [exact CP0| exact SK]. }
  (* [comment removed for export] *)
  destruct (pendb_busy L st X R1 m (qb_slot q) HQ1 eq_refl) as (nb & bb1 & bctx & bl1 & bl2 & XBB).
  destruct (any_range L st X BBatch K_BATCH_CLASS (qb_slot q) nb bb1 bctx bl1 bl2 XBB WF) as [_ KQ].
  pose proof (busy_slot_geo L st X ALO WF (bany BBatch K_BATCH_CLASS (qb_slot q) nb bb1 bctx) ltac:(rewrite XBB; apply in_app_iff; right; left; reflexivity)) as BG.
  unfold xb_alloc in BG. cbn [xb_class xb_slot bany] in BG. rewrite size_of_class_24 in BG. unfold abatch_addr in B. fold B in BG.
  destruct BG as (_ & _ & BG1 & BG2 & (BG3a & BG3 & BG3b) & BG4 & BG5 & BG6 & BG7).
  assert (RB : rng RNG B 24).
  { destruct ARNG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RCLS & _). destruct (RCLS K_BATCH_CLASS (K24)) as (RR1 & _). eapply rng_sub; [exact RR1| |]; clear -BG1 BG2 BG3; unfold K_FREEARR_OFF; lia. }
  (try pose proof atop_range as ATR). unfold Q_BATCH in CRNG.
  pose proof (tmp_len_bound R1 L st X m ALO WF HQ1) as TLEN. subst R1. cbn [qr_tmp qr_popr] in TLEN. set (R1 := qr_popr R b q T) in *.
  (* [comment removed for export] *)
  assert (QF : (T = [] /\ qfirst L (map snd T) = 0) \/ (T <> [] /\ 17594333495296 <= qfirst L (map snd T) /\ qfirst L (map snd T) + 8192 <= ATOP)).   (* [comment removed for export] *)
  { destruct T as [|[b' q'] T']; [left; split; reflexivity| right]. split; [discriminate|].
    pose proof (tmp_head_geo R1 L st X m b' q' T' ALO WF HQ1 eq_refl) as G. (try pose proof atop_range as ATR). unfold qfirst, qaddrs. cbn [map hd]. exact G. }
  (* [comment removed for export] *)
  assert (REST : forall m2 rax2 (a1x : word),
    munch [(TMP, TMP + 32)]%Z m m2 -> wmono asegs m m2 -> mem_inv asegs m2 -> stk asegs m2 lo SP -> munch [(0, bv_unsigned sp); (TMP, TMP + 32)]%Z m0 m2 ->
    rw_cells asegs m2 SP (dr_frame junk8) ->
    rw_cells asegs m2 TMP [C8 (Z_to_bv 64 (Z.of_nat (S (length T)))); C8 (Z_to_bv 64 (qfirst L (map snd T))); C8 (Z_to_bv 64 (qlast L (map snd T))); C8 tb] ->
    rw_cells asegs m2 B [C8 (Z_to_bv 64 (qfirst L (map snd T))); C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))] ->
    evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (do_recycle st (b :: map fst T) K)) (epostF Q) ms')
         (MS (mkR rax2 (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 TMP) (Z_to_bv 64 738072) (Z_to_bv 64 (Z.of_nat (S (length T)))) a1x a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 738136) (Z_to_bv 64 738760) (Z_to_bv 64 B) (Z_to_bv 64 137438953472) xs6 xs7 xs8 xs9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x33890) fc None m2 (seg_rom asegs))).
  { intros m2 rax2 a1x MUp WMp MI2 ST2 MU02 FR2 TH2 CC2. unfold dr_frame in FR2.
    zstep.                                                 (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (Z.of_nat (length T))) ltac:(f_equal; clear; lia).
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AR2 : AREP (AHr R1 (csx st R1)) L st X mx);
      [ eapply (AREP_frame_ext _ (HL R1 (csx st R1)) L st X m mx); [exact ALO| exact AR1| exact MUp| exact WMp|];
        constructor; [| constructor]; cbn [fst snd]; intros _; right; right; left; atop_facts; clear -CEIL LO TMPLO; lia |];
      assert (HF2 : AF L LB mx);
      [ eapply AFD; [exact HF| exact MUp| |]; [apply fake_untouched_of; intros iv [<-|[]]; apply high_fake; [exact ALO| cbn [fst]; atop_facts; clear -CEIL LO TMPLO; lia]
        | constructor; [| constructor]; cbn [fst snd]; right; pose proof (ao_t L ALO) as OT; unfold aobj in *; clear -OT CEIL LO TMPLO; lia] |];
      assert (CP2 : cpres L HI LB m0 mx);
      [ eapply cpres_trans; [exact CP0|]; eapply cpres_of_munch; [exact MUp|]; intros iv [<-|[]]; cbn [fst snd];
        eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO TMPLO; lia| exact HHI] |];
      assert (INV2 : drinv R1 st X RNG mx);
      [ unfold drinv; destruct INV1 as (_ & _ & _ & _ & RS1 & _); split; [exact ARNG|]; split; [exact AR2|]; split; [exact BL|]; split; [exact HF2|]; split; [exact RS1|];
        split; [assumption|]; split; [assumption|]; split; [exact FLE|]; split; [assumption|]; split; [exact CP2| exact SK] |];
      assert (EC2 : u64arr asegs mx (B + 24) (map (ehdr L) all));
      [ eapply (u64arr_frameD _ _ _ _ _ EC MUp); rewrite length_map; cbn [disjoint_from fst snd]; split; [left; clear -LALL CRNG BG5 CEIL LO TMPLO; lia| exact I] |]
    end.
    step.                                                  (* [comment removed for export] *)
    rewrite do_recycle_cons, <- MALL.
    step. if_cases KC; zify_cond KC; rewrite ?unsigned_lit in KC by (clear -CRNG; lia).   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      assert (E0 : all = []) by (destruct all; [reflexivity| exfalso; cbn [length] in LALL; clear -LALL KC; lia]).
      rewrite E0. cbn [map recycle_chunks].
      apply evtF_done.
      eapply (dr_after Q (fun st2 => do_recycle st2 (map fst T) K) R1 st X RNG _ (qb_slot q) T);
        [exact INV2| reflexivity| reflexivity| subst R1; unfold qr_popr; cbn [qr_pend]; fold all; exact E0| eassumption| eassumption|].
      intros st4 X4 RNG4 m4 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' INV4 FR4 TH4.
      pose proof INV4 as (_ & _ & _ & _ & _ & MI4 & ST4 & FLE4 & MU04 & _). destruct (drinv_rngs _ _ _ _ _ INV4) as [RSTK4 RTMP4].
      unfold ms_out, adorec_chk. unfold thdr in TH4. iprefix.
      step.                                                (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT.                     (* [comment removed for export] *)
      + destruct T as [|bq' T']; [exfalso; apply KT; reflexivity|].
        apply evtF_done. eapply (IH K (qr_unbatch (qr_drop R1 [])) st4 X4 RNG4 m4 _ junk8');
          [exact INV4| reflexivity| reflexivity| reflexivity| discriminate| exact FR4| exact TH4| exact KONT].
      + destruct T as [|bq' T']; [| exfalso; cbn [length] in KT, TLEN; first [rewrite Z.mod_small in KT by (clear -TLEN; lia)| rewrite unsigned_lit in KT by (clear -TLEN; lia)| idtac]; clear -KT; lia].
        apply evtF_done. eapply KONT; [exact INV4| exact FR4| exact TH4].
    - (* [comment removed for export] *)
      assert (NEA : all <> []) by (intros E0; apply KC; rewrite <- LALL, E0; reflexivity).
      zstep. zstep. zstep.                                 (* [comment removed for export] *)
      setreg 23 (Z_to_bv 64 (B + 152 + 8 * 0)) ltac:(f_equal; clear; lia).
      setreg 24 (Z_to_bv 64 (16 + Z.of_nat (length all))) ltac:(f_equal; clear -LALL; lia).
      setreg 25 (Z_to_bv 64 (16 + 0)) ltac:(f_equal; clear; lia).
      rewrite <- LALL.
      apply evtF_done.
      eapply (dr_inner Q all (fun st1 => cache_dealloc st1 K_BATCH_CLASS (fun st2 => do_recycle st2 (map fst T) K)) R1 st X RNG _ (qb_slot q) all T 0);
        [exact INV2| | reflexivity| reflexivity| exact NEA| clear; lia| eassumption| eassumption| eassumption|].
      { unfold batch_ok. subst R1. unfold qr_popr. cbn [qr_tmp qr_pendb]. split; [reflexivity|]. split; [reflexivity|]. unfold Q_BATCH. split; [clear -LALL CRNG; lia| clear -KQ; lia]. }
      intros st3 X3 RNG3 m3 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' INV3 FR3 TH3.
      unfold ms_in.
      eapply (dr_after Q (fun st2 => do_recycle st2 (map fst T) K) (qr_drop R1 []) st3 X3 RNG3 m3 (qb_slot q) T);
        [exact INV3| reflexivity| reflexivity| reflexivity| exact FR3| exact TH3|].
      intros st4 X4 RNG4 m4 junk8'' rax'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' INV4 FR4 TH4.
      pose proof INV4 as (_ & _ & _ & _ & _ & MI4 & ST4 & FLE4 & MU04 & _). destruct (drinv_rngs _ _ _ _ _ INV4) as [RSTK4 RTMP4].
      unfold ms_out, adorec_chk. unfold thdr in TH4. iprefix.
      step.                                                (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT.                     (* [comment removed for export] *)
      + destruct T as [|bq' T']; [exfalso; apply KT; reflexivity|].
        apply evtF_done. eapply (IH K (qr_unbatch (qr_drop R1 [])) st4 X4 RNG4 m4 _ junk8'');
          [exact INV4| reflexivity| reflexivity| reflexivity| discriminate| exact FR4| exact TH4| exact KONT].
      + destruct T as [|bq' T']; [| exfalso; cbn [length] in KT, TLEN; first [rewrite Z.mod_small in KT by (clear -TLEN; lia)| rewrite unsigned_lit in KT by (clear -TLEN; lia)| idtac]; clear -KT; lia].
        apply evtF_done. eapply KONT; [exact INV4| exact FR4| exact TH4]. }
  (* [comment removed for export] *)
  unfold ms_out, adorec_lout. unfold thdr in TH. cbn [length map snd qfirst qaddrs hd] in TH. change (abatch_addr L (qb_slot q)) with B in TH.
  change (Z.of_nat (length ((b, q) :: T))) with (Z.of_nat (S (length T))).
  pose proof (munch_refl [(TMP, TMP + 32)]%Z m) as MUp. pose proof (wmono_refl asegs m) as WMp. unfold dr_frame in FR.
  iprefix.
  step.                                       (* [comment removed for export] *)
  step.                                       (* [comment removed for export] *)
  step.                                       (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN.            (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct QF as [[-> QF0]|(TNE & QF1 & QF2)]; [exfalso; apply KN; rewrite QF0; reflexivity|].
    rewrite (qlast_cons_ne q (map snd T)) in * by (destruct T; [congruence| discriminate]).
    eapply REST; eassumption.
  - (* [comment removed for export] *)
    destruct QF as [[ET0 QF0]|(TNE & QF1 & QF2)]; [| exfalso; first [rewrite Z.mod_small in KN by (clear -QF1 QF2; lia)| rewrite unsigned_lit in KN by (clear -QF1 QF2; lia)| idtac]; clear -KN QF1; lia].
    step.                                     (* [comment removed for export] *)
    subst T. eapply REST; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma drinv_done : forall R st X RNG m, qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] -> drinv R st X RNG m -> drinv (qr_done R) st X RNG m.
Proof.
ltac2:(KReplay.run1 (kr_t_F_adorec ()) ["CANSEC2"; "DoRec"] "h01ch11Hh21lh31kh42NTh51bh62ARh74ARNGh82BLh92CPh:3CP0h;2EBh<2EIh=2EPh>2ETh?3FLEh@2GLhA2HFhB2HQhC3HS'hD2IAhE2MIhF3MU0hG2MXhH3NUMhI2QChJ1RhK3RNGhL2RShM2SKhN2SThO2TBhP2TChQ1XhR2_HhS3_H0hT3_H1hU3_H2hV3_H3hW3_H4hX1mhY2stp%0p&0p;1p;2p;3p;5p;6p;4p;7p;<p;=g00@lj1cTg00AQk10MTg00Aok10BTg01]ak10WTg00C8k203Tg00@Lj1iTg00ogj11Tg00DPj1aTg00H5j37Tg010_j1nTg011Yj1XTg03ZVj5wTg03[Oj3oTg03\Ej24Tg035nj6\Tg03]<j5UTg01Xgj15Tg03^5k20_Tg00GUj4}Tg00JNk10ETg00Jlk20]Tg00EJk30CTg03_<j2gTg03Ugj3hTg03a_j6sTg03bWj1uTg001ok20QTg01@fk20PTg01?mj2CTg00gWj1OTg00E0k200Tg003`j6LTg014Lj1ATg016=j1eTg01E@j1kTg01Foj1tTg01Gij7~Tg04::j1jTg01>;R0j20Tg0295k40GTg036bj2rTg037Yj3dTg038Rj4STg00LUk20FTg02@Nk20^Tg039Ij5ITg0356k40DTg03:Ej4>Tg03;Bj5WTg01^Cj1pTg01_Ak10[Tg015Dj1MTg00nij4lTg01b4j1]Tg01bkj1QTg006Gk60ZTg0176j1zTg01hXj4yTg01iQj2xTg00Z@j2mTg0180k10XTg018jj2|Tg001Nk30;Tg01Ifk10=Tg002Lj3@Tg01?Qk209Tg019fk101Tg01J`j3qTg01:ak108Tg01;Wk10VTg01<Lk10UTg01=Dk10TTg01K7k207Tg01KQk206Tg02aUk30ITg04;5k30STg000cj3KTg00l_k205Tg01Hcm<0OTg04;Pm=0RTg02WAk104Tg03cRk40:Tg03dDk20ATg000Gj4vTg01khk30Nk70KTg03@Mk50iTg03ACk50hTg03B=k40gTg03<ok30fTg03=gk10eTg03>]k10dTg03?Uk10cTg03<9k50bTg01l^k30aTg01`=k10`Tg01a<k602Tg01gXk10LTg01kMk40JTf6R1f5R2f4R3f3R4f2R5f1R6Esf0R7#u'0p=3Ah456/07p=6g03e8R8P2P3P4H0:1g56/07'0p=;20A86/07p=[1067,05,04,03p=9%j3P4P5P6P7Dwp=J20A87p=V1067,05p=8P8P5P6P7H0:p={1g23Ah456/07'0p>0<P5g01LdR8P6P7Cvp=2P5g01KjR9P6P7Cvp=Dg00]`R:?@67p=Tg00c<R;>0N7;p>0HP2P3P4P5P6I0i/07p=HP2P3P4P5P6I0h/07p=GP3P4P5P6H0g/07p=FB0f123&0e4&0d5&0c7,06'0'0'0p=?P2P3P4P5P6I0b/07p=<P2P3P4P5P6DW/07p=bP3P;P;P4P5P6P7K0Kp>0\B0N4;;P5P6P7H0Dp=B%j3P;P;P4P5P6P7K0Kp=:B0a7;;p=`P2P3P4P5P6&0`7J02p=RP3P4g01oKR<%z5%e6&0L7J02p=NP2P3P4P5P9P6P7CvCyp=_f7R=#k/x1P2P3P4P5Cl%]6%Q7'0'0'0p=EP3P4P5P6Cy/07p=f%k6/x7p>0@P2P3P4P5Cl%]6%Q7'0'0p>0?%]6%Q7'0p>0>P3P4P<P5P6&0L7J02p>0YA@5679@34p=ZA@967p==P9g00]BR<g01F7P7Cvp=^A@<67p=YP1P2P3P4P5P6P7H0JH0Jp=Pg01PHg01NVg01OQg03emg00bWR>#c#c#cR?#c#cR@#c$0MRA$0B&0M?$0B$0W[20389R?#iRB%13%a?RC37%i<RD%n2%a<RE37203:<RF#iRG%X1%aFRH37P=P1P2P3P4DwP0p,1LR4?o2=p,2rcRIp,3AHrRJf8RK14=KO2P4P=P1P3E\PIP4P=P1p,2LBRLDUp,2AFRMP4PLP3O3p,4RSECRN%5KP2O2P3p,2loROp,2SPRPp,4RNG0RQP2203<<RRP<P<P;p,2sp-0_AC}P<P<p,3TMPRA&0E@-0]AC}%aR60CR40CRAp,2m0R@P3PIP4p,2HIRSPLP@P3P=F3C6E;,[3D9f9R3PKP=P1P2DJP7Ao4=3PIPJf;R2f:RT/42O2P4PTP3P=E\PIP4PTP3PLDUPMP4PLP=O3PN%52PKO2P=POPPPQPKPAP@P=PIP4PSPLP@P=PTF3C6E;,[=D9P0PIPJf<R=142=O2P4P2PTPKE\PIP4P2PTPLDUPMP4PLPKO3PN%5=P3O2%VKPKPOPPPQP3PAP@PKPIP4PSPLP@PKP2F3C6E;D9f=RKP=P2PTP3DJP7PIPJf>R314K3O2P4PKP=PTE\PIP4P3PKPLDUPMP4PLP2O3PNf?RU#5P=O2%V2P2POPPPQP=PAP@P2PIP4PSPLP@P2P3F3C6E;D9P0PIP4PUP3PLDUPMP4PLP=O3PNf@R2#5PKO2P=POPPPQPKPAP@P=PIP4PSPLP@P=PUF3C6E;,[=38fAR=P2PUP3PKDJP7PIP4P=P2PLDUPMP4PLPUO3PNfCRK#5P2O2PUPOPPPQP2PAP@PUPIP4PSPLP@PUfBRVF3C6E;,[U38P0PMP4PLP2O3PNfDRU#5P=O2%V2P2POPPPQP=PAP@P2PIP4PSPLP@P2PKF3C6E;38fER2PUPKPVP=DJP7PMP4PLPVO3PNfGR=#5PUO2%VKPKPOPPPQPUPAP@PKPIP4PSPLP@PKfFRKF3C6E;38P0PNfHRW#5P2O2PUPOPPPQP2PAP@PUPIP4PSPLP@PUP=F3C6E;,[UfIRUPWP=PKP2DJP7PNfJR2#5P=O2P=POPPPQPWPAP@P=PIP4PSPLP@P=P2F3C6E;,[=P0%VWPWPOPPPQPUPAP@PWPIP4PSPLP@PWfKRWF3C6E;fMR=fLRXPWP2PUDJP7%V2PWPOPPPQPXPAP@PWPIP4PSPLP@PWfNRWF3C6E;P0A{XOPPQP=PAP@PXPIP4PSPLP@PXfORXF3J0<fQRUfPRYPXPWP=DJP7A{WOPPQPYPAP@PXPIP4PSPLP@PXfRRXF3J0<P01gQUPAP@PYPIP4PSPLP@PYfSRYF3C6fUR=fTRZPYPXPUDJP71gQYPAP@PYPIP4PSPLP@PYfVRYF3C6P0AhA@ZPIP4PSPLP@PZfWRZF3fYRUfXR[PZPYP=DJP7AhA@YPIP4PSPLP@PZfZRZF3P0PIP4PSPLP@P[Esf[R[#uf]R=f\P[PZPUDJP7PIP4PSPLP@PZEsf^RZ#uPBPC%i:R:20Q89R\=2?CR]20P89R^=D?CR_'CR`#ORa%OH'TRbA2?\7RcAD?^7Rd'CRe#OfaRf#X#O'T37X2BPGPH%O7,Ta97:bX2G200:bf`Rb#XRaPUEL%1bRUP[EL%Ab%eb%kbPCPEPH%tbF~R[#1Rg92?\AD?^g'C#O%X[#O'TA2?\UAD?^U'C#O%Oa'T57:e%jb#5%5b57:RaePaP:14bfRaf_RU=o4fR[PIPJfbRg#jRhP7O2P4PfPbPZE\PIP4PfPbPLDURiPMP4PLPZO3RjPN%5hPUO2PZPOPPPQPUPAP@PZPIP4PSPLP@PZPfF3C6E;,[ZRk'0D9X2:P:%5fRlP[PIPJPh14fgO2P4PfPbPZE\PiPjPNP7PUO2/0kD9X2:Ao4ZbPIPJ%jfRJPaO2P4PbPUP=E\RkPIP4PbPUPLDUS00PMP4PLP=O3S01PNPlPZO2S02%V=S03A{=OPS041gQZS05AhA@=S06PIP4PSPLP@P=EsR@%ubRL'0RS'0RA'0RQ'0RP'0RO'0RN'0Rj'0Ri'0PYPkPi&0HfRi&0HJp,5ASECcRYPaO1R[P[p,2ADRmPMP4PbPUP=PXP0PIP4PbPUH0G1r4=Ad4b=P4PbPUP=CS&0E>00F7g02MZ-0^7'0R>P4PgPUP6P4PgPfPUP6P4PgPfPUP6P4PgPfPUP6DIEHEGDF[^0<PiP[PmPMH0DR[P4PbPUP=P[P4PbPUP=P[P4P=P=P=P4PgPUP6C>\>^0<P=F?E<EbD9PhP4PfPbPZI0\PXPIP4PgPfH0G1r4bfcRI=d4bP4PIPgPbCSP4feRXPgP6P4PXfdRhPgP6P4PXPhPgP6P4PXPhPgP6DIEHEGDF\>^0<PhPY14IhO1PmPMCBR[P4PIPgPbP[P4PIPgPbP[P4PbPbPbP4PXPgP6C>\>^0<PbF?E<EbD9P01r4fAd4hfP4PhPIPfCSP4ffR[PIP6P4P[PXPIP6P4P[PXPIP6P4P[PXPIP6DIEHEGDF\>^0<PXPY14hXO1PmPMCBRiP4PhPIPfDWPiP4PhPIPfPiP4PfPfPfP4P[PIP6C>\>^0<PfF?E<D9P[P4PXPhPgD:P71r4IfgRI=d4hP4PIP[PhCSP4fiRiP[P6P4PifhRnP[P6P4PiPnP[P6P4PiPnP[P6DIEHEGDF\>^0<PnPY14InO1PmPMCBRoP4PIP[PhDWPoP4PIP[PhPoP4PhPhPhP4PiP[P6C>\>^0<PhF?E<D9P0Ad4nXP4PnPIPXCSP4fjRhPIP6P4PhPiPIP6P4PhPiPIP6P4PhPiPIP6DIEHEGDF\>^0<PiPY14niO1PmPMCBRoP4PnPIPXPoP4PnPIPXPoP4PXPXPXP4PhPIP6C>\>^0<PXF?E<Eb38PhP4PiPnP[D:P7Ad4hIP4fkRIPhPnCSP4fmR[PhP6P4P[flRXPhP6P4P[PXPhP6P4P[PXPhP6DIEHEGDF\>^0<PXPY14IXO1PmPMCBRoP4PIPhPnPoP4PIPhPnPoP4PnPnPnP4P[PhP6C>\>^0<PnF?E<Eb38P0P4PXPIPiCSP4fnRnPIP6P4PnP[PIP6P4PnP[PIP6P4PnP[PIP6DIEHEGDF\>^0<P[PY14X[O1PmPMCBRoP4PXPIPiDWPoP4PXPIPiPoP4PiPiPiP4PnPIP6C>\>^0<PiF?E<38PnP4P[PXPhD:P7P4PnP[PICSP4fqRIPnP6P4PIfpRhPnP6P4PIPhPnP6P4PIPhPnP6DIEHEGDF\>^0<PhPYfoRi/4hO1PmPMCBRoP4PiPnPXDWPoP4PiPnPXPoP4PXPXPXP4PIPnP6C>\>^0<PXF?E<38P0P4frRXPiP6P4PXPIPiP6P4PXPIPiP6P4PXPIPiP6DIEHEGDF\>^0<PIPY14hIO1PmPMCBRoP4PhPiP[PoP4PhPiP[PoP4P[P[P[P4PXPiP6C>\>^0<P[F?E<EbPXP4PIPhPnD:P7P4ftRnPIP6P4PnfsR[PIP6P4PnP[PIP6P4PnP[PIP6DIEHEGDF\>^0<PnPY14[nO1PmPMCBRiP4P[PXPhPiP4P[PXPhPiP4PhPhPhP4fuRiPXP6C>\>^0<PhF?E<EbP0PiPY14niO1PmPMCBRhP4PnP[PIDWPhP4PnP[PIPhP4PIPIPIP4fvRhP[P6C>\>^0<PIF?E<PhP4PiPnPXD:P7fwRXPY14hXO1PmPMCBP4PhPiP[DWfxR[PY14X[O1PmPMCBRMP4PXPhPnPMP4PnPnPnP4fyRMPhP6C>\>^0<PnF?E<P0%pi%`iP4Pi&0[4Rn%M[%AMP[ERP4PiP[PMP[DNP4Pi%1MR>92?\RmP?P^P>E_PMPiP4P[PXPMP[PmGED9fzRmP4PMP[PhD:P6%pX%`[P4P[Pnf{RX#Mf|Rh#APXERP4P[PXPhPXDNP4P[%1hRi92?\R>P?P^PiE_PhP[P4PXPmPhPXP>GED9P0%`MP4PMPn%Mhf}R>#APhERP4PMPhP>PhDNP4PM%1>R[92?\RiAD?^[P>PMP4PhPXP>PhPiGEDf38f~RiP4P>PhPmD:P7%`XP4PhPnp+01@RX#Mp+01ARm#APXERP4PhPXPmPXDNP4Ph%1mRM92?\R[AD?^MPmPhP4PXPiPmPXP[GEDf38P0P4P>Pn%Mmp+01BR[#APmERP4P>PmP[PmDNP4P>%1[Rh92?\RMP?P^PhE_P[P>P4PmPXP[PmPMGE38p+01CRMP4P[PmPiD:P7P4PXPn%MMp+01DRX#APMERP4PmPXp+01ERiPXDNP4Pm%1iR>92?\RhP?P^P>E_PiPmP4PXPMPiPXPhGE38P0P4P[Pip+01FRhPiDNP4P[%1hRm92?\R>AD?^mPhP[P4PiPXPhPiP>GEDfp+01GR>P4PhPiPMD:P7P4PXP>p+01HRXP>DNP4Pip+01IRM#1R[92?\RmAD?^[PMPiP4PXP>PMPXPmGEDfP0P4Php+01JRm#1Ri92?\R[P?P^PiE_PmPhP4PMPXPmPMP[GEp+01KR[P4PmPMP>D:P7P4PXp+01LRX#1R>92?\P?P^P>E_p+01MR>PMP4PXP[P>PX%1>92?\GEP0p+01NRM00@mP4P>PXPMP>%1M92?\J0?p+01ORmP4PMP>P[D:P7p+01PR[00@XP4P[Pmp+01QRXP[%1X92?\J0?P0P4PXP[p+01RR[Cl%1[92?\-0>Xp+01SR>P4P[PXPmD:P7P4P>P[p+01TR[Clp+01URm#192?\-0>[P0%]mp+01VR0#192?\#Qp+01WRXP4P0PmP>D:P7%]Xp+01YR>#192?\#QPBp+01ZRM#1%QcX2BP7PCPmJ0Z%Q]%pX%`XR]P4PXPn%MMRcp+01[Rh#ARiPMERRIP4PX%zMRo%ehRpPMI0YRqP4PX%a8Rr%a9RsCyRt%khRu/xXRXP4PMP>PiPpPuPCPEPH%thRuF~RvClRw%]MRx%QrRr'0Ry'0Rz'0R{'0R|'0R}'0R~'0PWP]P~P2PIP}PKPqP|PVPtP{g027ZPXPzPTPwPyP4PMPMP>PhPvP1g00^[Ry1m9i1m8c37Rw1m9p1m8o57yRy&0X>1|MhR860;F&0=8=@Ru-09R&01hR9-09<p+01\Rz$019q<7g01M_RX&08h9qX7g01QBR{&0V7Rtg01R:37&0U7R|g01S257<&0T7=7<6Rq'038X5X+07+06^3<P<P<P6P7C}p+01]R},|z$0=%t}5@R5qR&08z9qX7g01T297{tA7<|5/0q38X5X-07X+06^3<^0<20F;7X3<>0;<9'0D9R;'0RX<0I1B0SwX1:0Iy;PBPCPF%Mh%AzR;'CRyPF%zh%ezRX'CRwA@F`HRqDZR|PFPyPFPw%Xz9@FeDZ5KFX2BPGPHPFPyPFPwA@F`7DZ9KF|X2GPF1CciRGPF1CopR|PHDZ-05FPFPGPFP|PqDZRq=KFqe%XhRqP[EL%1hR[P0ELPF%AvR`,CcPF%evRc,Co%1vRo92?\AD?^oRo'C%Xv5@FDZPFPGPFP|A2?\[AD?^[R|'C=@FqDZ5KFe1|Mv=KF8ePBPC1=X_,=;#^R8/YERF1=Xd,=;#^%nz'Y5K<X2BPDPE1Y879K<FX2D1=ps,=i#^/YE-05<1=p_,=i#^/YER_=K<_e%nhRhPmELP[P0EL1=co,=`#^%nv'Y1=p|,=i#^/Yh5K<e&01v=K<9e%iR000uN<0OPxPrP5P7FPFPFPFPb4%p0%`0P4P0Pn%M>%AM%eM%kMPCPEPH%tMF~RH#AP>ERP4P0P>PHP>DNP4P0%1HRE92?\R\AD?^EPHP0P4P>p+01XREPHP>P\GEDfD9ePMP4P>PEP0D:eW4WHP6P7O2n2001000000121000000W1W9P6P7O2n2001000000121000000W1WDP6P7O2n2001000000121000000W1WOP6P7O2n2001000000121000000W1W@P6P7O2n2001000000121000000W1WPP6P7O2n2001000000121000000W1WGP6P7O2n2001000000121000000W1WIP6P7O2n2001000000121000000WWWBP6P7O2n2001000000121000000W1WVP6P7O2n2001000000121000000W1WUP6P7O2n2001000000121000000W1WTP6P7O2n2001000000121000000W1WSP6P7O2n2001000000121000000W1WRP6P7O2n2001000000121000000PYPaP4PbPUP=O5P7WCN=0RPkeQ00PjPWQ01PNP2Q02POPKQ03PPPVQ04PQP3Q05PAPTQ06PSP1P@PLP5P6FPFPFPFPFP%5JR5P7EL14bJP:Pl&04fRf/T7%5g,Tf57:X2:&04b/Tl-00:P5P7ELELPJPbPUPZP=Dweb<WMW:P6P7O2n2001000000121000000W1WFP6P7O2n2001000000121000000W1W?P6P7O2n2001000000121000000W1WNP6P7O2n2001000000121000000W1WEP6P7O2n2001000000121000000W1WLP6P7O2n2001000000121000000W1WAP6P7O2n2001000000121000000W1W8P6P7O2n2001000000121000000W1W6P6P7O2n2001000000121000000W1W7P6P7O2n2001000000121000000W1W=W;W>WXWKWQWYWJo"). Qed.

Theorem adorec : forall {RT} (K : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
    (R : qrconc) (X : aconc) (T : list (abatch * qbatchc)) (tb : word) (t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  arng L RNG0 st0 -> AREP (AHr R (csx st0 R)) L st0 X m0 -> ablocks L st0 X LB -> AF L LB m0 -> RSEC (inflight R) RNG0 ->
  qr_tmp R = T -> qr_pendb R = [] -> qr_pend R = [] ->
  mem_inv asegs m0 -> stk asegs m0 lo (bv_unsigned sp) ->
  rw_cells asegs m0 TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 (tb' : word) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_done R) st1 X1 RNG1 m1 -> stk asegs m1 lo (bv_unsigned sp) ->
     rw_cells asegs m1 TMP (thdr [] tb') ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m1 (seg_rom asegs))) ->
  implS asegs RNG0 (aembed ATOP (do_recycle st0 (map fst T) K)) (epostF Q)
        (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 TMP) (Z_to_bv 64 (al_t L + 208)) cbs a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 adorec_entry) fc None m0 (seg_rom asegs)).
Proof.
  intros RT K Q R X T tb t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 ARNG AR BL HF RS ET EB EP MI ST TH KONT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. (try pose proof atop_range as ATR).
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  pose proof AR as AR0. destruct AR0 as (WF & _ & _ & _ & _ & HQ & _). cbn [ah_quar AHr ARecyc1P.AHr] in HQ.
  pose proof (tmp_len_bound R L st0 X m0 ALO WF HQ) as TLEN. rewrite ET in TLEN.
  pose proof (munch_refl [(0, bv_unsigned sp); (TMP, TMP + 32)]%Z m0) as MU0. pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)]%Z m0) as MUf. pose proof (wmono_refl asegs m0) as WM0.
  unfold adorec_entry. unfold thdr in TH.
  iprefix.
  carve_frame 112%nat ST.
  do 12 step.                                 (* [comment removed for export] *)
  step.                                       (* [comment removed for export] *)
  step. step.                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (INV : drinv R st0 X RNG0 mx);
    [ unfold drinv; split; [exact ARNG|];
      split; [eapply (AREP_frame_ext _ (HL R (csx st0 R)) L st0 X m0 mx); [exact ALO| exact AR| exact MUf| exact WM0|];
              constructor; [| constructor]; cbn [fst snd]; intros _; right; right; left; atop_facts; clear -CEIL LO; lia |];
      split; [exact BL|];
      split; [eapply AFD; [exact HF| exact MUf| |]; [apply fake_untouched_of; intros iv [<-|[]]; apply high_fake; [exact ALO|]; cbn [fst]; atop_facts; clear -CEIL LO; lia
               | constructor; [| constructor]; cbn [fst snd]; right; pose proof (ao_t L ALO) as OT; unfold aobj in *; clear -OT CEIL LO; lia] |];
      split; [exact RS|]; split; [assumption|]; split; [rewrite SPE; assumption|]; split; [intros bb j Hb; exact Hb|]; split; [exact MU0|];
      split; [eapply cpres_of_munch; [exact MUf|]; intros iv [<-|[]]; cbn [fst snd]; eapply (np_high L st0 X LB HI); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO; lia| clear -TMPLO HHI; lia] |];
      unfold st_keep; repeat (split; [reflexivity|]); reflexivity |]
  end.
  (* [comment removed for export] *)
  assert (EPI : forall m1 st1 X1 RNG1 junk8' (tb' : word) rax' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 t3' t4' t5' t6',
    drinv (qr_done R) st1 X1 RNG1 m1 -> rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr [] tb') ->
    evtF asegs RNG1 (fun ms' => implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q) ms')
         (MS (mkR rax' (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x33908) fc None m1 (seg_rom asegs))).
  { intros m1 st1 X1 RNG1 junk8' tb' rax' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 t3' t4' t5' t6' INV1 FR1 TH1.
    pose proof INV1 as (_ & _ & _ & _ & _ & MI1 & ST1 & FLE1 & _). destruct (drinv_rngs _ _ _ _ _ INV1) as [RSTK1 RTMP1].
    unfold dr_frame in FR1.
    do 11 step.                               (* [comment removed for export] *)
    zstep.                                    (* [comment removed for export] *)
    setreg 2 sp ltac:(rewrite SPE; replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by (clear; lia); symmetry; apply Z_to_bv_bv_unsigned).
    step.                                     (* [comment removed for export] *)
    release_frame FR1 ST1 (bv_unsigned sp).
    apply evtF_done. eapply KONT; [exact INV1| exact ST1| exact TH1]. }
  step. if_cases K0; zify_cond K0.            (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct T as [|bq T']; [| exfalso; cbn [length] in K0, TLEN; first [rewrite Z.mod_small in K0 by (clear -TLEN; lia)| rewrite unsigned_lit in K0 by (clear -TLEN; lia)| idtac]; clear -K0; lia].
    cbn [map do_recycle].
    eapply EPI; [apply drinv_done; [exact ET| exact EB| exact EP| exact INV]| exact FR| exact TH].
  - destruct T as [|bq T']; [exfalso; apply K0; reflexivity|].
    do 8 step.                                (* [comment removed for export] *)
    apply evtF_done.
    eapply (dr_outer Q (bq :: T') K R st0 X RNG0 _ tb); [exact INV| exact ET| exact EB| exact EP| discriminate| exact FR| exact TH|].
    intros st1 X1 RNG1 m1 junk8' tb' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' xs4' xs6' xs7' xs8' xs9' t3' t4' t5' t6' INV1 FR1 TH1.
    unfold ms_out. iprefix. eapply EPI; [exact INV1| exact FR1| exact TH1].
Qed.
End DoRec.
End CANSEC2.
(* [comment removed for export] *)
