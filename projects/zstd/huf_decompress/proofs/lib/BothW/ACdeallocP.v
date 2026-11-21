(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (RK0_tlow, RK0_thigh, RK0_tstat and 11 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import MM_syscalls WStr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase AKit AKit2 AKitQ AKitR ABytes AQConst AModelFacts ARep ARepKit ARepFrame ALayout AHeapP
     ARepQ ARepQP ARepQR AFreeRep AFreeGeo AFreeRead ARecRep ARepQD ARefillP RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_apopulate F_agetfrom F_arefill F_amaybe F_areturn F_acdrain F_acdealloc F_arecyc1 ARecyc1P.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ACdeallocP () := "C46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7existsbI35stdpp4gmap4gmap00C35stdpp4base4fmapC59OSSVerify5KrLib3Lib3Arr@upd_firstn_skipnC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List:firstn_mapC46Stdlib5Lists4List=repeat_lengthC59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2or00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03I59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7comparec59OSSVerify5KrLib5BothW:ACdeallocP8iclr_intC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP8sclr_intC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula01K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib5BothW:ACdeallocP6reckf0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C46Stdlib5Lists4List9app_assocC47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List:repeat_appC47Corelib4Init3Nat3addI47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib5BothW:ACdeallocP;repeat_app3C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW6ARepQR<aquar_constsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9aq_tcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR6qr_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7aqcacheC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib5BothW6ARepQR6qr_tmpC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR<qcoupled_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQD5qnumRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR8qnum_tmpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR7qr_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR5qr_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6aintalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR8qr_qpendC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW6ARepQR6qrconc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQDDqcoupled_rec_unbatchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQD4AQdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR;aquar_mutexC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib5BothW5ARepQ8abatchesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR8qr_pendbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR7qr_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRep4banyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep4xrecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQD:qr_unbatchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9AQ_GCACHEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW6ARepQR6qrconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib5BothW8ARecyc1P=upd_app_rightC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARecyc1P<upd_app_leftC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=length_firstnI59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4AREPC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib5BothW5ARepQ;abatch_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;F_acdealloc<cdealloc_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_botC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupK59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib5BothW8AFreeRep9any_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aregion_infoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5BothW7ALayout=alayout_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9alayout_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout;alayout_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillP@alayout_res_disjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCsize_of_class_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep@max_cached_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:max_cachedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6aclass01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;F_acdealloc4cd_WC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec8AsanCtrl:init_cacheC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_aensure8m3_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC59OSSVerify5KrLib4Spec8AsanCtrl3rupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill8arec_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillPAinit_cache_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameBget_cls_put_cls_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill>init_cache_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameBget_cls_put_cls_neC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillP>put_cls_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeGeo8slot_geoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9div_exactC47Corelib4Init5Logic5proj2C47Corelib7Classes?RelationClasses=eq_TransitiveC57Corelib7BinNums6PosDef3Pos3mulC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsFtrans_co_impl_morphismC46Stdlib6ZArith4Zdiv:Z_mod_multC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib5BothW9ARepFrame<shlen_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5BothW9F_arefill4ic_WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillP;outside_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefillAic_W_disjoint_genC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulC59OSSVerify5KrLib5BothW4ARep8acompactC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib5BothW7ARecRep4rcutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep6rfree'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep7rcache'C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6xclass01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List7map_appC47Corelib4Init3Nat3subC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List:length_appC47Corelib4Init5Logic9False_indI47Corelib4Init5Peano2le00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC59OSSVerify5KrLib5BothW7ARecRep=xrec_cls_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP6RK0_riC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillP6dj_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;cells_frameC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z7inj_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib5BothW9ARepFrame:junk_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP7RK0_gapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<u32arr_frameC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9skipn_appC46Stdlib5Lists4List9skipn_mapC46Stdlib5Lists4List7skipn_0C46Stdlib5Lists4List:firstn_appC46Stdlib5Lists4List8firstn_0C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List;firstn_all2C59OSSVerify5KrLib5BothW:F_agetfrom:u32arr_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP6RK0_shC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto5fp_bwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit<fill_is_junkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:junk_mergeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame7xb_fitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>slot_in_regionC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP;RK0_space_cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameBbusy_of_Some_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame8awf_fitsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2or02C59OSSVerify5KrLib5BothW7ARecRepBbusy_of_xrec_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRep@busy_of_X_self_gC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRepAbusy_of_xrec_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame=aslots_updateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<slot_alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5azeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARepAslot_shadow_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8granulesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC59OSSVerify5KrLib5BothW9ARepFrameCaslot_shadow_updateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;azero_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillP@region_other_geoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP=RK0_reg_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCaregion_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep>xrec_cls_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9shlen_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame@afreearray_frameC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic:not_eq_symK47Corelib4Init5Logic2or01C59OSSVerify5KrLib5BothW9ARepFrame9shad_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCashadow_avail_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP7RK0_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefillDic_W_disjoint_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep8xrec_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep7In_xrecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_allocC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_app_iffC46Stdlib5Lists4List:in_map_iffC46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib5BothW:ACdeallocP7RK0_imgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP8RK0_tlowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP9RK0_tstatC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP9RK0_thighC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP7RK0_objC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep4rnf'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep5rcnt'C1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib5BothW7ARecRep8awf_xrecC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib5BothW9ARepFrame8rt_hullsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib5BothW9ARepFrame=arep_rt_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame?ainstance_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:junk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit=junk_of_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6al_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill<ic_W_outsideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP<AQdr_unbatchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP>quar_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9quar_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQD:AQdr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_untouchedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;Permutation@Permutation_reflC59OSSVerify5KrLib5BothW6AHeapP@sec_chunks_of_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8sec_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hs_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout4aobjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout<ad_nodes_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout5adisjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout<ad_store_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout:ad_t_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout:ad_t_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hd_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<arelro_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>arep_rt2_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>arep_rt3_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9arng_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4RSECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto9rng_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep9xrec_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C35stdpp4base6lookupC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula07C46Stdlib;setoid_ring6Ncring>ring_mult_compC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<ASTATS_WORDSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrC59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib5BothW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3KLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9rt3_hullsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ACdeallocP?store_cd24_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR9qr_bslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQDGqcoupled_rec_bslot_busyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8in_splitK59OSSVerify5KrLib5BothW4ARep5xbusy01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7qb_slotC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI :=
  ([(sp - 688, sp); (t + 2784, t + 2792); (t + 2800, t + 3168);
    (CA, CA + 4); (CA + 16, CA + 80); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1); (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z) (only parsing).

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_ACdeallocP ()) [] "h04__x1h14__x2h21Hh37__arithh44__ffh58__varmaph65__with71kh82G1h92G2h:1ah;1np;2p;1p;4p;3p;7p;8p-1p10000p4p710R0p8p1000Gp4p710R1p1000dp4p710R2p8P1p1001@p4p710R3p8p1001^p4p710R4p1002<R5p4p710R6p8P4P5p4p7210R5p8p1002Up4p70R7P0p8P7P2p8P7P1p8P7P3p8P7p1003Lp4p710p8P7p1003iR1p4p710p8P7p1004Fp4p710p8p1004bp4p710R7P4p8P7P6p8P7P5p8P7p10056p4p73110p8p1005Hp4p710P2p8P1p4p7210P3p8p1006Ep4p710P2p8p1006dp4p7210P2p8p1007Cp4p710P3p8g007ej2WTg008Zj20Tg0096j22Tg009Sj11Tg00:8j1;Tg00:Vj16Tg00;;j23Tg00;Vj29Tg00<3j2VTg00<Mj1UTg00<mj1TTg00=Mj2PTg00=kj1OTg00>Ij4NTg00>gj1LTg00?Ej1KTg00@0j2:Tg00@Sj2ATg00A6j1ITg00AXj3>Tg00B;j3=Tg00B^j2HTg00C@j2JTg00CZj2GTg00DFj3FTg00D`j3MTg00E?j4ETg00F1j4CTg00FKj4QTg00G6j7DTg00GZj7RTg00H>j8STf0R3#1#1#1#1p=?%13#1#1#1#1#1#1#1p=5%13#1p=B%63#6p=@%63#6#6#6p=7f2R2g00HbR1g00IAR7P7g00IaR5g00JAR6f1R4g00J_P3CQg00KFFDp=4P2P1P7P7P5P4P3FRp=8f3R0P1P7P7P5P2P4P3GSp=<1W43g00KfR1/021202g00LDR8#1R9#?#5R:#1#B#5#5#5#5#5#5#;R;'0g00Lif4R</20%@8#7#7#7#1#6#@#?#5#;R='0%7:#7#7#7#1#B#?#5#;R:/0<1013R>%;8R?,03'3R@f6RAf5RB'2193;,2=RC'019:3RD/0A'3'3X76,V6P212B</0=P6f7RE/2A/0C10DE'3,3@X76R@P1g00MCRD#URC%TDRDP61P62P4%O6CNRF%L6RG%K6RH1:61RI1A68R854H%I7R7PH1A699>68R91:6=RJ54HP7A4HII1:6?RK94HIRL58H1:6;RM9=6I9>6J94H91:6:RN==6I=4H858H58HC<C<1HH5R5P3P2g00MoRIg00NORO'J1G32=FIOdAM614CEROb4b5b6X06X161242/0=1011101?RI'31220RP191;,2='019:1/02'3'3[\>^06^16P3PAPEP<P4O4b3CCW2P3O110:BP6P@P?PCPDPFPGPHA4H9MP7PHA4HN8P7A4HKK98HLA=6KM9>6J94H9A=6NK=4H858H58HC<C<P5POb4b5b6X06X161234/0;10:410??,3I19?;,2=,0P19:?/02'3'3[[^06^16P3PAPEP0P4O4b3CCW2P3O1n200100001021100011000W9W8W2X;6X:6o"). Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6352896 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_ACdeallocP ()) [] "h04__x1h14__x2h22H0h31kh41Hh57__arithh64__ffh78__varmaph85__with92G2h:1ah;1np;2p;1p;4p;3p;7p;8p-1p10000p4p710R0p8p1000Gp4p710R1p1000dp4p710R2p8P1p1001@p4p710R3p8p1001^p4p710R4p1002<R5p4p710R6p8P4P5p4p7210R5p8p1002Up4p70R7P0p8P7P2p8P7P1p8P7P3p8P7p1003Lp4p710p8P7p1003iR1p4p710p8P7p1004Fp4p710p8p1004bp4p710R7P4p8P7P6p8P7P5p8P7p10056p4p73110p8p1005Hp4p710P2p8P1p4p7210P3p8p1006Ep4p710P2p8p1006dp4p7210P2p8p1007Cp4p710P3p8g00Noj2YTg009Sj11Tg00:8j1<Tg008Zj20Tg00:Vj1:Tg00LiR3j2DTg0096j23Tg00;Vj27Tg00<3j2ETg00<Mj1VTg00<mj1UTg00=Mj2TTg00=kj1RTg00>Ij4QTg00>gj1PTg00?Ej1NTg00@Sj2BTg00AXj3@Tg00@0j28Tg00A6j1KTg00B;j3>Tg00B^j2JTg00C@j2ITg00CZj2HTg00DFj3MTg00D`j3GTg00E?j4OTg00F1j4CTg00;;R2j2?Tg00FKj4FTg00G6j7STg00GZj7XTg00H>j8WTf0R1#1#1p=L%11#1#1#1#1#1#1#1p=5%11#1#1#1p=Af2R7f1R5'3/01p=;1075/?1p=61?51,?7p==P7g00HbR6g00IAR4P4g00IaR0g00JAR8P5g00J_P1CFg00KFFSp=2P7P6P4P4P0P5P1FXp=4f3R9P6P4P4P0P7P5P1GWp=91Y51g00LDR6#1R:#1#L#5R;#AR<#5#5#5#5#5#5#<R=9;75P2%<;R;/09R2%<<R<9;97%:6#1#A#:#:#:#:#A#5#<R>/09'Dg00KfR?%<6R@,01761RAf5RB,0;RCf4RD,3B171=,3<RE17>1RF/0B363=X38,E8P5f6RG?;B<10>G'DP3f7R3?;G<10>3f9RG,0;f8RB,3G10FG76E5=AX38,E8P1A;B3<P8f:RH,0;13HG10FH76E5=AX38RAP?g00MCRE#VRF%UEREP81T87P5%R8CQRI%P8RJ%N8RK1B86R61B8:5@8R:188<RL52K%K4R4PK188;=2K6RMP4188?RN=2KN188@RO92KNRP54K188=RQ9>8N9@8L92K:188>RR=>8N=2K654K94KM54KC9C91JK0R0P1P7g00MoRNg00NORS'I1H17=MNSdAG8?5CORSb6b7b8X08X181315RN/0<10;510?@RT96??10;7R;137917?=,3<17>?/07363=[[^08^18P1PGPHP5PDO4b5CCW2P1O110>BP8PAP@PFPEPIPJPKA2K:QP4PKA2KR6P4PKPMP4A2KOO94KPA>8OQ9@8L92K:A>8RO=2K654K94KM54KC9C9C9P0PSb6b7b8X08X1810N=10>510@@,?T139D17@=,3<17>@/09367=2\;[[^08^18P1PGPHP3P5PDO5b5CCW2P1O1n200100000021100011000W2X4CP5P1O2n2001000000121000000W9W4X;8X:8o"). Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6352896 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_ACdeallocP ()) [] "h01Hh14__p1h24__x1h34__x2h44__x3h51kh62rch72H1h87__arithh94__ffh:8__varmaph;5__with<2H0h=2hih>2lop;3p;1p;2p;4p;6p;7p;8p-1p10000p4p710R0p8p1000Gp4p710R1p1000dp4p710R2p8P1p1001@p4p710R3p8p1001^p4p710R4p1002<R5p4p710R6p8P4P5p4p7210R5p8p1002Up4p70R7P0p8P7P2p8P7P1p8P7P3p8P7p1003Lp4p710p8P7p1003iR1p4p710p8P7p1004Fp4p710p8p1004bp4p710R7P4p8P7P6p8P7P5p8P7p10056p4p73110p8p1005Hp4p710P2p8P1p4p7210P3p8p1006Ep4p710P2p8p1006dp4p7210P2p8p1007Cp4p710P3p8g00Odj3bTg00PYj1aTg00:Vj15Tg009Sj11Tg00:8j19Tg00QWj18Tg008Zj20Tg00;;R3j2>Tg00;Vj2=Tg0096j2ETg00<3j2JTg00RMj1DTg00Rlj2CTg00SUj3ITg00T>j2VTg00<Mj1UTg00Tjj3TTg00<mj1STg00=Mj2GTg00>Ij4RTg00>gj1QTg00?Ej1PTg00@Sj2BTg00UJj6OTg00A6j1NTg00@0j2FTg00B;j3ATg00AXj3HTg00B^j2MTg00C@j2`Tg00CZj2_Tg00DFj3^Tg00D`j3[Tg00E?j4ZTg00F1j4KTg00FKj4YTg00G6j7\Tg00GZj7WTg00H>j8]Tf0R2#5#5#5#5p=7%52#5p=X%12#1p=@%12#1#1#1p=:%12#1#1#1#1#1#1#1p=3f2R1f1R7'0/>2p=21>72,>1p=?g00JAR5/F2p=;P1g00HbR6g00IAR4P4g00IaR0P5P7g00J_P2CYg00KFF\p=4P1P6P4P4P0P7P2FWp=6f3R8P6P4P4P0P1P7P2G]p=<1072,>1p=Lg00UnR9Ab172%a8g00LDR:#5R;#5#7#7#7R<#1#5#XR=#5#7#1#@#:#3#3#9R>%88R?%5<#7#7#1#@#:#3#3#9R<,0?32g00Li%5:#1#:#7#:#3#9R?/08R@%:=#3#9R=,01RA'>%1:RB#:#3RC#7#7#7#7#1#@#:#3#9RDf4RE#8,01728g00KfRF%9:RG,02722RHf5RI,0?RJ1=D2RK%1C#@#3#3#3#3#3#3#9RC,=2,E=RLf6RM#8,0ERN52E72I3?X55,J5P7108=92?EP3PJ10E=f7RJ,0?ROf8#8,0M92ML92KJ5?HX55,J5RMP210J=P5f:RP,0?f9RQf;#8RR,0Q72L92KP5?HX55RHPFp-0RKg00MCRLg00VkRS#D#DRT#D,C51C5T1C5S5I55I5g00WJ'V%UL3TRS%SLRLP51G51P71G58CRRT%Q5RU%P5RV%;>1B5;R;54VPVP6P4P4P0PIEOR656V%N4R4PV1B5BRB%;=RW54VP4PV%;?1B5:R:54VRXP41F5FRY=4VY%;GRZ94VYR[56V%;DR\=A5Y=4V:%;CR]9A5Y9H5W94VBA4VB;RY56V56V96VX56VC<C<C<1MV0R0P2P1g00MoR^g00NOR_'`1_21=^^_dA[5F7CZR_b9b:b;X25X35X45W1A2>1810?110FGR?92FF1=DF1=FC,E=10EIRF52E7287?@[\A[^25^35^45^1KP210R<PRPQPPPJP7P1O7b8CKW7X0OP7P2O2n2001000010121000000W0P2O1%8I,0892DEP310DIPNPMP210DJ%8Q,0JP5PHPGPSPLPTPUPV%;<94V;96V6P4PVPYP4PVA4V\:P4A4VZZ96V[AA5\Z=4V:AA5Z]9H5W94VB=6VY56V96VX56VC<C<C<P0P_b9b:b;X25X35X45X1KAL81<101810D1AL?GG1=DG1=GC,E==2EF7287?@[[[^25^35^45^1KP210>RPRPQPPPJP7P1O7b8CKW7W0P7P2O2n2001000010121000000W0P2O1n200100001021100011000b<W0X=5X>5X69P2O1X69P2O1W6o"). Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
Section Kinds0.
Variables (sp lo t ctx SB c RB FA RI CA mu au nf mfa mfa' SHF0 SHF1 : Z).
Definition reckf0 : Prop :=
     (ATOP <= lo /\ lo <= sp - 688 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6352896 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (2201439137792 <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : reckf0.

Ltac kind0 := pose proof KF as KF'; unfold reckf0, AIMG_HI in *;
  destruct KF' as (F_lo & (Ft1 & Ft2 & Ft3 & Fc1 & Fc2 & Fc3 & Ftc) & F_c & F_sb & F_tsb & F_csb & F_mu & F_sh);
  band_int Ft2; band_int Ft1; band_int Fc1; clear Ft1 Ft2 Fc1;   (* [comment removed for export] *)
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma RK0_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6352896 -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof.
ltac2:(KReplay.run1 (kr_t_ACdeallocP ()) ["CANSEC1"; "Kinds0"] "p'0h02H2h16__sat5h24__x1h34__p1h44__x2h54__x3h64__x4h74__p2h84__x5h97__arithh:4__p3h;6__sat4h<4__ffh=8__varmaph>5__with?4__p4h@4__p5hA4__p6hB4__x6hC4__x7hD4__x8hE4__p7hF1khG2G0hH1ehI1GhJ2HahK5__p10hL5__p11hM5__p12hN5__p13hO5__p14hP5__p15hQ5__p16hR5__p17hS5__p18hT5__p19hU4__p8hV4__p9hW4__x9hX1AhY3F_chZ5F_csbh[4F_loh\4F_muh]4F_sbh^4F_shh_5F_tsbh`3Fc1ha3Fc2hb3Fc3hc3Ft1hd3Ft2he3Ft3hf3Ftchg5KAFc1hh5KAFt1hi5KAFt2hj5KBFc1hk5KBFt1hl5KBFt2hm5KCFc1hn5KCFt1ho5KCFt2hp5KDFt2hq3KF'hr4kFc1hs4kFt1ht4kFt2i001xp%0p%1p&0p;1p;2p;3p;4p;5p;6p;7p;8p-1p10000p4p710R0p8p1000Gp4p710R1p1000dp4p710R2p8P1p1001@p4p710R3p8p1001^p4p710R4p1002<R5p4p710R6p8P4P5p4p7210R5p8p1002Up4p70R7P0p8P7P2p8P7P1p8P7P3p8P7p1003Lp4p710p8P7p1003iR1p4p710p8P7p1004Fp4p710p8p1004bp4p710R7P4p8P7P6p8P7P5p8P7p10056p4p73110p8p1005Hp4p710P2p8P1p4p7210P3p8p1006Ep4p710P2p8p1006dp4p7210P2p8p1007Cp4p710P3p8g009Sj12Tg00:8j1<Tg008Zj20Tg00:Vj17Tg00QWk10;Tg00X6j2wTg00XSk20STg007ek206Tg00Nok20MTg0096j21Tg00;;R3j23Tg00;Vj25Tg00Y0k20ETg00<Mj1}Tg00YPj36Tg00PYk10?Tg00ZLk20>Tg00[4j2zTg00[Pk30<Tg00\4k20:Tg00C@j2xTg00RMj1DTg00Rlk209Tg00<mk10TTg00=kk10RTg00>gk10QTg00?Ek10PTg00A6k10LTg00@Sk205Tg00B^k20KTg00CZk20JTg00DFk304Tg00D`k30ITg00E?k40HTg00\Uk40GTg00<3S00j2uTg00@0j2sTg00]Sk501Tg00^Qk30FTg00_4j2bTg00_]j2kTg00`Ik10DTg00`gk20CTg00aHj3pTg00b1k50@Tg00Lik200Tg00bUj4yTg00Tjj3qTg00SUj3jTg00T>j2~Tg00=Mk20=Tg00>Ij4fTg00UJk603Tg00FKj4mTg00G6j7nTg00AXj3vTg00GZj7_Tg00H>j8gTg00c5k707Tg00cYk30NTg00B;k30OTg00dBk408Tf0R2#2#2p=o%22#2#2p=rg00KfR1/02p=H%72#2p=Y%22#2#2#2p=P%72#7p=Z%22#2#2#2#2#2#2#<p=Nf2R7f1R5'1/02p=B%22#2#2#<p=W1075/32p=@f3R6/071052+00p=:g00JAR411528047p=U%72#7#7#7p=E%22#2#2#2#2#2#2#2p=L1352,37p=A10671052'3p=Rf4R01352,37,36'3p=\f6R8P4P4f5R9P0CyP4P4P7P5Cy=q623qp=d20942p=MAj452p=GAj452g00WJR:'~p=Vg00MCR;?q52p=>20=42p=OP4P7P5P2Cfp=?P4P4P0P6P7CfP5P2Cfp=SP5g00HbR<g00IAR=P=g00IaR>P2J03p=920542p=C1s42p==P7P<P=P=P>P4P5g00J_R?P2Cmg00KFR@Fnp=4Av452p=;P7P<P=P=P>P5P2F_p=IP8P<P=P=P>P9P0P6P<P=P=P>P7P5P2GgGgp=8P9P<P=P=P>P0P<P=P=P>P6P7F_P5P2Ggp=F1052,37p=l1152,07p=e1552,17p=tP6P<P=P=P>P7P5P2Ggp>02P0P<P=P=P>P6P7P<P=P=P>P5P2F_F_p=[P6P<P=P=P>P7P<P=P=P>P5J03P2F_p=KP4P5P?P2Cmp=TP6P<P=P=P>P7P<P=P=P>P5P@FnP2F_p=]P9P<P=P=P>P0P6P7P<P=P=P>P5P2K07Ggp=X10750002p=JB0N452p=aB0O452p=^1s429v45p=QP6P<P=P=P>P7P<P=P=P>P5P@FnP2K07p=`Aj4529j47p=hP4P5g00d]P2Cmp=iP5P<P=P=P>P2P@Fnp=|P4Av475P?P2Cmp={1~2:p>0BP4P0P6P4P7P5P2CfCfp>0AP8P9P0P6P7P5P2H08H08p=cg00LDR:#2R?#2R@#2RA#2RB#2RC#2RD#2RE#oRF#rRG#2RH#rRI#<RJ/05%H5RK%Y:#P#7#Z#Y#P#NRL9B67p,2KFS01g00eDP3p,2rcRM$0;RNp,2loS02Q02p,2spRO%7?S03#2S04#7S05#7RP#2#WRQ'wS06%<?RR%<DRD+0SRS,0OS073@3@S08p,1tRT%<GRG+06S0920MTGS0:11TGRU/0NS0;p,3ctxRV006JS0<10LVS0=11VJRW/0NS0>11VGPTPUPVC:S0?'3S0@'3S0A'3S0B'3S0C'3S0D'3S0E%<:RXp,1cRY%7:RZ#7R[#ZR\#<S0F,0YS0G3@p,2CAR]%2ZR^#7S0H#2#WS0I,1TQ04#WR_,5Y3US0J'3S0K%EH#E#E#E#L#NRHp,2SBR`'0S0L%LIRI#Y#P#NRa,1`Rb/0NS0Mp,2RBS0N%2I#PRI#rRc#<S0O,5Y7U`S0Pp,2FAS0QQ0N%2[S0R#2#P#L#L#NS0S3US0Tp,2RIRd%2c#PRc#<S0U,1`%<ERE,5Y3US0V3AS0W'3S0X'3S0YPUP`PbPTC:S0ZPWP`PbPVC:S0[p,2auRb#HS0\p,2muRe,0bS0]Q0S,0eS0^p,2nfS0_#H%<@ReQ0_'5Rbp,3mfaRfPfp,4mfa'RfPf%<ICR3@S0`D\S0a%YF#o#7#Z#E#E#Y#Z#Y#P#NS0bp,4SHF0S0cQ0cp,4SHF1S0dQ0dPHCRS0e3@S0f'3S0g'3S0h'3S0i'3S0j'3RF'3S0k20E44RIQ06POPI%7PRP#2Rg#2#WS0l,1TS0m%7g#WS0n,1TS0oPI%YP#WS0p,1TS0q%o^#Z#o#WS0r,1TS0sPIP]11]eS0tPI%<BRB,1]S0u11]_S0vPIQ0Q/1bS0wQ0Q/1fS0xPIQ0cQ0dPIPd%<A,1dS0yPI11dBS0z%<C,1dS0{PI%7@S0|#WS0},1dS0~11dES10%}IFdFdFdFdFdRI?689P2Q08Q0kP3Q0EPFf:RCf9Rf56IP2Q0EP3Q09Q0Df>S11f=Rb56I\FP2Q09Q0DP3Q0:Q0CfBS12fAS1356I\FP2Q0:Q0CP3Q0;Q0BfFS14fES1556I\FP2Q0;Q0BP3Q0<Q0AfJS16fIS1756I\FP2Q0<Q0AP3Q0=Q0@fNS18fMS1956I\FP2Q0=Q0@P3Q0>Q0?fRfQ56I\FP2Q0>Q0?P3Q0KQ0jfVfUS1:56IP2Q0KQ0jP3Q0YQ0ifZfY56IP2Q0YQ0iP3Q0ZQ0hf^S1;f]56IP2Q0ZQ0hP3Q0[Q0gfbfa56IP2Q0[Q0gP3Q0aQ0fffS1<feS1=56IP2Q0aQ0f&0?MRM%Z\#E#ER\#2#7#ZS1>#7#E#L#L#NR^/0NS1?%7\#E#E#L#L#NR\,0NS1@'3RP20>RDRg1z1RRh%HD1z1S[Ri[Rj%HRRkg00f@S1AB0<RD5UWJRDQ1A%HS[^JkRkP5g00f\20:1R'xPheO1RhPip-0RRg00VkRS#DRl#DS1B#DS1C#DS1D#MRm%MlS1E2094SRS'GRl'V%};Rn'>&0T;R;%O0Ro&0R4Rp7?0P7PpP5%O6S1F??0pDS&0Q4Rq&0P4RrPr19r8S1G%C?R?%=\54rS1H&0L=RsPrPrf7Rt,9rS1I%CAS1J%=aS1K';=4r?S1Lf8RA,9rS1M5IrPsPrQ03#CRu%=JRv';=4r?PsPr2054:Rw%=GRx';Ry=4r?Ps%Pc#L#L#NRc#=Rz94ryF8EFEF20Kr>RyP2P7g00MoR{g00NOR|'x20J27>04{|dB0I415H0HR|b<b=b>X24X44X54X64X3RX7RW:S1N105\S1O,30AB0a7=A8tAB0J6116GS1P/00110GS1Q/0c[[[[^24^44^54^64^3R^7R^:RS1RP2Q0WQ0LQ1?P`PVPNPTP0Q12fKS1SfWR\O;b9b1b;b110UcR{eb0P{PTPGP\P2H0G%H2?l2XR\10GTR}PU152cS1T,1J15L2PTCR3AS1UXF4R~,u4Q00P4P~flfk56IP2Q1UP3AlK5XS1V155cS1W9eUJ15L5/0T5A}fpfo56IP2%H6S1X?l6XS1Y150cS1Z9eUJ15L0/0T5A}P3P}PU159cS1[,1J15L9S1\PTCRftfs56IP2PUAtJAcS1]15LAPTCRP315fc9eUJ15Lf/0Tfxfw56IP2f;R~/5c9eUJf<S1^,5L/0TPMPPPgPjPDPkPhPiPnP;%O5S1_PqPrA4rxwPs1s41S1`=4rwS1aH02PyP|b<b=b>X2410G2PK[^24P2PTPCO2b9b1b;b1%HTR1eb0P1PMPPPgPjPDPkPhPiQ1NQ1RP2Q0WQ0LQ1?P`PVPNPTP0Q1:Q1;fjO;b9b1b;b1P{eb0P{PTPGfnP5P2I01Q1>#2#P#NR{Q1T'1S1T,0U15H2S1>/0T5A\S1;XF4R1,u4Q00P4P1p+01@S1:f~56IP2Q1;P3Q1VPUQ1W,1{S1W15H5S1RPTCRp+01Dp+01C56IP2Q1YPUQ1Z,1{S1Z15H0S1NPTCRP3Q1[,1{S1[,0U15H9S1b/0Tp+01Hp+01G56IP2At{tcS1c,0U15HARU/0TPMPPPgPjPDPkPhPiPnP;Q1_PqPrPr19r6PrPrP0Pr19r9S1_PrQ1GPrQ1IPr%=LR{=4rwQ1MD[D[CK19rfS1d5IrPsQ1aEFPyP|b<b=b>X24X3RX7RX:RX?RX@RXARXERP7P6P0P9A@L28D\=A5tPK[^24^3R^7R^:R^?R^@R^AR^ERP2PFQ0@Q0<Q0;Q0:Q09Q08PVQ01O9b9b1b;b1%HVRKeb0PKPMPPPgPjPDPkPhPiQ1C#MRK/Vl/>nP;Q1F??6pP7PpP5PpDSPqPrPrQ1_Q1HPsPrPrQ1GQ1LQ1I5IrPsPr1;wvR1=4r?PsA4r1zH02EFEFPyP|b<b=b>X24X44X54X3RX7RX:RQ1O,36AB6a7=A98AB7J6AB6Jc[[[^24^44^54^3R^7R^:RP2Q0WQ0LQ1?P`PNPVP0fdfmO9b9b1b;b110WcR1eb0P1PVPJfqP5P2I01Q1T,0WQ1>/0V5A\S1>XF4R\,u4Q00P4P\p+01Op+01N56IP2Q1>P3Q1VPWQ1WQ1RPVCRp+01Sp+01R56IP2Q1YPWQ1ZQ1NPVCRP3Q1[,0WQ1b/0Vp+01WS1bp+01V56IP2Q1c,0W10UVp+01ZRUp+01YS1c'1RWQ06POPUC:PWQ0mQ0oPUC:S0oPWQ0qQ0sPUC:S0sPWP]Q0tPUC:S0tPWQ0uQ0vPUC:S0vPWQ0wQ0xPUC:S0wPWQ0cQ0dPUC:S0uPWPdQ0yPUC:S0qPWQ0zQ0{PUC:S0zPWQ0~Q10PUC:S0~Q1A'3S0m'3S06'3S1['3S1N'3S1Z'3S1R'3S1W'3RW'3PMPPPgPjPDPkPhPiQ1B#MR3/GlS1B,GK,Vm/>nP;PoP7PpP5%O9R\??6pDSPqPrPr%=^%C@R@54rQ1IPsPrPrA4r@uPrPr%CZRZ%=Q60F4R1,TuQ1MC]PsPr1;w?R?=4r{RuPsPrA4r?1Q1dEXEFEFPyP|b<b=b>X24X44X54X64X84X3RX7RX:RA@^691w6Q=@9t9@091176S1V/0LR^1160R11w9Q;JC[[[^24^44^54^64^84^3R^7R^:RP2p+01_RQ,0OQ07Q1@Q02PNPOp+01^ROPQP0Q1bp+01[RNO;b9b1b;b1b0Q0oPWPMPPPgPjPDPkPhPiQ1D#DS1D#DRW#MS0o1G3SS1b'G1b4L/aSS02%DWS1@#DS07#DS00#MRWQ1D#MS1D/GKS1T'G'V,kS'k/>nS1?P;PpP7A?\8pP5PpP8%O8S0L??8pP6PoDSDSS0WPqPrQ05#CS05,^{S1O=4rZS1LPsPr1;ZxQ05/^z,;vS0554rS1HPsPr%=HS1CQ04#CRz54rS04Q1M5IrS1aPsPr%C[R[94r{S1ePsPrPuPsPrA4rvwS1fPsPrPrQ0l,QZ,T?Q0n,QZ=4rwC`F8F8F8PyP|b<b=b>X24X44X54X64X84XB4X3RQ1\/07S1\Q1P158c7eJS1PA@H8AS1g10L8S1hAB09LS1i10J9S1j118tS1kQ0l,1AQ0n=BA83J[[[[[[^24^44^54^64^84^B4^3RP2Q0Xf`S0nP`PVPTPOPQfSS0lfTS1lfrRcQ1:PNp+01]S1mO=S1nb9b1b;b1b0Q0sQ1WPMPPPgPjPDPkPhPiQ1?P;Q0WPqPrQ1LPsPrQ1HPsPrQ1aPsPrQ1ePsPrPuPsPrQ1fPsPrPrQ0p,QZ,T?Q0r,QZ=4rwC`F8F8F8PyP|b<b=b>X24X44X54X64X84XB4X3RQ1\Q1PQ1gQ1hQ1iQ1jQ1kQ0p,1AQ0r=BA83J[[[[[[^24^44^54^64^84^B4^3RQ1nb9b1b;b1b0Q0tQ1RPMPPPgPjPDPkPhPi1b4_S1RQ0o'aQ1DQ1b'G5hWQ02Q00#D#D#D#MQ1R/aW&0D:-0C4S1RQ1@#M5p4S1@Q1T'G3h'V,kS'k/>nS02P;A?\ApP7%OtS1T??ApP5Q0LPA%OAS00??ApP6PoDSDSS1bPqPrQ1O=4r[S1OPsPr1;[xQ0554rS05PsPrQ0419rCS0t5IrS04PsPr%=XS1nQ0|#CR:54rS0|Q0F#=94r:5IrQ0I,Q[%=_S1\,^:';,iZ,|r5IrS1PPsPrQ1J94r{S1JPsPrPuPsPrQ1fPsPrA4r?ZS1g%=eS1h,;Z=4rwEXF8F8F8PyP|b<b=b>X24X44X54X64X84XB4XC4XD4X3R15Lt/06S1iQ1QQ1]'0S1]10HAS1Q/3CS1j10XAS1kQ0F7lAQ0I,1815A_5U9'3S0I10LAS0F1198S0r/0LS0p10J8R{11tAR[ABfet7Jf[[[[[[[^24^44^54^64^84^B4^C4^D4^3RP2Q0XQ0nP`PYPVPTP]POPQQ0lQ1lPcfvR]Q1:PNQ1mO@S1mb9b1b;b1b0Q0vQ1ZPMPPPgPjPDPkPhPiQ02P;Q1bPqPrQ1OPsPrQ05PsPrQ04PsPrQ1PPsPrQ1JPsPrPuPsPrQ1fPsPr1QZB94r?S1fQ1\,;Z=4rwEXF8F8F8PyP|b<b=b>X24X44X54X64X84XB4XC4XD4X3RQ1iQ1]Q1jQ0IQ0FQ0p11fBABf_t5J[\{[[[[[[^24^44^54^64^84^B4^C4^D4^3RQ1mb9b1b;b1b0Q0wQ1NPMPPPgPjPDPkPhPi1b4e/aWQ07#MQ1@Q1RQ0o5p4Q0O,b4Q1D'a1GmS3h3h'VRSQ1E,G3,VK/>n,>S,>S,>S,>S,>S,>S'>P;PoP7Q0L%Of7?fP5P\PfQ00P6Q1T??fpDSDSPqPrPr19r~RSPrQ1^,9rRWPr19rbPrPrQ1`/T@Q11,9rC]D[PsPrPrQ1CQ0H#CR{54rPrPrf?S0HPrPrQ0R#CR[Q03#7#CR_Q0O#='^,;{'iPrPrQ0S,Q[,iZf@,9rC]C]CKPsPrPrPrPrQ1n/T_Q13,9rC]Q12,9rPsPrPuPsPrPrPrfCPrPrPrfDPrPrQ15PrPrQ14PrPrfGR[PrPrfHRwPrPrQ17PrPrA{zx:1;:xRx=4rzC`CKCKCKCKCKCKPrQ16,9rPrPrQ1SPrPrPr1Tx{Q1K,;{Rx=4r:C`PrPrPrA{zv{A4rxzC`fLRx,9rD[CKD[CKPsPrPrQ1h/^@,;Z,T?Q19,9rC`F8EFEFEFPyP|b<b=b>X24X44X54X64X84XB4XC4XD4XW4X3RX7RX:RX?RX@RXARXERXURXVRXKRXLRXMRXNRXORXPRXQRXRRXSRXTRPfPCP~Q1XQ1^D\Q1QQ11Q0O,5t9UfAQ0S9U6fQ0HD\Q1kQ13'3Q12'3101LQ15Q14P[PwQ17Q16Q1S11fGPA11AGRGPfC:3AD\PxQ19PGP~11~aRaPAC:11fJP~PaPfC:Q183AD\Q0rAtteAfP3J[[[[[^24^44^54^64^84^B4^C4^D4^W4^3R^7R^:R^?R^@R^AR^ER^UR^VR^KR^LR^MR^NR^OR^PR^QR^RR^SR^TRP2Q0x/0QQ0gQ0YQ0KQ0>Q0=Q0<Q0;Q0:Q09Q08Q0JQ0GQ0VQ0MQ0`Q0^Q0]Q0\Q0NP`PYPVPTQ0_Q0QPOPQQ1<PcP]PNQ01OQb9b1b;b1b0Q0uQ1[PMPPPgPjPDPkPhPiQ1B$0B/>nP;%O7RTQ1F7?5PqPrPrQ0b#==4rZQ1_PsPrPuPsPrQ1gQ1GEXEFPyP|b<b=b>X24X44X54X3RX7RQ0b?@76AB57LQ1V?J08[[^24^44^54^3R^7RP2Q0d/0QQ0eQ0cPOPQQ1=PNO7b9b1b;b1b0Q0qQ06PMPPPgPjPDPkPhPiQ1R=p4K1b4E/a3;hl,Vm/>nRmP;PTP5A?o9pP6A?\9pI0AR\PqPrPrPrQ1C/T_PrQ1IPrQ1MQ1dQ0U,Q_%=E,^:';,iZ,|r5IrD[C]R:PsPrQ0|Q0t5Ir=IrSRSPsPrPuPsPrQ1gPWEXF8PyP|b<b=b>X24X44X54X64X84X3RX7RX:RX?RX@RXARQ0U,10156E5U7,3t9A989@H0RHA@X0f/3CRCAJ19b\^[[^24^44^54^64^84^3R^7R^:R^?R^@R^ARP2Q0y/0QQ0JQ0GQ0TQ0PQ0MP`PYPdPOPQPcP]PNO>b9b1b;b1b0Q0zQ0mPMPPPgPjPDPkPhPiPmP;P\PqPrP:PsPrPSPsPrPuPsPrQ1fPWEXF8PyP|b<b=b>X24X44X54X64X84X3RX7RX:RX?RX@RXAR119B=J1b\^\C\H^24^44^54^64^84^3R^7R^:R^?R^@R^ARP2Q0{/0QQ0JQ0GQ0TQ0PQ0MP`PYPdPOPQPcP]PNO>b9b1b;b1b0Q0~Q1APMPPPgPjPDPkPhPiPmP;P\PqPrP:PsPrPSPsPrPuPsPrQ0},QZ94r?PWEXF8PyP|b<b=b>X24X44X54X64X84X3RX7RX:RX?RX@RXARQ0},19=J1b\^\C\H^24^44^54^64^84^3R^7R^:R^?R^@R^ARP2Q10/0QQ0JQ0GQ0TQ0PQ0MP`PYPdPOPQPcP]PNO>b9b1b;b1b0PMPPPgPjPDPkPhPiPnP;PpPqPrP<P=P=P>I0@PyP|b<b=b>Q1AP2b9b1b;b1b0FcFcFcFcFcQ1c96IUeWmWjP5P2O2n2001000010121000000W0WgP5P2O2n2011000010121000000W0Xr4P5P2O2n2011000010121100000bHbGbIWnWkP5P2O2n2001000010121000000W0WhP5P2O2n2011000010121000000W0Xs4P5P2O2n2011000010121100000bHbGbIWpWoP5P2O2n2001000010121000000W0Xl}P5P2O2n2001000010121000000W0WiP5P2O2n2001000010121000000W0Xt4P5P2O2n2011000010121100000bHbGW^W\P5P2O2n2001000010121000000W0WZP5P2O2n2011000010121000000W0W_P5P2O2n2011000010121000000W0W]P5P2O2n2111000010121000000W0WYP5P2O2n2011000010121000000X0FWfWbP5P2O2n2001000010121000000W0WaP5P2O2n2001000010121000000W0W`P5P2O2n2001000010121000000W0WeP5P2O2n2001000010121000000W0WdP5P2O2n2001000010121000000W0WcP5P2O2n2001000010121000000W0P5P2O2n2111000010121000000W0W[P5P2O2n2011000010121000000A6I90ebqUUUXF4XX4o"). Qed.
Lemma RK0_obj : forall A k, ((6352896 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof.
ltac2:(KReplay.run1 (kr_t_ACdeallocP ()) ["CANSEC1"; "Kinds0"] "p'0h02H4h16__sat6h24__x1h34__x2h44__x3h54__p1h64__p2h74__p3h84__p4h94__p5h:4__p6h;4__p7h<4__x4h=7__arithh>5__p10h?5__p11h@4__p8hA4__p9hB6__sat5hC4__x5hD4__x6hE4__x7hF4__ffhG8__varmaphH5__withI5__p12hJ5__p13hK5__p14hL4__x8hM1khN2G0hO1ehP1GhQ2HahR5__p15hS5__p16hT5__p17hU5__p18hV5__x10hW4__x9hX1AhY3F_chZ5F_csbh[4F_loh\4F_muh]4F_sbh^4F_shh_5F_tsbh`3Fc1ha3Fc2hb3Fc3hc3Ft1hd3Ft2he3Ft3hf3Ftchg5KAFc1hh5KAFt1hi5KAFt2hj5KBFc1hk5KBFt1hl5KBFt2hm5KCFc1hn5KCFt1ho5KCFt2hp5KDFt2hq3KF'hr4kFc1hs4kFt1ht4kFt2i001xp%0p%1p%2p&0p;1p;2p;3p;4p;5p;6p;7p;8p-1p10000p4p710R0p8p1000Gp4p710R1p1000dp4p710R2p8P1p1001@p4p710R3p8p1001^p4p710R4p1002<R5p4p710R6p8P4P5p4p7210R5p8p1002Up4p70R7P0p8P7P2p8P7P1p8P7P3p8P7p1003Lp4p710p8P7p1003iR1p4p710p8P7p1004Fp4p710p8p1004bp4p710R7P4p8P7P6p8P7P5p8P7p10056p4p73110p8p1005Hp4p710P2p8P1p4p7210P3p8p1006Ep4p710P2p8p1006dp4p7210P2p8p1007Cp4p710P3p8g00:Vj1=Tg009Sj12Tg00QWk10]Tg00:8j1ATg0096j21Tg00X6k201Tg00XSk20UTg008Zj20Tg007ek20<Tg00Nok20PTg00;;R3j23Tg00;Vj28Tg00Y0k20KTg00<Mk104Tg00YPj39Tg00PYk10FTg00ZLk20ETg00[4k202Tg00[Pk30CTg00\4k20\Tg00C@k20BTg00RMj1>Tg00Rlk20@Tg00<mk10ZTg00=kk10YTg00>gk10XTg00?Ek10WTg00A6k10VTg00@Sk20?Tg00B^k20TTg00CZk20STg00DFk30=Tg00D`k30RTg00E?k40QTg00\Uk40OTg00<3S00j2~Tg00@0j2|Tg00]Sk50:Tg00^Qk30MTg00_4j2tTg00`Ik10JTg00`gk20ITg00aHj3vTg00B;j3rTg00b1k50GTg00Lij2fTg00bUk409Tg00Tjj3RTg00SUj3uTg00T>k20DTg00=Mk20NTg00>Ij4pTg00UJk60>Tg00FKj4ZTg00G6j7PTg00AXk300Tg00GZj7iTg00H>j8qTg00c5j7jTg00cYk30[Tg00dBk40ATf0R2#=#2p=d%22#2#2#2p=U%=2#=p=X%22#2#2#2#2#2#2#Ap=V%=2#=#=#=p=If2R1f1R7'1/02p=M1017/32p=L%22#2p={%22#2#2p=y%22#2#2#2#2#2#2#2p=Q1072,f1p=`g00KfR5/02p=Df4R6f3R4'1/011072'fp=T%22#2#2#Ap=\g00JAR0117280=1p=^1317/32p>071372,31p=N10411072'fp=;f6R8f5R91372,31,34,36'3'3p=H1072,31p=bP0P0P9P6H09P0P0P1P7H09=R425R8p=k20@02p=CAu072p=JAu072g00WJ+0Dp=Bg00MCR:?R72p=o20N02p=OP0P1P7P2Cpp=EP0P0P6P4P1CpP7P2Cpp=]P7g00HbR;g00IAR<P<g00IaR=P2J0>p=<20?02p=F1|02p=?P1P;P<P<P=P0P7g00J_R>P2CZg00KFR?FPp=4B00072p=:P1P;P<P<P=P7P2Fip=SP8P;P<P<P=P9P6P4P;P<P<P=P1P7P2GqGqp=7P9P;P<P<P=P6P;P<P<P=P4P1FiP7P2Gqp=G10411072'3p=W1172,01p=m1872,11p=}P4P;P<P<P=P1P7P2Gqp>0;P6P;P<P<P=P4P1P;P<P<P=P7P2FiFip=5P4P;P<P<P=P1P;P<P<P=P7J0>P2Fip=g1372,31,34,36p>08Au0729u01p=[AR:729R:19R:49R:6p=6P0P7P>P2CZp=YP4P;P<P<P=P1P;P<P<P=P7P?FPP2Fip=aP8P;P<P<P=P9P;P<P<P=P0P6P>P4CZP?FPP1P;P<P<P=P0P7P>P2CZP?FPFjp=@P0B00017P>P2CZp=lP4P;P<P<P=P1P;P<P<P=P7P?FPP2Fjp>0LP6P;P<P<P=P4P;P<P<P=P0P1P>P7CZP?FPP2Fjp>061017/f2p>051141/07/f2p=hP4P;P<P<P=P1P7P;P<P<P=P2P?FPFjp=z1|02:0007p=KP9P;P<P<P=P6P4P1P;P<P<P=P7P2FjGqp=_10641117/02'fp=cB0[072p=eAR:729R:1p>03P0P7g00d]P2CZp=sP7P;P<P<P=P2P?FPp=xP9P;P<P<P=P6P;P<P<P=P4P?FPP1P;P<P<P=P0P7P>P2CZP?FPFjp=wP0P6P4P0P1P7P2CpCpp>0HP8P9P6P4P1P7P2H0AH0Ap=ng00LDR?#d#U#=#X#d#U#VR>%=?R@#=RA#XRB#X#I#IRC#2#=#XRD#2#U#VRE9M727L7%2?RF#2RG#2RH#2RI#2RJ#2RK#2RL#{RM#yRN#2RO#I#I#I#I#Q#VRP;`7p,2rcRQ$0]RR9M17%D1P6P4p,1tRS%ANRN,1SRTP6DTP9P6p,2SBRU%yORO#QRV#d#U#VRW,1URXP9DTp,2KFS01g00eDP3p,2loS02Q02p,2spRY%=FS03#2RZ#XR[#2#\R\+01S04%AFR]%AKRK+0UR^,0YS053L5LRS0620<SNR_20PSNR`10TRRap,3ctxRb%AORO+0<Rc10>bS0711bORd/0RS08PbPNPSPTPbDTS09'3S0:'3S0;'3S0<'3S0='3S0>'3S0?%A?Rep,1cRf'0%ABS0@,0fp,2CARB%2@Rg#=S0A#2#\S0B,1S%\ZRh,8f3^S0C407S0D10PUS0E10XRS0Fp,2RBS0G%2V#URV#yRi#AS0H,8f7^US0Ip,2FAS0JQ0G%2AS0K#2#U#Q#Q#VS0L3^S0Mp,2RIRj%2i#URi#AS0N,1U%ALRL,8f3^S0O3NS0P'3S0Q'3S0RPTPUPXPSC;S0SPdPUPXPbC;S0Tp,2auRX#DS0Up,2muRk,0XS0VQ0L,0kS0Wp,2nfS0X#D%AGRkQ0X'8RXp,3mfaRl'0S0Yp,4mfa'S0Z,0lS0[Q0Z%AVS0\'0FHS0]%dM#{#=#X#I#I#d#X#d#U#VS0^p,4SHF0S0_Q0_p,4SHF1S0`'0S0aQ0`;bP3LS0b'3S0c'3S0d'3S0e'3S0f'3RM'3S0g20K00RVQ04PYPV%=[R[#2Rl#2#\Rm,1SS0h%=l#\S0i,1SS0jPV%d[#\S0k,1SS0l%2gS0m#2#X#{#\S0n,1SS0oPVPB11BkS0pPV%AIS0q,1BS0r11BhS0sPVQ0J/1XS0tQ0JQ0Z'1S0uPVQ0_Q0`PVPj%AHS0v,1jS0wPVQ0q,1jS0x%AJS0y,1jS0zPV%=GS0{#\S0|,1jS0}11jLS0~&04VFkFkFkFkFkRVf8RJf7RX39P2Q06Q0gP3Q0?PMf<RIf;R[59VP2Q0?P3P_Q0>f@S10f?S1159V\MP2Q0>P3P`Q0=fDS12fCS1359V\MP2Q0=P3PaQ0<fHS14fGS1559V\MP2Q0<P3PcQ0;fLS16fKS1759V\MP2Q0;P3Q07Q0:fPS18fOS1959V\MP2Q07Q0:P3Q08Q09fTS1:fSS1;59V\MP2Q08Q09P3Q0DQ0ffXfWRl59VP2Q0DQ0fP3Q0RQ0ef\f[59VP2Q0RQ0eP3Q0SQ0df`f_59VP2Q0SQ0dP3Q0TQ0cfdS1<fc59VP2Q0TQ0cP3Q0]Q0bfhfg59VP2Q0]Q0b&0FQRQ%=D#I#Q#Q#V/0RS1=%=C#I#I#Q#Q#VRC7bRRD20E]KRn2025]Ro%DK2025^[Rp[Rq%D]Rrg00f@S1>B0C]K7UWQRKQ1>%D^[^QrRrP7g00f\20\5]+0BPoeO1RoPpp-0R]g00VkR^#>Rs#>S1?#>S1@#>S1A#CS1B%CsS1C20@0^S1D'JS1E'B&04:R^'o&0Z:R:%O6S1F&0Y0Rs7E6P1PsP7%O4Rt?E6sD]&0X0Ru&0W0RvPv1<v8S1G%FFRF%?C54vS1H&0V<RwPvPv1<vXRx%FHRH%?WS1I':=4vFS1J1<vJS1K5SvPwPvQ03#FS1L%?ORy':=4vFPwPv20?0?Rz%?NR{':R|=4vFPw%Ui#Q#Q#VRi#?S1M94v|F7EGEG20Tv=R|P2P1g00MoR}g00NOR~+0B20S21>0=}~dB0R057H0QR~bFbGbHX20X30X40X<0X5]X6]W7S1N107CS1O,36AM6W1=N8X116OS1P/04AM4N6116NS1Q/0i[[[[^20^30^40^<0^5]^6]^7]S1RP2Q0PQ0EQ1=PUPbPRPSP6fBS1SQ17PlO;b=b1bBb110TiRCeb0PCPSPNPlP2H0O%D2?b2eRl10NSS1TPT182iS1U,1O18>2PSCW3NS1VXM0R},~0Q00P0P}fnS1WfmS1X59VP2Q1VP3%D7S1Y?b7eS1ZQ1T187iS1[9mTO18>7/0S3NfrS1\fqS1]59VP2%D4S1^?b4eS1_Q1T186iS1`9mTO18>6/0S3NP3Q1TPT189iS1a,1O18>9PSCWfvS1bfu59VP2Q1TPTA}OJi18>JPSCWP3f9R}/8i9mTO18>}/0SfzS1cfy59VP218[i9mTO18>I/0SPQPDPnPqPKPrPoPpP^P:%O7S1dPuPvA4v{zPw1|05S1e=4vzS1fH0;P|P~bFbGbHX2010N2Q1Y[^20P2PSf:R5O2b=b1bBb1%DSS1geb0Q1gPQPDPnPqPKPrPoPpQ1NQ1RP2Q0PQ0EQ1=PUPbPRPSP6fUf^fjS1RO;b=b1bBb1PCeb0PCPSPNQ1WP7P2I0:Q1U,1ES1U,0T18P2S1N/0S5NlS1gXM0RC,~0Q00P0PCp+01Bp+01A59VP2Q1gP3Q1ZPTQ1[,1ES1[18P7S1hPSCWp+01Fp+01E59VP2Q1_PTQ1`,1ES1`18P6S1iPSCWP3Q1a,1ES1a,0T18P9S1j/0Sp+01Jp+01I59VP2A}EXiS1k,0T18PJRT/0SPQPDPnPqPKPrPoPpP^P:Q1dPuPvPv1<v4PvPvP6Pv1<v9S1dPvQ1GPvPxPv%?>=4vzQ1KD5D5Cg1<v}S1K5SvPwQ1fEGP|P~bFbGbHX20X5]X6]X7]X8]X9]X:]X;]P1P4P6P9AL>28I08=N7XQ1Y[^20^5]^6]^7]^8]^9]^:]^;]P2PMQ0:PcPaP`P_Q06PbQ01O9b=b1bBb1%DbRCeb0PCPQPDPnPqPKPrPoPpQ1@#CRCQ1E'B/o^P:AEt4sP1PsP7PsD]PuPvPvQ1dQ1HPwPvPvQ1GQ1J=SvxPwPv1:zyRx=4vFPwQ1M94vxH0;EGEGP|P~bFbGbHX20X30X40X5]X6]X7]Q1O,34AM4W1=N98AM1O4AM4Oi[[[^20^30^40^5]^6]^7]P2Q0PQ0EQ1=PUPRPbP6Q1<Q1XO9b=b1bBb110diRieb0PiPbPOQ1]P7P2I0:Q1U,0dQ1N/0b5NlS1NXM0Rl,~0Q00P0Plp+01Qp+01P59VP2Q1NP3Q1ZPdQ1[Q1hPbCWp+01Up+01T59VP2Q1_PdQ1`Q1iPbCWP3Q1a,0dQ1j/0bp+01Yp+01X59VP2Q1k,0d10Tbp+01\RTp+01[S1k'1RdQ04PYPTC;PdQ0hQ0jPTC;S0jPdQ0lQ0oPTC;S0oPdPBQ0pPTC;S0pPdQ0rQ0sPTC;S0sPdQ0tQ0uPTC;S0uPdQ0_Q0`PTC;S0tPdPjQ0wPTC;S0wPdQ0xQ0zPTC;S0zPdQ0}Q0~PTC;S0~Q1>'3S0}'3S0x'3S0r'3S0l'3S0h'3S04'3S1j'3S1a'3PQPDPnPqPKPrPoPpQ1A#>Rd#>S1A#CR3%CdS1iQ1BQ1D3['BRdPdPdPdPdPdPdPdP^D6D6P:Q1FP1%OJS1`?E8sP7%O9S1h%OXS1[7E4D]PuPvPv%FGRGQ1L54vPvPvQ1L%F@R@%?\60M0S1Z'Y1<v5S00CaPwPv1:zFRd=4vGPwPvPv1<v[S1UPvPv1<vIS1]Pvf=Rl,<vS1XPvf>Ri,<vS1<PvQ11,<vS1=PvQ10,<vS0EPvfAS0P,<vS1OPvPv%FARA/:{S1M%FgRgPv1:g{RxPAF@D5D5D5PvQ1S,<vS1JPvQ13,<vS1GPvPvPvPx%FZRZPvQ1I,:ZRxPgF@PvPvPvAlAyZA4vxAS1HH0LQ12,<vS1dD5D5D5PwPvPvPdQ1ZfES1Z,<vS1EI06F7EGP|P~bFbGbHX20X30X40X<0XC0XD0XE0XL0X5]X6]X7]X8]X9]X:]X;]X@]XA]X>]X?]XI]2011\=L6J9L461171S1@/06P[PIPlPiQ11Q10Q0P11JNS1YPX11XNS1fPJC;RgFHQ1SQ13Q1f11}WS1l/0XS1m805}PJPOP}Q1lPJDTQ12FHP4P62019\fFS1lCh[[[^20^30^40^<0^C0^D0^E0^L0^5]^6]^7]^8]^9]^:]^;]^@]^A]^>]^?]^I]P2p+01aS1n,0YQ0cQ0RQ0DQ08Q07PcPaP`P_Q06Q05PUPbPSQ02PRPYp+01`S02Q1np+01Wp+01^Q01OGb=b1bBb1b0Q0jQ1aPQPDPnPqPKPrPoPpP^P:%O1?E7tRtPuPvPvA4vd@S1aPvAl@{zCzRYPwPv1K@m94vdQ0i,K@=4vzE_P|P~bFbGbHX20X30X40P2P7P1AM1N2ChRRQ1@114mP4Q0iP7Dc[^20^30^40P2PSQ02Q1nPTO4Rmb=b1bBb1b0Q0oQ1jPQPDPnPqPKPrPoPpP^P:PtPuPvPYPwPvQ0k,K@94vdQ0n,K@=4vzE_P|P~bFbGbHX20X30X40Q1@Q0k,14P4Q0nP7Dc\R^20^30^40Pmb=b1bBb1b0Q0pQ04PQPDPnPqPKPrPoPp1t0hRmQ1A#>RR#>#>RY#>Rt#CS1A'e%CYRYQ1D7[3'BR\%>tS04#CS0p,emRm&0J?-0I0S0n=v0YR?Q1C7[3'BRt%CRS0kQ1C'JS1@9[m?,BCR?Q0kQ1i7[3S1j,BCS0oQ0oP?PtP\P\PtPtP\P\PtPtP\P\PtPtP\P\PtPtP\Q0oQ1?#CS1?Q1B,JC'BR3P3P31o3^D6S0i,o?:03\tD6D6D6D6D6D6S0jP:Q1h?EXsS05P1Q1[?EXsP7%O8S1o?EXsS1pQ1F7E4D]S1qPuPvPvPv1:HyS1rPZPvPxPHF@S1sPwPvPvPvQ1MPZQ1HI06S1HPwPvPvPv%?PRt/YZQ1KCaS1tPwPvPvPv%?eS1uQ0{#FR\'YQ0@#?S0{94v\CaS1vQ0B,KA%?hS1w9r0\':,s@,xv5SvS1xPwPvPvPv1:H{S1yPAPvQ1MPHF@S1zPwPvPvPvPdPZPvPxPzF@S1{PwPvPvPvPdPAPvQ1MPzF@S1|PwPvQ1e=4vFS1}PwPvPvQ00PvPvQ1UPvQ1]PvQ1XPvQ1<PvQ1=PvQ0EQ1zD5D5D5PvQ1OPvQ1JPvQ1HPvQ1sQ1GD5D5D5S1~PwPvQ1a%?kS20,:@=4vzE_F7F7F7F7P|P~bFbGbHX20X30X40X<0XC0XD0XE0X5]X6]X7]X8]X9]X:]X;]X@]XA]X>]X?]Q1PP8P8PWP6DcRFQ1QPX11XWS1QP6C;Rx10PJS1P/3}S21PePJPJQ0@CWS22Q0B,1818Jh5^9'3S0B1198S23P[P[PWP9DcR?118XS24P}11}NS25P8C;Rm%DJRRQ10Q0PQ1SQ13Q12Q1ZQ1l11INS26P[11[NS27PIC;S28FHQ15Q14Q27Pi11iWS29P[C;S2:PIPOPiQ29/0IS2;ChS2<fIS2=FHS2>11}5S2?/0[S2@11[k;`}[[[[\g[[[[^20^30^40^<0^C0^D0^E0^5]^6]^7]^8]^9]^:]^;]^@]^A]^>]^?]P2Q0cQ0RQ0DQ08Q07PcPaP`P_Q06Q0QPUPfPbPSPBQ02Q1nQ1RQ1WQ1\Q1bQ1cQ1kPTp+01]S2AQ01OKRBb=b1bBb1b0Q0sQ0hPQPDPnPqPKPrPoPpQ0jP:Q1qPuPvQ1sPwPvQ1HPwPvQ1tPwPvQ1xPwPvQ1zPwPvQ1{PwPvQ1|PwPvQ1}PwPvQ1~PwPvQ0q,K@94vdS1~Q1w,:@=4vzE_F7F7F7F7P|P~bFbGbHX20X30X40X<0XC0XD0XE0X5]X6]X7]X8]X9]X:]X;]X@]XA]X>]X?]Q21Q0BQ2>Q2?Q0q7m[S0q11[h;`}[\R\m\?\g[[\x\F^20^30^40^<0^C0^D0^E0^5]^6]^7]^8]^9]^:]^;]^@]^A]^>]^?]PBb=b1bBb1b0Q0uQ0lPQPDPnPqPKPrPoPpP3P3P3P3Q0o1t0kQ04#>RB#>S04#>#>#>S0l#>#C'eQ0n%CBS0u5v0Q0nQ0p5v0S0nQ0H,t0RBQ1A'eQ1@'J3['BRhQ0l#CQ0uQ0p1eBYQ0kQ1D'JS0k'J3['BRBPBPBPBPhPhPhPhQ1?Q1BQ1j'J'BS1?PBPBPBPhPhPhPhPBPBPBPBPhQ0oQ0oPhPBPBP^D6D6D6D6D6D6D6D6P:Q1FP1Q1[%O57E5P7Q1oP9%O}P4Q1`?E5sD]D]PuPvPvQ1]PvQ1XPvQ1<PvPvQ1e/YGPvQ1=PvQ0EQ1LQ0\#?54vD5CaD5PwPvPvPvQ0A#FRB9lZyPvQ1I,:BS0APZEwS1ePwPvPvPv1:\{S1`PBPvQ0AP\F@S1oPwPvPvA4vtBPvQ1OPvQ0K#FS0KQ03#=#FRhQ0H#?5r0,:B's,xvPvPvQ0KQ0L'K,s@Q1JCaD5PwPvPvPvPvQ1u/YhQ0{94vhCaQ1GPwPvPvPvAlZ{\PvQ1`PZEwRZPwPvPvPvPdPBPvQ0APzF@PwPvPvPvPdP\PvQ1`PzF@PwPvQ1}PwPvPvQ1dPvPvQ1EPvQ1l,<vRBPvPvQ15PvPvQ14PvPvQ2=PvPvfJR{PZCgCgCgCgD5PvQ17,<vPvPvQ16PvQ1oPvQ1efMRZ,<vD5CgD5PwPvPvPdQ20=r0G,:@PvQ1L,:@PzF@EGF7F7EGEGF7EGP|P~bFbGbHX20X30X40X<0XC0XD0XE0XL0XW0XV0X5]X6]X7]X8]X9]X:]X;]X@]XA]X>]X?]XI]XJ]XK]XR]XS]XT]XU]P5P[PIQ1^PlPiQ0\,06FHPXPOP}Q1mChQ1fP5P5PWPXDcQ1SQ0H,859^I[Q0L9^9IQ13'33N9LP[10e[Q0@,0[Q1Z407Q27P5P5PNP[DcQ24PiQ29P8C;11XJRePIQ26PXC;%D}Q17Q16PZfNQ19Q18fQQ11PNPi11iNRZQ11DTFHfRQ1;PZQ0PQ0P/1WRZPiC;Q11POQ0PPZQ11DTQ1:FHP5P[A}IklAMIi5Ch[[[[[[[[[[^20^30^40^<0^C0^D0^E0^L0^W0^V0^5]^6]^7]^8]^9]^:]^;]^@]^A]^>]^?]^I]^J]^K]^R]^S]^T]^U]P2Q0cQ0RQ0DQ08Q07PcPaP`P_Q06Q0CQ0OQ0FQ0[Q0YQ0WQ0VQ0UQ0GPUPfPbPSQ0ZQ0XQ0JQ02Q1nffQ1RQ1WQ1\Q1bQ1cQ1kPTQ2AQ01OVb=b1bBb1b0Q0tQ0rPQPDPnPqPKPrPoPpQ04#CQ1iQ1C'J'BRkQ0uQ0k9[CY'BRCQ0uQ1iQ1D'J'BRZPkP3P3P3P3PkPZPZPkPkPZPZPkPkPZPZPkPkPZPZPkPkPCPZPkPkPZPCPkP^D6D6D6D6D6D6D6D6P:Q1hQ1[7E6P1PsP7Q1p?E4sD]PuPvPvQ0^#?=4v@Q1KA4vGt5SvPwPvPvPvQ0m#FRk9l\yPvQ1I,:kRyP\EwRCPwPvPvPvQ1yPkPvPyPHF@RyPwPvPvA4vtkQ00PwPvPvPvQ1`PHPvQ1yP\F@RkPwPvPvPvPdPHPvQ1yPzF@PwPvQ1}PwPvPvQ1U%?E94vd5SvPv1YtzCzPwPvPvQ1]PvPvQ1XPvQ1<PvQ1=PvQ0EPvQ1OPvQ1JPkD5D5D5PvQ1GPvQ1dPvPyQ1E9SvCD5D5PwPvQ1aPv1YGzCzEGF7F7EGF7EGP|P~bFbGbHX20X30X40X<0XC0XD0XE0X5]X6]X7]X8]X9]X:]X;]X@]XA]X>]X?]XI]XJ]Q0^AbX4P7L1P8POPXQ1QP8DTP8PNPJAMJW8ChALP}[Q25PJQ1YP}C;Q23P}Q25P9C;%DXQ10?beE?`PXQ1SQ13Q12Q1ZQ1lQ15Q14PlPNPIQ26PlDTFHQ2=P{Q26Q2;805iPlPOPiQ29PlDTQ17FHQ2@?`I}[[[[[[[[[^20^30^40^<0^C0^D0^E0^5]^6]^7]^8]^9]^:]^;]^@]^A]^>]^?]^I]^J]P2Q0cQ0RQ0DQ08Q07PcPaP`P_Q06Q1n,0>Q0QQ0aPUPbPSQ0`Q0_Q02Q1nfeQ1RQ1WQ1\Q1cPTQ2Ap+01_Q01OMb=b1bBb1b0Q0wQ0xPQPDPnPqPKPrPoPpQ0p1t0LR>/eYQ0k'J'BRYPYQ0nQ1A,e>Q1@'J'BR>Q0oQ0oP>PYPYPYPYP>P>P>P>PYPYPYQ1?P>P>P>P>PYPYQ0i,o>:03YYD6D6D6D6D6D6RYP:Q05P1PsP7Q1pP4Q1[P6PsI0HD]R4PuPvPvPvQ1rPhPvQ1I,:hR1PHF@RHPwPvPvPvQ1MPhPvP1PAF@RAPwPvPvPv1YthPvQ1KPvQ00Q1UQ0N,Kh%?LRt9r0\':,s@,xv5SvD5CaR\PwPvQ1vQ1]5SvR>PwPvQ1zPwPvPvPvPdPhPvP1PzF@R1PwPvQ1|PwPvQ1}PwPvPvQ1XPvPvQ1<PvQ1=PvQ0EPvQ1OPvQ1JPvQ1GQ1zD5D5D5PvQ1dPvQ1EPvPAPvPHPBD5D5D5RBPwPvQ1aQ0v,K@=4vzE_F7F7F7F7P|P~bFbGbHX20X30X40X<0XC0XD0XE0X5]X6]X7]X8]X9]X:]X;]X@]XA]X>]X?]XI]XJ]XK]Q1PP}P5P[Q0N,1J18XL5^6I08R6Q22/3lRlQ13Q12Q1ZQ1lQ15Q14Q2=Q28FHP{Q17Q2:Q2<Q16FHR{Q2@Q0v,1[;`}[\R\m\?\g[[\x\F^20^30^40^<0^C0^D0^E0^5]^6]^7]^8]^9]^:]^;]^@]^A]^>]^?]^I]^J]^K]P2Q0cQ0RQ0DQ08Q07PcPaP`P_Q06Q0CQ0MQ0IQ0FPUPfPbPSPjQ02Q1nQ1RQ1WQ1\Q1bQ1cQ1kPTQ2AQ01ONRjb=b1bBb1b0Q0zQ0}PQPDPnPqPKPrPoPpPYP:P4PuPvPHPwPvPAPwPvP\PwPvP>PwPvQ1zPwPvP1PwPvQ1|PwPvQ1}PwPvPBPwPvQ1~Q0y,K@=4vzE_F7F7F7F7P|P~bFbGbHX20X30X40X<0XC0XD0XE0X5]X6]X7]X8]X9]X:]X;]X@]XA]X>]X?]XI]XJ]XK]Q0qQ0y,1[;`}\{\R\m\?\g\l\6\x\F^20^30^40^<0^C0^D0^E0^5]^6]^7]^8]^9]^:]^;]^@]^A]^>]^?]^I]^J]^K]Pjb=b1bBb1b0Q0~Q1>PQPDPnPqPKPrPoPpPYP:P4PuPvPHPwPvPAPwPvP\PwPvP>PwPvQ1zPwPvP1PwPvQ1|PwPvQ1}PwPvPBPwPvQ0|,K@94vd1:@t=4vzE_F7F7F7F7P|P~bFbGbHX20X30X40X<0XC0XD0XE0X5]X6]X7]X8]X9]X:]X;]X@]XA]X>]X?]XI]XJ]XK]Q2?Q0|,1[P[PLP}Dc\{\R\m\?\g\l\6\x\F^20^30^40^<0^C0^D0^E0^5]^6]^7]^8]^9]^:]^;]^@]^A]^>]^?]^I]^J]^K]Pjb=b1bBb1b0PQPDPnPqPKPrPoPpP^P:PsPuPvP;P<P<P=I0GP|P~bFbGbHQ1>P2b=b1bBb1b0FnFnFnFnFnQ1k99VTeWmWjP7P2O2n2001000010121000000W0WgP7P2O2n2011000010121000000W0Xr0P7P2O2n2011000010121100000bObNbPWnWkP7P2O2n2001000010121000000W0WhP7P2O2n2011000010121000000W0Xs0P7P2O2n2011000010121100000bObNbPWpWoP7P2O2n2001000010121000000W0WlP7P2O2n2001000010121000000W0WiP7P2O2n2001000010121000000W0Xt0P7P2O2n2011000010121100000bObNW^W\P7P2O2n2001000010121000000W0WZP7P2O2n2011000010121000000W0W_P7P2O2n2011000010121000000W0W]P7P2O2n2111000010121000000W0WYP7P2O2n2011000010121000000X0MWfWbP7P2O2n2001000010121000000W0WaP7P2O2n2001000010121000000W0X`cP7P2O2n2001000010121000000W0XeaP7P2O2n2001000010121000000W0Xd`P7P2O2n2001000010121000000W0Xc_P7P2O2n2001000010121000000W0P7P2O2n2111000010121000000W0W[P7P2O2n2011000010121000000A9VX8ebqUUUUUXM0XX0o"). Qed.
Lemma RK0_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2800 -> 0 <= k -> (A + k <= t + 2784 \/ t + 2792 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 80 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
(* [comment removed for export] *)
Lemma RK0_space_c : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_gap : forall A k, RB + mu <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 32 <= A) -> (A + k <= RI + 72 \/ RI + 128 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_sh : forall A k, 2201439137792 <= A -> A + k <= 17594333495296 -> 0 <= k ->
  (A + k <= SHF0 \/ SHF1 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
End Kinds0.


Lemma repeat_app3 : forall {X} (x : X) a b c, repeat x a ++ repeat x b ++ repeat x c = repeat x (a + b + c).
Proof. intros. rewrite !repeat_app. rewrite app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Lemma AQdr_unbatch : forall R L st X m kb nb b1 ctx l1 l2 drained,
  AQdr R 0 0 L st X m -> qr_pendb R = [kb] -> qr_pend R = [] ->
  x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 -> awf L st X ->
  AQdr (qr_unbatch R) 0 0 L st (xrec st X K_BATCH_CLASS kb l1 l2 drained) m.
Proof.
  intros R L st X m kb nb b1 ctx l1 l2 drained (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EB EP XB WF.
  unfold AQdr, qr_unbatch. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  exact (qcoupled_rec_unbatch L st st X R kb nb b1 ctx l1 l2 drained CP EB EP XB WF eq_refl eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop).
Let AHr := AHr ASECc AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).

(* [comment removed for export] *)
Definition acd24_ret (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (R : qrconc) (cs : list achunk) (lo : Z) (m : amem)
    (stX : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  let c := K_BATCH_CLASS in
  fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (mfa' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (cd_W L (bv_unsigned sp) c (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_unbatch R) cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

Definition store_cd24_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st stX : astate) (X : aconc) (R : qrconc)
         (cs : list achunk) (kb nb b1 ctx lo : Z) (l1 l2 : list xbusy) (tail : list word),
  let c := K_BATCH_CLASS in
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] -> x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 ->
  ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  u32arr bsegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  cdealloc_ret L RNG sp st c (abatch_addr L kb) lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) m stX RNG' m' ->
  exists X' mfa',
       munch (cd_W L (bv_unsigned sp) c (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono bsegs m m'
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_unbatch R) cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cd24_store : store_cd24_stmt.
Proof.
  unfold store_cd24_stmt.
  intros L RNG RNG' sp m m' st stX X R cs kb nb b1 ctx lo l1 l2 tail ALO ARNG AR EB EP XB CEIL LO CH LCH CDR.
  set (c := K_BATCH_CLASS) in *. set (k := kb) in *.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (any_range L st X BBatch c k nb b1 ctx l1 l2 XB WF) as [HC KR].
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof SLOTS as SLOTS0. pose proof SSH as SSH0. destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (ARecRep.max_cached_range c) as (MCR & MCH & MCE).
  (* [comment removed for export] *)
  destruct CDR as (FPLE & drained & mfa' & sj' & sta' & DR & GCX & STE & MFD & NEWB & NEWM & NEWMOD & MU2 & WM2 & MI' & ST' & RECS' & RECc' & CH' & MTX' & REG' & J72' & STATS' & LSJ' & STA' & DRA & FJ' & AZF' & MC').
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  (* [comment removed for export] *)
  set (S := size_of_class c) in *. set (half := max_cached c / 2) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *. set (cnt := c_count (get_cls st c)) in *.
  set (nd := ndist st c) in *.
  set (nf' := if drained then nf + half else nf) in *. set (cnt' := if drained then cnt - half + 1 else cnt + 1) in *.
  set (X' := xrec st X c k l1 l2 drained).
  set (AB := aslot_addr L c k) in *.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE & CAE).
  set (RB := aregion L c) in *. set (FA := afreearr L c) in *. set (RI := aregion_info L c) in *. set (CA := acache_addr L c) in *.
  (* [comment removed for export] *)
  assert (MCle : forall c', max_count st c' <= max_cached c') by (intros c'; unfold max_count; pose proof (ARecRep.max_cached_range c'); destruct (a_cinit st); lia).
  assert (DRC : if drained then cnt = max_cached c else cnt < max_cached c).
  { rewrite DR. pose proof (MCle c) as M. unfold max_count in CNTB, M. fold cnt in CNTB.
    destruct (a_cinit st); cbn [andb]; [destruct (Z.eqb_spec cnt (max_cached c)); [exact e| lia] | lia]. }
  assert (HALF : 1 <= half <= 8 /\ max_cached c = 2 * half) by (subst half; clear -MCR MCH MCE; lia). destruct HALF as [HALF MC2].
  assert (CNT16 : 0 <= cnt <= 16 /\ cnt' - 1 <= cnt /\ 1 <= cnt' <= 16 /\ Z.of_nat (length (xc_cache (x_cls X c))) = cnt /\ nf <= nf' <= nf + 8).
  { subst cnt' nf'. fold cnt in CNTB, LENC. pose proof (MCle c). destruct drained; clear -CNTB LENC DRC HALF MC2 MCR H; lia. }
  destruct CNT16 as (CNT16 & CNTle & CNT1 & LENCc & NFle).
  (* [comment removed for export] *)
  set (st_r := put_cls c (mkAClass mu au nf' mfa' cnt') (init_cache st)) in *.
  assert (STR : stX = st_r) by (rewrite STE, GCX; reflexivity). subst stX.
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (GR : get_cls st_r c = mkAClass mu au nf' mfa' cnt') by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (NDR : ndist st_r c = nd) by (unfold ndist; rewrite GR; reflexivity).
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. destruct (put_cls_fields c (mkAClass mu au nf' mfa' cnt') (init_cache st)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  destruct EF as (EF1 & EF2 & EF3 & EF4 & EF5 & EF6 & EF7 & EF8 & EF9 & EF10).
  (* [comment removed for export] *)
  pose proof (slot_geo L st X c k ALO WF HC KR) as (_ & _ & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  fold S AB RB mu au in AL16, G1, G2, G3, G4, G5, G6, G7, G8, R8, M8.
  (* [comment removed for export] *)
  assert (AU8 : au mod 8 = 0).
  { pose proof (proj2 (Z.div_exact au S ltac:(clear -SZ16; lia)) A3) as EA. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    rewrite ES in EA at 1. rewrite EA. replace (16 * (S / 16) * (au / S)) with ((2 * (S / 16) * (au / S)) * 8) by (clear; lia). apply Z_mod_mult. }
  set (SHF0 := shad (FA + mfa)) in *. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHF1 = shad (FA + mfa') /\ shad FA + shlen mfa = SHF0 /\ shad AB + shlen S <= shad (RB + au) /\ shad (RB + au) <= shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296 /\ 2201439137792 <= shad RB /\ shad RB <= shad AB
                /\ shad (RB + au) + shlen (mu - au) = shad (RB + mu) /\ shad (RB + mu) <= shad FA
                /\ shad (RB + mu) + shlen (3758096384 - mu) = shad FA).
  { subst SHF1 SHF0. clearbody S mu au nf mfa nd RB FA RI CA AB half cnt nf' cnt' c k.
    generalize R8 AL16 SZM M8 A7 NEWMOD AU8 G1 G2 A1 A2 A5 A6 NEWB NEWM HC SP1 SP2 SP3 RBE FAE SZ16. clear. intros.
    rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
  destruct SHE as (SHE1 & SHE4 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH9 & SH10 & SH11 & SH12 & SH13 & SH14 & SH15 & SH16).
  assert (KF : reckf0 (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu au nf mfa mfa' SHF0 SHF1).
  { unfold reckf0. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)).
    clear -H H0 CEIL LO SPR TL1 TL1u TL4u TL2 CL1 CL1u CL3 CL2 CL5 HC CAE SP1 SP2 RBE FAE RIE TSP SCX A1 A2 A5 A6 NEWB NEWM G1 G2 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6 SH10 SH11.
    unfold c, K_BATCH_CLASS in *. unfold iclr, AIMG_LO, AIMG_HI in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [assumption | lia].   (* [comment removed for export] *) }
  assert (MUALL : munch (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) m m').
  { eapply munch_weaken; [| exact MU2].
    unfold sub_fp, cd_W. cbv zeta. fold nf mfa CA FA RI. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW].
    apply outside_app. split; [cbn [outside] in H13 |- *; clear -H13; lia|]. apply outside_app. split; [exact HW|].
    subst SHF0 SHF1. cbn [outside] in H13 |- *. clear -H13. lia. }
  pose proof WM2 as WMALL.
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  (* [comment removed for export] *)
  assert (CPT : (AB - RB) / 16 = acompact c k).
  { subst AB RB. unfold aslot_addr, acompact. fold S. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    set (q := S / 16) in ES. replace (aregion L c + k * S - aregion L c) with (k * q * 16) by (rewrite ES; clear; nia). rewrite Z.div_mul by (clear; lia). reflexivity. }
  unfold abatch_addr in CH'. fold c AB in CH'. rewrite CPT in CH'.
  (* [comment removed for export] *)
  assert (RCUT : drained = true -> rcut st c = Z.to_nat (cnt - half) /\ (Z.to_nat (cnt - half) < length (xc_cache (x_cls X c)))%nat /\ Z.to_nat (cnt' - 1) = Z.to_nat (cnt - half)).
  { intros D. unfold rcut, rcnt, rhalf. fold cnt half. subst cnt'. rewrite D in DRC |- *. split; [reflexivity|]. clear -LENCc DRC HALF MC2. split; lia. }
  (* [comment removed for export] *)
  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count]. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_cache].
    unfold rcache'. pose proof RCUT as RC. destruct drained.
    - destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1. rewrite RC3 in CH'.
      exists (skipn (Datatypes.S (Z.to_nat (cnt - half))) (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c))) ++ tail).
      split; [exact RECc'|]. split.
      + rewrite upd_app_left in CH' by (rewrite length_map; exact RC2). rewrite upd_firstn_skipn in CH' by (rewrite length_map; exact RC2).
        rewrite map_app, <- List.firstn_map. cbn [map]. rewrite <- !app_assoc in CH' |- *. cbn [app] in CH' |- *. exact CH'.
      + rewrite !length_app, length_skipn, length_map, length_firstn. cbn [length]. clear -RC2 LCH. lia.
    - assert (TL : exists t0 tail', tail = t0 :: tail').
      { destruct tail as [|t0 tail']; [exfalso| exists t0, tail'; reflexivity]. cbn [length] in LCH. clear -LCH LENCc DRC MCR. lia. }
      destruct TL as (tw & tail' & ->). exists tail'.
      split; [exact RECc'|]. split.
      + subst cnt'. replace (Z.to_nat (cnt + 1 - 1)) with (length (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)))) in CH' by (rewrite length_map; clear -LENCc; lia).
        rewrite upd_app_right, Nat.sub_diag in CH' by (clear; lia). cbn [upd] in CH'. rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. exact CH'.
      + rewrite length_app. cbn [length] in LCH |- *. clear -LCH. lia. }
  (* [comment removed for export] *)
  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user].
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [| exact J72'].
    eapply cells_frame; [exact EXH | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add].
    apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  assert (FAB : 2201439137792 <= shad FA /\ SHF1 <= 17594333495296 /\ 0 <= shlen mfa /\ 0 <= shlen S
                /\ 0 <= shlen (mu - au) /\ 0 <= shlen (3758096384 - mu)).
  { pose proof (shlen_nonneg mfa ltac:(clear -A5 A6; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)). pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)).
    pose proof (shlen_nonneg (mu - au) ltac:(clear -A1; lia)). pose proof (shlen_nonneg (3758096384 - mu) ltac:(clear -A2; lia)).
    clear -H H0 H1 H2 H3 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6. lia. }
  destruct FAB as (FB1 & FB2 & FB4 & FB5 & FB6 & FB7).
  assert (SB2 : SHF1 <= shad (RB + 4294967296)) by (clear -SH5 FB2 NEWB; pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)); lia).
  (* [comment removed for export] *)
  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array]. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_free].
    assert (FL' : u32arr bsegs m' FA (map (fun k0 : Z => Z_to_bv 64 (acompact c k0)) (xc_free (x_cls X c)))).
    { eapply u32arr_frame; [exact FL | exact MUALL | exact WMALL |]. rewrite length_map, LENF. fold nf.
      apply dj_app; [eapply (RK0_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?FAE, ?RBE; clear -A1 A2 A5; lia | apply ICW_far; rewrite FAE; clear -A5 A6 HC TSP; lia]. }
    split; [| split; [exact FJ'|]].
    - unfold rfree'. pose proof RCUT as RC. destruct drained; [| exact FL'].
      destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1, map_app. apply u32arr_app; [exact FL'|].
      rewrite length_map, LENF. fold nf. specialize (DRA eq_refl).
      rewrite skipn_app, List.skipn_map, length_map in DRA. replace (Z.to_nat (cnt - half) - length (xc_cache (x_cls X c)))%nat with 0%nat in DRA by (clear -RC2; lia).
      rewrite skipn_O, firstn_app, length_map, length_skipn in DRA.
      replace (Z.to_nat half - (length (xc_cache (x_cls X c)) - Z.to_nat (cnt - half)))%nat with 0%nat in DRA by (clear -RC2 LENCc HALF MC2 DRC; lia).
      rewrite firstn_O, app_nil_r, firstn_all2 in DRA by (rewrite length_map, length_skipn; clear -RC2 LENCc HALF MC2 DRC; lia). exact DRA.
    - assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -FB1 FB2 FB4 SHE4 SH3 SH4; lia
                      | apply ICW_far; clear -FB1 FB2 SHE4 SH3 SH4 TL1u; lia]. }   (* [comment removed for export] *)
      destruct MFD as [Emfa|(_ & _ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -A7 NEWMOD NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply fill_is_junk; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }
  (* [comment removed for export] *)
  assert (SLc : aslots L st_r X' m' c).
  { eapply (aslots_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SLOTS0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | |].
    - intros k' Hk' NE'. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|]. split.
      + destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
        apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -Q1 Q2 A1 SZ16; lia | apply ICW_far; clear -Q1 Q2 A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia].
      + intros b Hb. destruct (busy_of_Some_facts X c k' b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
    - intros POS. apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS A1 G2 SZ16; lia | apply ICW_far; clear -A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BBatch c k nb b1 ctx l1 l2 drained XB WF). fold S AB.
      (* [comment removed for export] *)
      specialize (SL k KR). rewrite (busy_of_X_self_g L st X BBatch c k nb b1 ctx l1 l2 XB WF) in SL.
      unfold aslot_busy in SL. cbn [xb_st xb_class xb_slot bany xb_alloc] in SL. fold S AB in SL.
      eapply junk_frame; [exact SL | exact MUALL | exact WMALL |]. intros POS.
      apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1; lia | apply ICW_far; clear -G1 G2 A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia]. }
  (* [comment removed for export] *)
  assert (SSc : aslot_shadow L st_r X' m' c).
  { eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SSH0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | | | exact FB5].
    - intros k' Hk' NE'. fold S. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|].
      destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
      pose proof (slot_aligned L c k' SAL HC) as AL'. fold S in AL'.
      assert (B : 2201439137792 <= shad (aslot_addr L c k') /\ shad (aslot_addr L c k') + shlen S <= shad (RB + au)).
      { rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -Q1 Q2 AL' SZM SH12 R8 AU8. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B FB2 FB5 SH2 SH3 SH4; lia | apply ICW_far; clear -B FB2 SH2 SH3 SH4 TL1 TL1u TL4u; lia].
    - intros POS. fold RB mu au in POS |- *. apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15; lia
                                | apply ICW_far; clear -POS FB2 FB5 FB6 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 TL1u; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BBatch c k nb b1 ctx l1 l2 drained XB WF). cbn [slot_shadow_bytes]. fold S AB.
      specialize (SSL k KR). rewrite (busy_of_X_self_g L st X BBatch c k nb b1 ctx l1 l2 XB WF) in SSL.
      cbn [slot_shadow_bytes xb_n xb_st bany] in SSL. fold S AB in SSL. rewrite <- !repeat_app in SSL.
      destruct (proj1 (proj1 SSL)) as [LWF _]. cbn [cell_wf] in LWF. rewrite repeat_length in LWF. rewrite LWF in SSL.
      eapply cells_frame; [exact SSL | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact FB5.
      apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SH12 SH13 FB2 SH1 SH2 SH3 SH4 FB5; lia
                    | apply ICW_far; clear -SH12 SH13 FB5 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u; lia]. }
  (* [comment removed for export] *)
  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA. split; [| exact AZF'].
    eapply azero_frame; [exact AZU | exact MUALL | exact WMALL |]. unfold K_FREEARR_OFF. intros POS.
    apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16; lia
                  | apply ICW_far; clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 TL1 TL1u TL4u; lia]. }
  (* [comment removed for export] *)
  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. destruct (CLS c' Hc') as (RC2 & FA2 & SL2 & SS2). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. fold RB in REGD.
    destruct REGD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & RD7 & RD8 & RD9 & RD10 & RD11).
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [eapply (RK0_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                         | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 RD10 SB2 SH3 SH4 SH2 SH1 SH13 FB5; lia.
      - eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD9 RD10 SB2 SH3 SH4 SH2 SH1 SH13 FB5; lia. }
    assert (DJI : disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xrec_cls_other st X c k l1 l2 drained c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|]. split.
        * destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c' k0 b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|].
        destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_other st X c k l1 l2 drained c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK0_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X') ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= RB + mu \/ xb_alloc L b + size_of_class (xb_class b) <= RB \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. subst X'. pose proof (xrec_sub st X BBatch c k nb b1 ctx l1 l2 drained XB b Hb) as HbX. apply In_xrec in Hb.
    destruct (BUSY b HbX) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact HbX| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. fold RB au mu S in P5, P4, Q1, Q2.
      split; [clear -P5 RBE HC; unfold c, K_BATCH_CLASS in *; lia|]. split; [clear -P4 A1 A2 RBE HC; unfold c, K_BATCH_CLASS in *; lia|]. left. clear -P4 A1; lia.
    - pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as (R1 & R2 & R3 & _). fold RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      right. destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2; lia | right; clear -D P5; lia]. }
  (* [comment removed for export] *)
  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6352896 ->      (* [comment removed for export] *)
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [eapply (RK0_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2784) \/ (al_t L + 2792 <= A /\ A + k <= al_t L + 2800) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|[H3|H3]]];
      [ eapply (RK0_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    eapply (RK0_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1u CL3 CL2 CL5 SCX; unfold AIMG_HI in *; lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (WF' : awf L st_r X').
  { subst X'. eapply (awf_xrec L st X BBatch c k nb b1 ctx l1 l2 drained XB WF ltac:(intros p; discriminate) DRC st_r mfa');
      [exact EF10 | exact EF9 | exact CIR | exact EF1 | exact EF2 | exact GO | | clear -NEWB; unfold K_FREEARR_MAX; subst nf'; unfold rnf', rhalf; fold nf half; destruct drained; lia | exact NEWMOD].
    rewrite GR. unfold rnf', rcnt', rcnt, rhalf. fold nf half cnt. subst nf' cnt'. destruct drained; f_equal; lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J16 _].
        eapply junk_frame; [exact J16 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STA') as J. cbn in J. exact J.
        * destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ J8].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2768 + 24) by (clear; lia).
          eapply junk_frame; [exact J8 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }
  (* [comment removed for export] *)
  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128);
              (FA + 4 * nf, FA + 536870912); (SHF0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & _).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 SH5 FB2 NEWB CAE HC SH10 SH9 SHE1 NEWM A5 A6.
      pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). unfold c, K_BATCH_CLASS in *. repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (HQ0 : AQdr (qr_unbatch R) 0 0 L st X' m) by (subst X'; eapply AQdr_unbatch; [exact HQ | exact EB | exact EP | exact XB | exact WF]).
  assert (QU : quar_untouched L X' WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X' X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]).
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : AQdr (qr_unbatch R) 0 0 L st_r X' m').
  { eapply AQdr_frame; [exact HQ0 | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; first [apply iff_refl | clear; tauto | tauto]|].   (* [comment removed for export] *)
    rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5). apply Permutation_refl. }
  assert (HS' : ASECc cs L st_r X' m').
  { eapply (hs_frame _ (HL (qr_unbatch R) cs) L st st_r X X' m m'); [exact HS | exact MUH | exact WMALL | exact SU | exact SSM]. }
  assert (HD' : AD L m').
  { eapply (hd_frame _ (HL R cs) L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    pose proof (ao_nodes L ALO) as (_ & ON1 & ON3 & ONs & _). pose proof (ao_store L ALO) as (_ & OS1 & OS3 & OSs & _). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5; unfold c, K_BATCH_CLASS in *; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 ON1 ON3 ONs DNR DTN; unfold c, K_BATCH_CLASS in *; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 OS1 OS3 OSs DSR DTS; unfold c, K_BATCH_CLASS in *; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP (AHr (qr_unbatch R) cs) L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - destruct (CLS' c' Hc' NE) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }
  (* [comment removed for export] *)
  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    destruct AM as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & RC & RPA & RSC & RPSH).
    unfold arng. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
    split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9|].
    split; [| split; [rewrite EF8; exact RPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact RSC| exact RPSH]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA.
      destruct (RC c HC) as (Q1 & Q2 & Q3 & Q4). fold RB FA mu mfa in Q1, Q2, Q3, Q4.
      split; [exact Q1|]. split; [exact Q2|]. split.
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact Q3 | exact RF].
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q4|].
        assert (M8c : mfa mod 8 = 0 /\ mfa' mod 8 = 0) by (clear -A7 NEWMOD; Z.div_mod_to_equations; lia). destruct M8c as [M8c M8d].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact Q4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (RC c' Hc'). }
  (* [comment removed for export] *)
  exists X', mfa'.
  split; [exact MU2|]. split; [exact WMALL|]. split; [clear -NEWB NEWM; lia|]. split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|].
  split; [exact EF7|]. split; [exact EF8|]. split; [exact EF9|]. split; [exact EF10|]. split; [exact GO|].
  split; [intros b Hb; subst X'; exact (xrec_sub st X BBatch c k nb b1 ctx l1 l2 drained XB b Hb)|].
  intros b p Hb Sb. subst X'. exact (xrec_live st X BBatch c k nb b1 ctx l1 l2 drained XB ltac:(intros p'; discriminate) b p Hb Sb).
Qed.

(* [comment removed for export] *)
Lemma pendb_busy : forall L st X R m kb,
  AQdr R 0 0 L st X m -> qr_pendb R = [kb] ->
  exists nb b1 ctx l1 l2, x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2.
Proof.
  intros L st X R m kb (_ & _ & _ & _ & _ & _ & CP & _) EB.
  destruct (qcoupled_rec_bslot_busy L st X R kb CP ltac:(unfold qr_bslots; rewrite EB; apply in_app_iff; right; left; reflexivity)) as (b & Hb & Sb & Cb & Kb).
  destruct (in_split _ _ Hb) as (l1 & l2 & E). destruct b as [bc bk bn bs bb1 bctx]. cbn in Sb, Cb, Kb. subst bs bc bk.
  exists bn, bb1, bctx, l1, l2. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem acdealloc24 :
  forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (cs : list achunk)
         (kb lo : Z),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 K_BATCH_CLASS -> a3 = Z_to_bv 64 (abatch_addr L kb) ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall stX X' RNG' ms', acd24_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R cs lo m stX X' RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros RT k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X R cs
         kb lo ALO ARNG AR EB EP MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 RSTK KONT.
  set (c := K_BATCH_CLASS) in *.
  pose proof AR as AR0. destruct AR0 as (WF & RT0 & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr ARecyc1P.AHr] in HQ, HS, HD.
  destruct (pendb_busy L st X R m kb HQ EB) as (nb & b1 & ctx & l1 & l2 & XB). fold c in XB.
  destruct (any_range L st X BBatch c kb nb b1 ctx l1 l2 XB WF) as [HC KR].
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT0 as RT1.
  destruct RT1 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [sta STA].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH. cbv zeta in LCH.
  pose proof (cache_vals_lt L st X c tail WF HC LCH) as CH31.
  destruct (nf_bound L st X c WF HC) as [NFA NFN].
  pose proof (slot_geo L st X c kb ALO WF HC KR) as (S1 & S2 & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  (* [comment removed for export] *)
  eapply (cdealloc_spec RNG k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c (abatch_addr L kb) lo
            sj (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail) sta);
  try lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact RJ56
       | |- junk_at _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact CH31
       | |- length (map _ _ ++ _) = _ => rewrite length_app, length_map; exact LCH
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall j, _ -> 0 <= _ <= _ => intros j Hj; destruct (PERC j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB2 & _); exact CB2
       end.
  all: lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- aregion _ _ <= abatch_addr _ _ => exact G1
       | |- abatch_addr _ _ < aregion _ _ + _ => unfold ndist in KR; unfold K_REGION, K_FREEARR_OFF in *; change (2^32) with 4294967296; unfold abatch_addr; fold c; clear -G1 G2 G3 G4 S1; lia
       | |- al_ctx _ + 4096 <= _ => clear -CL2; atop_facts; lia
       | |- ?g => first [assumption | idtac "REMAINS" g]
       end.
  (* [comment removed for export] *)
  intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' CDR.
  destruct (cd24_store L RNG RNG' sp m m' st stX X R cs kb nb b1 ctx lo l1 l2 tail ALO ARNG AR EB EP XB CEIL LO CH LCH CDR)
    as (X' & mfa' & MU & WM & MFB & AR' & ARNG' & CIN & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & GC & XS & XL).
  destruct CDR as (FPLE & dr & mfa2 & sj2 & sta2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _).
  eapply KONT. unfold acd24_ret. split; [exact FPLE|]. do 16 eexists. exists mfa'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MFB|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|].
  split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact GC|].
  split; [exact XS| exact XL].
Qed.
End P.
End CANSEC1.
