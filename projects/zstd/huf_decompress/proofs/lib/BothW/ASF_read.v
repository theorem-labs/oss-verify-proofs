(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (9 recorded proofs replaced by written proofs (read_ek_appS, max_count_24S, cnt24_le16S and 6 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes AQConst ARep ARepQ ARepQP ARepFrame ARepKit ALayout AHeapP
     AModelFacts AFreeModel AFreeRep AFreeGeo F_afree_tail F_afree_icpt AFreeRead F_afreeC_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASF_read () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC46Stdlib5Lists4List7existsbC59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qcoupledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4qnumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4q_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6aintalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7aqcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9aq_tcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5q_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ@aquar_glob_constC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5BothW7AQConst9AQ_GCACHEC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List2InC59OSSVerify5KrLib5BothW9AFreeRead9last_app1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib5BothW9AFreeRead:enq_is_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead5ek_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7b_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8acompactC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ;abatch_addrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5BothW5ARepQ5qlastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail6ek_preC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC59OSSVerify5KrLib5BothW5ARepQ5qb_ksC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib5BothW5ARepQ9qentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qentriesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib5BothW5ARepQ9qprim_idsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_pendC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib5BothW5ARepQ6qfirstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8abatchesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=batches_bytesC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC47Corelib4Init5Logic9False_indC46Stdlib5Lists4List>rev_involutiveC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init3Nat3addK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Peano2ltK46Stdlib9micromega6VarMap1t01C46Stdlib5Lists4ListCapp_removelast_lastC46Stdlib5Lists4List:removelastK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW5ARepQ;abatches_toC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6qaddrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQP?abatches_to_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ<abatch_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQP:qlast_app1C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib5Lists4List9in_or_appC59OSSVerify5KrLib5BothW9AFreeRead;bslot_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7qb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead9bslot_geoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead:bslot_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQP@batches_bytes_InC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qhdrsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib5BothW<F_afree_icpt7ek_sepsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00C59OSSVerify5KrLib5BothW6ARepQP<qhdrs_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4lastC47Corelib5Lists7ListDef3mapK59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail8ek_deltaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail4ek_bC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List3revC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead;dummy_batchC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead8dummy_qbC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib4Spec8AsanCtrl7Q_BATCHC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib5BothW8ASF_read4CPS'C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ASF_read4WFS'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib5BothW6ARepQP@size_of_class_24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltc59OSSVerify5KrLib5BothW8ASF_read=max_count_24SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib5BothW9AFreeRead3K24C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4findC59OSSVerify5KrLib5BothW5ABase8ablk_linC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8AQUAR_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit=kit_cache_popC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:max_cachedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9find_noneC56Stdlib6ZArith6BinInt1Z8eqb_reflC47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib5BothW7ALayout=alayout_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeGeo8slot_geoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9alayout_tC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapC59OSSVerify5KrLib5BothW9ARepFrame>slots_disjointC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z3injC59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib5BothW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8K_REGIONC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ASF_read;cnt24_le16SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout4aobjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_ReflexiveC59OSSVerify5KrLib5BothW9AFreeRead4g_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQP@batches_bytes_lbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ASF_read=qfirst_casesSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ASF_read<qlast_casesSC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8in_splitC46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib5BothW9AFreeReadBbslots_nodup_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K59OSSVerify5KrLib5BothW<F_afree_tail3gqd01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail6dk_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_icpt7dk_sepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail5g_lstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail7dk_glstC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succI59OSSVerify5KrLib5BothW<F_afree_tail3gqd00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst6AQ_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AQ_MUTEXC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib5BothW>F_afreeC_iface7dk_preCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail7g_drainC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section VariantS.
Variables (H : aholes) (L : alayout) (st : astate) (X : aconc) (Q : qconc) (m : amem) (RNG : footprint) (hm n : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis ARNG : arng L RNG st.
Hypothesis AR : AREP H L st X m.
Hypothesis AQ : AQUAR_at L st X Q m.
Hypothesis N1 : 1 <= n.
Hypothesis NQM : n <= Q_MAX.
Hypothesis HM0 : ablk hm (hm + 24).      (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis HMSEP : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> hm + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= hm.

Lemma WFS' : awf L st X.
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_read ()) ["CANSEC1"; "VariantS"] "h01cp;4p;2p;3p;1p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p7210p9P0p1002Qp4p710p9p1003Ip4p710p1003fp4p710R0p8p1004Bp4p70R1p10059p4p710p8P1P0p8P1p1005Pp4p710p8g005lj4DTg006_j2CTg007Vj33Tg008Oj42Tg009Fj1BTg009dj29Tg00:@j24Tg00:\j21Tg00;7j45Tg00<4j56Tg00<nj57Tg00=dj58Tg00>`j5ATg00?Wj5:Tg00@Mj3;Tg00AEj1<Tg00B;j1=Tg00C3j4>Tg00D0j1?Tg00Dhj3@Tf2f1R1f0R0'1'1p=0p,2rcp,1LR2p,2stR3p,1XR4CDp,1mR5,C2A3235P2P3P4P5C2g00ECR6g00Ea#B/90g00FF,40'1R0P2P3P5P1C5P2P3P4P5P1D6P2P3P4P5P1D7P2P3P4P5P1D8'130[]0p,1HR7P2P3P4P5DAP7P2P3P4P5D:A;725%<5%=5P2P3P5P1C>\0^06%?53030303030p,2AR3@o"). Qed.
Lemma CPS' : qcoupled L st X Q.
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_read ()) ["CANSEC1"; "VariantS"] "p;4p;1p;2p;6p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p7210p9P0p1002Qp4p710p9p1003Ip4p710p1003fp4p710R0p8p1004Bp4p70R1p10059p4p710p8P1P0p8P1p1005Pp4p710p8g00GFj4?Tg00H?j1>Tg00I4j14Tg00Iij23Tg00:\j21Tg00J`j1;Tg00KZj1:Tg00LQj15Tg00MQj62Tg00NIj16Tg00OEj17Tg00P>j18Tg00Q4j19Tg00R3j1=Tg00S4j30Tg00Dhj3<Tp,1LR1p,2stR0p,1Xp,1QR2C?R3%>0R4%42p,1mR5'3R61134R4P1P5g00SO%;0%:2%50E2R31164R4P1P5%61%70%82%90E2R01134R4%=51104p,2AQ303030303<o"). Qed.
(* [comment removed for export] *)
Lemma read_ek_appS : forall stj chunks k24,
  enq_is_app st = true ->
  let ek := ek_of L st X Q n k24 stj chunks in
  forall (maxc csz : word) (cnt24 : Z),
  rw_cells bsegs m (al_t L + 2128) [C4 (Z_to_bv 64 (c_count (get_cls st K_BATCH_CLASS))); C4 (Z_to_bv 64 (max_count st K_BATCH_CLASS));
                                     C8 (Z_to_bv 64 (if a_cinit st then size_of_class K_BATCH_CLASS else 0))] ->
  rw_cells bsegs m (al_t L + 2784) [C8 stj] ->
     ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m
  /\ ek_seps ek L hm (qlast L (q_loc Q))
  /\ ek_delta ek n = n /\ ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
  /\ (exists l bl ql qz, a_qloc st = l ++ [bl] /\ q_loc Q = ql ++ [qz] /\ length ql = length l /\ b_count bl <> Q_BATCH
        /\ ek = EkAppend 0 (b_size bl) (b_count bl) (map (Z_to_bv 64) (qhdrs L (b_chunks bl) (qb_ks qz)))
                        (c_count (get_cls st K_BATCH_CLASS)) (Z_to_bv 64 (max_count st K_BATCH_CLASS))
                        (Z_to_bv 64 (if a_cinit st then size_of_class K_BATCH_CLASS else 0)) stj).
Proof.
  intros stj chunks k24 EA ek maxc csz cnt24 CR STS. subst ek. unfold ek_of. rewrite EA. cbv zeta.
  pose proof CPS' as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & _).
  destruct AQ as (GC & [QC ABL] & GL & IA & _ & NUM). destruct NUM as (NB1 & NB2 & NF & NC & NM).
  (* [comment removed for export] *)
  pose proof EA as EA0. unfold enq_is_app in EA0.
  destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [discriminate|].
  assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
  destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [|NFULL]; [discriminate|]. clear EA0.
  set (l := rev rl) in *. set (bl := blr) in *.
  assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; lia).
  destruct (q_loc Q) as [|q0 qs0] eqn:QQ0; [cbn in LQ; lia|]. rewrite <- QQ0 in *.
  assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]).
  { apply app_removelast_last. rewrite QQ0. discriminate. }
  set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
  assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; lia).
  rewrite QL, last_app1.
  (* [comment removed for export] *)
  unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
  cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
  assert (QLST : qlast L (q_loc Q) = abatch_addr L (qb_slot qz)) by (rewrite QQ; apply qlast_app1).
  (* [comment removed for export] *)
  assert (INz : In qz (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity).
  pose proof (bslot_range L st X Q WFS' CPS' qz INz) as KZ.
  pose proof (bslot_geo L st X ALO WFS' (qb_slot qz) KZ) as (B0 & B1 & BAL & BT & BN & BS & BR).
  destruct (bslot_busy L st X Q CPS' qz INz) as (yz & Hyz & Syz & Cyz & Kyz).
  pose proof (HMSEP (qb_slot qz) KZ) as DH.
  (* [comment removed for export] *)
  assert (INbl : In bl (a_qloc st ++ a_qglob st)) by (apply in_or_app; left; rewrite QL; apply in_or_app; right; left; reflexivity).
  pose proof (batches_bytes_In _ bl NF INbl) as [SZ1 _].
  assert (SZ2 : b_size bl <= a_qloc_bytes st).
  { rewrite NB1. apply Forall_app in NF. destruct NF as [NFl _]. exact (proj2 (batches_bytes_In _ bl NFl ltac:(rewrite QL; apply in_or_app; right; left; reflexivity))). }
  rewrite QLST. unfold fhm in *.
  split; [| split; [| split; [reflexivity| split; [reflexivity|]]]].
  - (* [comment removed for export] *)
    cbn [ek_pre]. unfold Q_BATCH, Q_BATCH_BYTES, Q_CACHE, Q_MAX in *.
    split; [rewrite ?QL, length_app; cbn; lia|]. split; [exact Z1|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact Z2|]. split; [rewrite length_map, qhdrs_length by exact Z5; rewrite Z4; lia|].
    split; [exact Z3|]. split; [exact B0|]. split; [exact B1|]. split; [exact BT|]. split; [generalize DH; clear; intros; lia|].
    split; [exact CR|]. split; [exact STS|]. apply BR. exact ARNG.
  - cbn [ek_seps]. split; [exact DH|]. split; [exact BN| exact BS].
  - exists l, bl, ql, qz. split; [first [exact QL| reflexivity]|]. split; [exact QQ|]. split; [exact LNl|]. split; [exact NFULL|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma max_count_24S : max_count st K_BATCH_CLASS <= 2.
Proof. unfold max_count, max_cached. rewrite size_of_class_24. change (1024 / 8192) with 0. destruct (a_cinit st); lia. Qed.

Lemma cnt24_le16S : c_count (get_cls st K_BATCH_CLASS) <= 16.
Proof.
  pose proof max_count_24S as MC. pose proof WFS' as WF0. destruct WF0 as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC K_BATCH_CLASS K24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia.
Qed.

Lemma read_ek_newS : forall stj,
  enq_is_app st = false -> 0 < c_count (get_cls st K_BATCH_CLASS) ->
  rw_cells bsegs m (al_t L + 2784) [C8 stj] ->
  exists k24 chunks, let ek := ek_of L st X Q n k24 stj chunks in
     ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m
  /\ ek_seps ek L hm (qlast L (q_loc Q))
  /\ ek_delta ek n = n + 8192 /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24
  /\ nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
  /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
  /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
  /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
  /\ a_cinit st = true
  /\ ((a_qloc st = [] /\ q_loc Q = [])
      \/ (exists l bl ql qz, a_qloc st = l ++ [bl] /\ q_loc Q = ql ++ [qz] /\ length ql = length l /\ b_count bl = Q_BATCH
            /\ qlast L (q_loc Q) = abatch_addr L (qb_slot qz) /\ 0 <= qb_slot qz < ndist st K_BATCH_CLASS /\ qb_slot qz <> k24))
  /\ ek = EkNew (match a_qloc st with [] => false | _ => true end) 0 (b_size (List.last (a_qloc st) dummy_batch))
               (c_count (get_cls st K_BATCH_CLASS)) (Z_to_bv 64 (max_count st K_BATCH_CLASS))
               (Z_to_bv 64 (if a_cinit st then size_of_class K_BATCH_CLASS else 0)) stj
               (Z_to_bv 64 (acompact K_BATCH_CLASS k24)) chunks (al_space_beg L) (abatch_addr L k24)
               (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb)))).
Proof.
  intros stj EA POS STS.
  pose proof (ablk_lin _ _ HM0) as (HML1 & HML2 & HML3 & HML4). unfold AIMG_HI in HML1.   (* [comment removed for export] *)
  pose proof CPS' as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BS & _).
  pose proof AQ as AQ0. destruct AQ0 as (GC & [QC ABL] & GL & IA & _ & NUM). destruct NUM as (NB1 & NB2 & NF & NC & NM).
  destruct (kit_cache_pop H L st X m K_BATCH_CLASS (c_count (get_cls st K_BATCH_CLASS)) AR K24 eq_refl POS)
    as (k24 & chunks & NK & NB & KK & CR & CH & LCH & NTH & JK & FSH).
  rewrite size_of_class_24 in JK, FSH.
  assert (CIN : a_cinit st = true).
  { pose proof max_count_24S as MC. pose proof WFS' as WF0. destruct WF0 as (_ & _ & _ & _ & _ & PERC & _).
    destruct (PERC K_BATCH_CLASS K24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _).
    unfold max_count in CNTB |- *. destruct (a_cinit st); [reflexivity| exfalso; lia]. }
  exists k24, chunks. cbv zeta. unfold ek_of. rewrite EA. cbv zeta.
  (* [comment removed for export] *)
  assert (NIB : ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))).
  { intros Hin. apply (BS k24) in Hin. destruct Hin as (y & Hy & Sy & Cy & Ky).
    enough (E : busy_of X K_BATCH_CLASS k24 <> None) by (apply E; exact NB).
    intros E. unfold busy_of in E. destruct (List.find _ _) eqn:FE; [discriminate|].
    apply (List.find_none _ _ FE) in Hy. rewrite Cy, Ky, !Z.eqb_refl in Hy. discriminate. }
  (* [comment removed for export] *)
  pose proof (bslot_geo L st X ALO WFS' k24 KK) as (B0 & B1 & BAL & BT & BN & BSR & BR).
  pose proof (HMSEP k24 KK) as DHB.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  destruct AR as (_ & _ & INST & _). destruct INST as (I32 & _).
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CH by (unfold acache_addr, K_BATCH_CLASS; lia).
  replace (al_t L + 2128 + 16) with (al_t L + 2128 + 16) in CH by lia.
  assert (IXS : bv_unsigned (Z_to_bv 64 (acompact K_BATCH_CLASS k24)) = k24 * 512 /\ k24 * 512 < 2^32).
  { unfold acompact. rewrite size_of_class_24. change (8192 / 16) with 512.
    assert (KB : k24 < 2^19).
    { pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WFS' K24 KK) as (_ & _ & _ & SG1 & SG2 & SG3 & SG4 & _).
      rewrite size_of_class_24 in SG2. unfold aslot_addr, K_FREEARR_OFF in *. rewrite size_of_class_24 in SG2. generalize SG1 SG2 SG3 SG4 KK. clear. intros. nia. }
    rewrite unsigned_lit by lia. lia. }
  destruct IXS as [IX1 IX2].
  assert (HBq : abatch_addr L k24 = al_space_beg L + 24 * 2 ^ 32 + 16 * bv_unsigned (Z_to_bv 64 (acompact K_BATCH_CLASS k24))).
  { rewrite IX1. unfold abatch_addr, aslot_addr, aregion. rewrite size_of_class_24. unfold K_REGION, K_BATCH_CLASS. lia. }
  (* [comment removed for export] *)
  pose proof EA as EA0. unfold enq_is_app in EA0.
  destruct (a_qloc st) as [|b0 bs0] eqn:QL0.
  - (* [comment removed for export] *)
    assert (QQ0 : q_loc Q = []) by (destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]).
    rewrite QQ0. cbn [qlast last qaddrs map List.last b_chunks qb_ks qhdrs dummy_batch dummy_qb b_size length Z.of_nat].
    unfold fhm in *.
    split; [| split; [| split; [reflexivity| split; [reflexivity|]]]].
    + cbn [ek_pre]. atop_facts. rewrite CIN.
      split; [split; reflexivity|]. split; [exact I32|]. split; [rewrite ?CIN in CR; exact CR|]. split; [exact CH|]. split; [exact LCH|].
      split; [split; [exact POS| exact cnt24_le16S]|]. split; [exact NTH|]. split; [lia|]. split; [exact STS|].
      split; [exact HBq|]. split; [exact JK|]. split; [lia|]. split; [exact B0|]. split; [exact B1|].
      split; [exact BT|]. split; [generalize (proj1 (alayout_t L ALO)); clear; intros; lia|]. split; [lia|].
      split; [generalize DHB; clear; intros; lia|]. split; [lia|]. apply BR. exact ARNG.
    + cbn [ek_seps]. split; [exact DHB|]. split; [exact BN|]. split; [exact BSR|]. intros; discriminate.
    + split; [exact NK|]. split; [exact NB|]. split; [exact KK|]. split; [rewrite QQ0 in NIB; exact NIB|]. split; [exact JK|]. split; [exact FSH|].
      split; [exact CIN|]. split; [left; split; [reflexivity| first [exact QQ0| reflexivity]]|]. rewrite CIN. reflexivity.
  - (* [comment removed for export] *)
    rewrite <- QL0 in *.
    destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [exfalso; rewrite <- (rev_involutive (a_qloc st)), RV in QL0; discriminate|].
    assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
    destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [FULL|]; [| discriminate]. clear EA0.
    set (l := rev rl) in *. set (bl := blr) in *.
    assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; lia).
    assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]).
    { apply app_removelast_last. destruct (q_loc Q); [cbn in LQ; lia| discriminate]. }
    set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
    assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; lia).
    unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
    cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
    assert (QLST : qlast L (q_loc Q) = abatch_addr L (qb_slot qz)) by (rewrite QQ; apply qlast_app1).
    assert (INz : In qz (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity).
    pose proof (bslot_range L st X Q WFS' CPS' qz INz) as KZ.
    pose proof (bslot_geo L st X ALO WFS' (qb_slot qz) KZ) as (Z0' & Z1' & ZAL & ZT & ZN & ZS & ZR).
    destruct (bslot_busy L st X Q CPS' qz INz) as (yz & Hyz & Syz & Cyz & Kyz).
    pose proof (HMSEP (qb_slot qz) KZ) as DHL.
    assert (NEz : qb_slot qz <> k24) by (intros E; apply NIB; rewrite <- E; apply in_map; exact INz).
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot qz) k24 ltac:(lia) ltac:(lia) NEz ltac:(rewrite size_of_class_24; lia)) as DBL.
    rewrite size_of_class_24 in DBL.
    assert (INbl : In bl (a_qloc st ++ a_qglob st)) by (apply in_or_app; left; rewrite QL; apply in_or_app; right; left; reflexivity).
    pose proof (batches_bytes_In _ bl NF INbl) as [SZ1 _].
    assert (SZ2 : b_size bl <= a_qloc_bytes st).
    { rewrite NB1. apply Forall_app in NF. destruct NF as [NFl _]. exact (proj2 (batches_bytes_In _ bl NFl ltac:(rewrite QL; apply in_or_app; right; left; reflexivity))). }
    assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1).
    rewrite QLST, !LST. fold qz. unfold fhm in *.
    split; [| split; [| split; [reflexivity| split; [reflexivity|]]]].
    + cbn [ek_pre]. unfold Q_CACHE, Q_BATCH, Q_BATCH_BYTES in *. rewrite CIN.
      split.
      { split; [rewrite QL, length_app; cbn; lia|]. split; [rewrite <- FULL; exact Z1|]. split; [lia|]. split; [lia|]. split; [exact Z0'|]. split; [exact Z1'|].
        split; [exact Z2|]. split; [rewrite length_map, qhdrs_length by exact Z5; apply Nat2Z.inj; rewrite <- Z4, FULL; reflexivity|]. apply ZR. exact ARNG. }
      split; [exact I32|]. split; [rewrite ?CIN in CR; exact CR|]. split; [exact CH|]. split; [exact LCH|].
      split; [split; [exact POS| exact cnt24_le16S]|]. split; [exact NTH|]. split; [lia|]. split; [exact STS|].
      split; [exact HBq|]. split; [exact JK|]. split; [lia|]. split; [exact B0|]. split; [exact B1|].
      split; [exact BT|]. split; [clear -ZT; lia|]. split; [generalize DBL; clear; unfold abatch_addr; intros; lia|].
      split; [generalize DHB; clear; intros; lia|]. split; [generalize DHL; clear; intros; lia|]. apply BR. exact ARNG.
    + cbn [ek_seps]. split; [exact DHB|]. split; [exact BN|]. split; [exact BSR|]. intros _. split; [exact DHL|]. split; [exact ZN| exact ZS].
    + split; [exact NK|]. split; [exact NB|]. split; [exact KK|]. split; [exact NIB|]. split; [exact JK|]. split; [exact FSH|]. split; [exact CIN|].
      split; [right; exists l, bl, ql, qz; repeat (split; [first [assumption| reflexivity]|]); exact NEz|].
      rewrite CIN. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma read_lastS : enq_is_app st = false ->
  let lst := qlast L (q_loc Q) in
  let bl := List.last (a_qloc st) dummy_batch in
  let hs := map (Z_to_bv 64) (qhdrs L (b_chunks bl) (qb_ks (List.last (q_loc Q) dummy_qb))) in
     (if match a_qloc st with [] => false | _ :: _ => true end
      then 0 < Z.of_nat (length (a_qloc st))
           /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (b_size bl)); C8 (Z_to_bv 64 1021)]
           /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           /\ 0 <= b_size bl < 2^64
      else Z.of_nat (length (a_qloc st)) = 0 /\ lst = 0)
  /\ (al_t L + 4096 <= lst \/ lst + 8192 <= al_t L \/ lst = 0) /\ (hm + 24 <= lst \/ lst + 8192 <= hm)   (* [comment removed for export] *)
  /\ (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L)
  /\ 0 <= lst < 2^64.
Proof.
  intros EA. cbv zeta.
  pose proof CPS' as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BS & _).
  pose proof AQ as AQ0. destruct AQ0 as (GC & [QC ABL] & GL & IA & _ & NUM). destruct NUM as (NB1 & NB2 & NF & NC & NM).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. unfold aobj in ON, OS.
  pose proof EA as EA0. unfold enq_is_app in EA0.
  destruct (a_qloc st) as [|b0 bs0] eqn:QL0.
  - assert (QQ0 : q_loc Q = []) by (destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]).
    rewrite QQ0. cbn [qlast last qaddrs map length Z.of_nat]. unfold fhm in *.
    split; [split; reflexivity|]. generalize TL1 HM0 ON OS. clear. intros HA HB HC HD. pose proof (ablk_lin _ _ HB) as (HB1 & HB2 & HB3 & HB4). unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in *. lia.   (* [comment removed for export] *)
  - rewrite <- QL0 in *.
    destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [exfalso; rewrite <- (rev_involutive (a_qloc st)), RV in QL0; discriminate|].
    assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
    destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [FULL|]; [| discriminate]. clear EA0.
    set (l := rev rl) in *. set (bl := blr) in *.
    assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; lia).
    assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]).
    { apply app_removelast_last. destruct (q_loc Q); [cbn in LQ; lia| discriminate]. }
    set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
    assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; lia).
    unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
    cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
    assert (QLST : qlast L (q_loc Q) = abatch_addr L (qb_slot qz)) by (rewrite QQ; apply qlast_app1).
    assert (INz : In qz (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity).
    pose proof (bslot_range L st X Q WFS' CPS' qz INz) as KZ.
    pose proof (bslot_geo L st X ALO WFS' (qb_slot qz) KZ) as (Z0' & Z1' & ZAL & ZT & ZN & ZS & ZR).
    destruct (bslot_busy L st X Q CPS' qz INz) as (yz & Hyz & Syz & Cyz & Kyz).
    pose proof (HMSEP (qb_slot qz) KZ) as DHL.
    assert (INbl : In bl (a_qloc st ++ a_qglob st)) by (apply in_or_app; left; rewrite QL; apply in_or_app; right; left; reflexivity).
    pose proof (batches_bytes_In _ bl NF INbl) as [SZ1 _].
    assert (SZ2 : b_size bl <= a_qloc_bytes st).
    { rewrite NB1. apply Forall_app in NF. destruct NF as [NFl _]. exact (proj2 (batches_bytes_In _ bl NFl ltac:(rewrite QL; apply in_or_app; right; left; reflexivity))). }
    assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1).
    rewrite QLST, !LST. fold qz. unfold fhm, Q_CACHE, Q_BATCH, Q_BATCH_BYTES in *.
    split.
    + split; [rewrite QL, length_app; cbn; lia|]. split; [rewrite <- FULL; exact Z1|]. split; [exact Z0'|]. split; [exact Z1'|].
      split; [exact Z2|]. split; [rewrite length_map, qhdrs_length by exact Z5; apply Nat2Z.inj; rewrite <- Z4, FULL; reflexivity|].
      split; [apply ZR; exact ARNG| lia].
    + split; [clear -ZT; lia|]. split; [generalize DHL; clear; intros; lia|]. split; [exact ZN|]. split; [exact ZS| lia].
Qed.

(* [comment removed for export] *)
Lemma qfirst_casesS : forall qs, qfirst L qs = 0 \/ exists q, In q qs /\ qfirst L qs = abatch_addr L (qb_slot q).
Proof. intros [|q qs]; [left; reflexivity| right; exists q; split; [left; reflexivity| reflexivity]]. Qed.
Lemma qlast_casesS : forall qs, qlast L qs = 0 \/ exists q, In q qs /\ qlast L qs = abatch_addr L (qb_slot q).
Proof.
  intros qs. destruct qs as [|q0 qs0] eqn:E; [left; reflexivity| right]. rewrite <- E.
  assert (NE : qs <> []) by (subst; discriminate).
  exists (List.last qs dummy_qb). pose proof (app_removelast_last dummy_qb NE) as D. split.
  - rewrite D at 2. apply in_or_app. right. left. reflexivity.
  - rewrite D at 1. apply qlast_app1.
Qed.

Lemma read_dkS : forall (eb delta : Z) (ek : enq_kind),
  0 <= delta ->
  (eb = qlast L (q_loc Q) \/ exists kk, eb = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))) ->
  (Q_CACHE < a_qloc_bytes st + delta -> a_qglob_bytes st + (a_qloc_bytes st + delta) <= Q_MAX) ->
  ek_b ek (qlast L (q_loc Q)) = eb ->
  let g := g_of L st Q delta in
     dk_pre ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes st + delta) m
  /\ dk_seps g L hm
  /\ g_lst g = qlast L (q_glob Q) /\ dk_glst g (qlast L (q_loc Q)) = (if Q_CACHE <? a_qloc_bytes st + delta then qlast L (q_glob Q) else qlast L (q_loc Q)).
Proof.
  intros eb delta ek D0 EB NOREC EKB g. subst g. unfold g_of. cbv beta iota zeta delta [dk_pre dk_seps g_drain g_full g_nb g_fst g_lst g_qb g_nx dk_glst].
  pose proof CPS' as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BS & _).
  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GC ABG] & IA & _ & NUM). destruct NUM as (NB1 & NB2 & NF & NC & NM).
  apply Forall_app in NF. destruct NF as [NFl NFg].
  pose proof (batches_bytes_lb _ NFg) as GLB0. rewrite <- NB2 in GLB0.
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. pose proof (bslot_geo L st X ALO WFS' (qb_slot q) (bslot_range L st X Q WFS' CPS' q Hq)) as (B0 & B1 & _). atop_facts. lia. }
  assert (GF64 : 0 <= qfirst L (q_glob Q) < 2^64).
  { destruct (qfirst_casesS (q_glob Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; right; exact Hq]. }
  assert (GL64 : 0 <= qlast L (q_glob Q) < 2^64).
  { destruct (qlast_casesS (q_glob Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; right; exact Hq]. }
  (* [comment removed for export] *)
  assert (GFULL : a_qglob st <> [] ->
      0 < Z.of_nat (length (a_qglob st))
   /\ rw_cells bsegs m (qlast L (q_glob Q)) [C8 (Z_to_bv 64 0)]
   /\ 0x10007fff8000 <= qlast L (q_glob Q) /\ qlast L (q_glob Q) + 8192 <= ATOP
   /\ (al_t L + 4096 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_t L)
   /\ (hm + 24 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= hm)
   /\ (qlast L (q_loc Q) + 8192 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= qlast L (q_loc Q))
   /\ (eb + 8192 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= eb)
   /\ (al_nodes L + 1048576 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_nodes L)
   /\ (al_store L + 8388608 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_store L)
   /\ rng RNG (qlast L (q_glob Q)) 8192).
  { intros GNE.
    assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
    assert (LQ : (0 < length (q_glob Q))%nat) by (rewrite LN2; destruct (a_qglob st); [congruence| cbn; lia]).
    assert (QQ : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]).
    { apply app_removelast_last. destruct (q_glob Q); [cbn in LQ; lia| discriminate]. }
    set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
    set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
    assert (LNg : length qg = length lg) by (rewrite QQ, QG, !length_app in LN2; cbn in LN2; lia).
    unfold abatches in ABG. rewrite QG, QQ in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [_ ABz].
    cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & _) _].
    assert (QLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQ; apply qlast_app1). rewrite QLST.
    assert (INz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQ; apply in_or_app; right; left; reflexivity).
    pose proof (bslot_range L st X Q WFS' CPS' qgz INz) as KZ.
    pose proof (bslot_geo L st X ALO WFS' (qb_slot qgz) KZ) as (B0 & B1 & BAL & BT & BN & BSR & BR).
    destruct (bslot_busy L st X Q CPS' qgz INz) as (yz & Hyz & Syz & Cyz & Kyz).
    pose proof (HMSEP (qb_slot qgz) KZ) as DH.
    (* [comment removed for export] *)
    assert (DL : qlast L (q_loc Q) + 8192 <= abatch_addr L (qb_slot qgz) \/ abatch_addr L (qb_slot qgz) + 8192 <= qlast L (q_loc Q)).
    { destruct (qlast_casesS (q_loc Q)) as [E0 |(q & Hq & Eq)]; [rewrite E0; left; lia| rewrite Eq].
      assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
      pose proof (bslot_range L st X Q WFS' CPS' q INq) as KQ.
      assert (NEq : qb_slot q <> qb_slot qgz).
      { apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl).
        apply (bslots_nodup_split L st X Q CPS' qs1 q (qs2 ++ qg) qgz []). rewrite EQl, QQ. rewrite <- ?app_assoc. cbn [app]. rewrite <- ?app_assoc. reflexivity. }
      pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q) (qb_slot qgz) ltac:(lia) ltac:(lia) NEq ltac:(rewrite size_of_class_24; lia)) as DD.
      rewrite size_of_class_24 in DD. unfold abatch_addr. exact DD. }
    assert (DE : eb + 8192 <= abatch_addr L (qb_slot qgz) \/ abatch_addr L (qb_slot qgz) + 8192 <= eb).
    { destruct EB as [-> |(kk & -> & KK & NIK)]; [exact DL|].
      assert (NEq : kk <> qb_slot qgz) by (intros ->; apply NIK; apply in_map; exact INz).
      pose proof (slots_disjoint L K_BATCH_CLASS kk (qb_slot qgz) ltac:(lia) ltac:(lia) NEq ltac:(rewrite size_of_class_24; lia)) as DD.
      rewrite size_of_class_24 in DD. unfold abatch_addr. exact DD. }
    split; [rewrite QG, length_app; cbn; lia|].
    split; [pose proof Z1 as Z1'; rw_split Z1' 1%nat ZN ZR; exact ZN|].
    split; [exact B0|]. split; [exact B1|]. split; [exact BT|]. split; [exact DH|]. split; [exact DL|]. split; [exact DE|].
    split; [exact BN|]. split; [exact BSR|]. apply BR. exact ARNG. }
  (* [comment removed for export] *)
  unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES in *.
  split; [| split; [| split; [reflexivity| reflexivity]]].
  - split; [exact MX|]. split; [exact GC|].
    split; [lia|]. split; [lia|]. split; [exact GF64|]. split; [exact GL64|].
    destruct (Z.ltb_spec 1048576 (a_qloc_bytes st + delta)) as [LT|GE]; [| lia].
    split; [exact LT|]. split; [lia|].
    destruct (a_qglob st) as [|bg lg0] eqn:QG0.
    + split; [reflexivity|]. assert (QQ0 : q_glob Q = []) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). rewrite QQ0. reflexivity.
    + rewrite <- QG0 in *. destruct (GFULL ltac:(rewrite QG0; discriminate)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
      rewrite EKB. unfold fhm in *.
      split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|]. split; [generalize F6; clear; intros; lia|].
      split; [exact F7|]. split; [exact F8|]. exact F11.
  - intros DR FU. destruct (a_qglob st) as [|bg lg0] eqn:QG0; [discriminate|]. rewrite <- QG0 in *.
    destruct (GFULL ltac:(rewrite QG0; discriminate)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    unfold fhm in *. split; [generalize F6; clear; intros; lia|]. split; [exact F9| exact F10].
Qed.

(* [comment removed for export] *)
Lemma read_dkSC : forall (eb delta : Z) (ek : enq_kind),
  0 <= delta -> delta <= Q_MAX + 8192 ->
  (eb = qlast L (q_loc Q) \/ exists kk, eb = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))) ->
  Q_CACHE < a_qloc_bytes st + delta -> Q_MAX < a_qglob_bytes st + (a_qloc_bytes st + delta) ->
  ek_b ek (qlast L (q_loc Q)) = eb ->
  let g := g_of L st Q delta in
     dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes st + delta) m
  /\ dk_seps g L hm
  /\ g_lst g = qlast L (q_glob Q) /\ dk_glst g (qlast L (q_loc Q)) = qlast L (q_glob Q) /\ g_drain g = true.
Proof.
  intros eb delta ek D0 DMAX EB REC1 REC2 EKB g. subst g. unfold g_of. cbv beta iota zeta delta [dk_preC dk_seps g_drain g_full g_nb g_fst g_lst g_qb g_nx dk_glst].
  pose proof CPS' as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BS & _).
  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GC ABG] & IA & _ & NUM). destruct NUM as (NB1 & NB2 & NF & NC & NM).
  apply Forall_app in NF. destruct NF as [NFl NFg].
  pose proof (batches_bytes_lb _ NFg) as GLB0. rewrite <- NB2 in GLB0.
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. pose proof (bslot_geo L st X ALO WFS' (qb_slot q) (bslot_range L st X Q WFS' CPS' q Hq)) as (B0 & B1 & _). atop_facts. lia. }
  assert (GF64 : 0 <= qfirst L (q_glob Q) < 2^64).
  { destruct (qfirst_casesS (q_glob Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; right; exact Hq]. }
  assert (GL64 : 0 <= qlast L (q_glob Q) < 2^64).
  { destruct (qlast_casesS (q_glob Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; right; exact Hq]. }
  (* [comment removed for export] *)
  assert (GFULL : a_qglob st <> [] ->
      0 < Z.of_nat (length (a_qglob st))
   /\ rw_cells bsegs m (qlast L (q_glob Q)) [C8 (Z_to_bv 64 0)]
   /\ 0x10007fff8000 <= qlast L (q_glob Q) /\ qlast L (q_glob Q) + 8192 <= ATOP
   /\ (al_t L + 4096 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_t L)
   /\ (hm + 24 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= hm)
   /\ (qlast L (q_loc Q) + 8192 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= qlast L (q_loc Q))
   /\ (eb + 8192 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= eb)
   /\ (al_nodes L + 1048576 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_nodes L)
   /\ (al_store L + 8388608 <= qlast L (q_glob Q) \/ qlast L (q_glob Q) + 8192 <= al_store L)
   /\ rng RNG (qlast L (q_glob Q)) 8192).
  { intros GNE.
    assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
    assert (LQ : (0 < length (q_glob Q))%nat) by (rewrite LN2; destruct (a_qglob st); [congruence| cbn; lia]).
    assert (QQ : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]).
    { apply app_removelast_last. destruct (q_glob Q); [cbn in LQ; lia| discriminate]. }
    set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
    set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
    assert (LNg : length qg = length lg) by (rewrite QQ, QG, !length_app in LN2; cbn in LN2; lia).
    unfold abatches in ABG. rewrite QG, QQ in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [_ ABz].
    cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & _) _].
    assert (QLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQ; apply qlast_app1). rewrite QLST.
    assert (INz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQ; apply in_or_app; right; left; reflexivity).
    pose proof (bslot_range L st X Q WFS' CPS' qgz INz) as KZ.
    pose proof (bslot_geo L st X ALO WFS' (qb_slot qgz) KZ) as (B0 & B1 & BAL & BT & BN & BSR & BR).
    destruct (bslot_busy L st X Q CPS' qgz INz) as (yz & Hyz & Syz & Cyz & Kyz).
    pose proof (HMSEP (qb_slot qgz) KZ) as DH.
    (* [comment removed for export] *)
    assert (DL : qlast L (q_loc Q) + 8192 <= abatch_addr L (qb_slot qgz) \/ abatch_addr L (qb_slot qgz) + 8192 <= qlast L (q_loc Q)).
    { destruct (qlast_casesS (q_loc Q)) as [E0 |(q & Hq & Eq)]; [rewrite E0; left; lia| rewrite Eq].
      assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
      pose proof (bslot_range L st X Q WFS' CPS' q INq) as KQ.
      assert (NEq : qb_slot q <> qb_slot qgz).
      { apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl).
        apply (bslots_nodup_split L st X Q CPS' qs1 q (qs2 ++ qg) qgz []). rewrite EQl, QQ. rewrite <- ?app_assoc. cbn [app]. rewrite <- ?app_assoc. reflexivity. }
      pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q) (qb_slot qgz) ltac:(lia) ltac:(lia) NEq ltac:(rewrite size_of_class_24; lia)) as DD.
      rewrite size_of_class_24 in DD. unfold abatch_addr. exact DD. }
    assert (DE : eb + 8192 <= abatch_addr L (qb_slot qgz) \/ abatch_addr L (qb_slot qgz) + 8192 <= eb).
    { destruct EB as [-> |(kk & -> & KK & NIK)]; [exact DL|].
      assert (NEq : kk <> qb_slot qgz) by (intros ->; apply NIK; apply in_map; exact INz).
      pose proof (slots_disjoint L K_BATCH_CLASS kk (qb_slot qgz) ltac:(lia) ltac:(lia) NEq ltac:(rewrite size_of_class_24; lia)) as DD.
      rewrite size_of_class_24 in DD. unfold abatch_addr. exact DD. }
    split; [rewrite QG, length_app; cbn; lia|].
    split; [pose proof Z1 as Z1'; rw_split Z1' 1%nat ZN ZR; exact ZN|].
    split; [exact B0|]. split; [exact B1|]. split; [exact BT|]. split; [exact DH|]. split; [exact DL|]. split; [exact DE|].
    split; [exact BN|]. split; [exact BSR|]. apply BR. exact ARNG. }
  (* [comment removed for export] *)
  pose proof NC as NC'. pose proof NM as NM'.
  unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES in *.
  assert (GDT : (1048576 <? a_qloc_bytes st + delta) = true) by (apply Z.ltb_lt; exact REC1).
  rewrite GDT.
  split; [| split; [| split; [reflexivity| split; reflexivity]]].
  - split; [reflexivity|]. split; [exact MX|]. split; [exact GC|].
    split; [lia|]. split; [lia|]. split; [exact GF64|]. split; [exact GL64|].
    split; [exact REC1|]. split; [exact REC2|]. split; [lia|].
    destruct (a_qglob st) as [|bg lg0] eqn:QG0.
    + split; [reflexivity|]. assert (QQ0 : q_glob Q = []) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). rewrite QQ0. reflexivity.
    + rewrite <- QG0 in *. destruct (GFULL ltac:(rewrite QG0; discriminate)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
      rewrite EKB. unfold fhm in *.
      split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|]. split; [generalize F6; clear; intros; lia|].
      split; [exact F7|]. split; [exact F8|]. exact F11.
  - intros _ FU. destruct (a_qglob st) as [|bg lg0] eqn:QG0; [discriminate|]. rewrite <- QG0 in *.
    destruct (GFULL ltac:(rewrite QG0; discriminate)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    unfold fhm in *. split; [generalize F6; clear; intros; lia|]. split; [exact F9| exact F10].
Qed.
End VariantS.
End CANSEC1.
