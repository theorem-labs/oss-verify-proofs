(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (K_img, K_hi, K_shad and 11 more); K_shad restated for the revision's model). *)



From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes ASecFacts AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepKit ARepFrame
     AKit AModelFacts F_aalloc2 F_aalloc F_amalloc_icpt F_amalloc_arep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARepStore () := "C46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC35stdpp4base6LookupC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC46Stdlib5Lists4List8map_consC35stdpp4gmap;gmap_finmapC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List7existsbI46Stdlib5Lists4List5NoDup00I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4base4fmapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5BothW7ALayout4aobjC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2geC59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula01K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepStore6kfactsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op204K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4findC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbI47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5BothW9ARepStore4bnewC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:removelastK59OSSVerify5KrLib5BothW4ARep6xclass01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep5aconc01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepStore5xfastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List2InC35stdpp4base6lookupC46Stdlib5Lists4List9app_assocC47Corelib7Classes?RelationClasses8symmetryC35stdpp4base6insertC59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>st_fast_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame7st_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib5BothW9ARepFrame@cache_split_lastC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib5BothW9ARepFrameAlength_removelastC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z9is_nonnegK59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z8eqb_reflK46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib5BothW9ARepStore@xfast_busy_slotsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ARepStore9xfast_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame=st_fast_ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameAst_fast_max_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;st_fast_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC47Corelib7Classes?RelationClasses=neq_SymmetricC56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01C47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2or02C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat3N2Z6inj_ltC45stdpp7numbers1N6eq_decC56Stdlib6ZArith4Znat3N2Z8inj_succI59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~C35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib5BothW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6hb_idsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7sec_wf1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7ab_kindC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;in_flat_mapK46Stdlib5Lists4List5NoDup02K59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8SEC_UOFFC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6abkind00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_aalloc2:hdr_b1_midC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8F_aalloc@hdr_b1_mid_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC56Stdlib6ZArith6BinInt1Z9log2_landC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC59OSSVerify5KrLib5BothW8F_aalloc?lt_pow2_of_log2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z7lor_0_rC46Stdlib5Lists4List7forallbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List>forallb_forallI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4RSECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame@st_fast_countersC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapPIsec_chunks_of_insert_primC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_symC59OSSVerify5KrLib5BothW6AHeapP9RSEC_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.





Notation Wn sp t c AB UB PGE n nodes store :=
  ([(sp - 4096, sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + n); (AB, AB + 16); (shad UB, PGE);
    (ADEPOT_LO, ADEPOT_HI); (nodes, nodes + 1048576); (store, store + 8388608)]%Z) (only parsing).

Section CANSEC1. Context {rc : runConstT}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->      
  exists k, 0 <= k <= 1 /\ 6352896 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepStore ()) ["CANSEC1"] "h01Hh14__p1h24__x1h34__x2h44__x3h51kh62H1h77__arithh84__ffh98__varmaph:5__with;2H0h<2hih=2lop;3p;1p;2p;4p;6p;7p;8p-1R0p10000p4p710R1p8P0p1000Gp4p710p8P0p1000hR2p4p710p8P0P2p4p7210p8P0p1001ER0p4p7210p8p1001Yp4p710R2p10026p4p710R3p8P2p1002Rp4p710R2p8p10030p4p710R4p1003NR5p4p710R6p8P4P5p4p7210R5p8p1003gp4p70R7g004^R8p4p710p8P7P1p8P7p10058p4p710p8P7P3p8P7p1005dp4p710p8P7p1006Bp4p7210p8P7P2p8P7p1006_R1p4p710p8P7p10076R9p4p710p8P7p1007RR:p4p710p8P7p1007op4p710p8P7p1008HR;p4p710p8P7P;p4p7210p8P7P0p4p710R;p8P7p1008ep4p710p8P7p1009Ap4p710p8p1009]R7p4p73101R<p100:7R=p4p73110p8P<p100:PR>p4p73110p8P<p100:lp4p710p8P<p100;?R?p4p7201p8P<p100;Qp4p7201p8P<P0p4p73110p8P<p100;cR0p4p73110p8P<p100<7R@p4p73110p8P<p100<Qp4p7201p8P7p4p710R<P=p4p710p8P<P>p4p710p8P<P6p8P<P5p8P<P;p8P<P0p4p710p8P<P@p4p710p8p100<dR@p4p710R<P4p8P<P6p8P<P5p8P<p100=8p4p73110p8P@p4p741110R@P9p4p73101p8p100=Jp4p7210P2p8P:p4p7210P3p8p100>6p4p7<111111111110R:P3p8P:P2p8p100>Xp4p7<111111111110R:P3p8P:P2p8p100?:p4p741110R2P7p4p7511100R:p8P:P2p8p100?Sp4p741110R2P7p4p76111100R:p8P:P2p8p100?kp4p741110R2P7p4p771111100R:p8P:P2p8P1p4p741110R1P7p4p7:1111111100R7p8P7P1p8P?p4p7200R?P@p8P@P?p8g00@Kj3bTg00A@j1aTg00B>j15Tg00Bcj11Tg00CHj1:Tg00Cfj1OTg00D\j20Tg00E8R?j2<Tg00ESj2=Tg00F0j2DTg00FMj2ITg00Fgj1CTg00GFj2BTg00Goj3HTg00HXj2VTg00IDj1UTg00Idj3TTg00JDj1STg00Jdj2ETg00KBj4RTg00K`j1QTg00L>j1PTg00Lij2ATg00MLj6NTg00N0j1MTg00NRj2GTg00O5j3@Tg00OXj3FTg00P;j2LTP8j2`Tg00P]j2_Tg00QIj3^Tg00Qcj3[Tg00RBj4ZTg00S4j4JTg00SNj4YTg00T9j7\Tg00T]j7WTg00UAj8]Tf0R8#5#5#5#5p=7%58#5p=X%18#1p=?%18#1#1#1p=9%18#1#1#1#1#1#1#1p=3f2R@f1R1'0/<8p=21<18,<@p=>g00UeR7/G8p=8P@g00VCR2g00VbR:P:g00WBR3P7P1g00WbP8CYg00XIF\p=4P@P2P:P:P3P1P8FWp=6f3R9P2P:P:P3P@P1P8G]p=;1018,<@p=Kp,2rcR<?b18%a<g00XiR5#5R6#5#7#7#7R4#1#5#XR0#5#7#1#?#9#3#3#:R;%O<R<'0R>%54#7#7#1#?#9#3#3#:R4,0<R='<g00YN%55#1#9#7#9#3#:RA/09RB%90#3#:R0,0@RC'<%15RD#9#3RE#7#7#7#7#1#?#9#3#:RF10@<729g00YhRG%:5RH,08728RIf5RJ,0ARK1=F8RLf4RM%1E#?#3#3#3#3#3#3#:RE,=8,D0RN10M<RO3272J3>X57,I7P1109092AMP?PK10M0f7RK,0ARPf6RQ10Q<72N92LK5>IX57,I7RQP810K0P7f:RR,0Af9RS10S<72N92LR5>IX57RIPGp-0RLg00ZFRNg00[2RT#C#CRU#C,B71B7U1B7T5H75H7g00[Q'V%UN3TRT%SNRNP71E7@P11E79CRRU%Q7RV%P7RW%8;1A76R654WPWP2P:P:P3PJENR256W%M:R:PW1A7DRD%80RX54WP:PW%8A1A75R554WRYP:1G7GRZ=4WZ%8HR[94WZR\56W%8FR]=@7Z=4W5%8ER^9@7Z9F7X94WDA4WD6RZ56W56W96WY56WC;C;C;1LW3R3P8P@g00\=R_g00\]R`'`1_8@=^_`dA[7G1CZR`b8b9b:X27X37X47W1A2;@910A@10GHRA92GG1=FG1=GE,D010MJRG52M7297>B[\C[^27^37^47^1LP8P=P<PSPRPKP1P@O7b7CJW6X0PP1P8O2n2001000010121000000W0P8O1109<92FMP?10FJPOPQP810FK10K<P7PIPHPTPNPUPVPW%8494W696W2P:PWPZP:PWA4W]5P:A4W[[96W\A@7][=4W5A@7[^9F7X94WD=6WZ56W96WY56WC;C;C;P3P`b8b9b:X27X37X47X1LAK9@410@910F@AKAHH1=FH1=HE,D0=2MG7297>B[[[^27^37^47^1LP8P>P<PSPRPKP1P@O7b7CJW6W0P1P8O2n2001000010121000000W0P8O1n200100001021100011000b;W0X<7X=7o"). Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6352896 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepStore ()) ["CANSEC1"] "h04__x1h14__x2h21Hh31kh47__arithh54__ffh68__varmaph75__with84__x3h94__p1h:2H0h;2H1h<3H10h=2H2h>2H3h?2H4h@2H5hA2H6hB2H7hC2H8hD2H9hE2HnhF6__sat6hG1ahH1np;3p;1p;2p;4p;7p;6p;8p-1R0p10000p4p710R1p8P0p1000Gp4p710p8P0p1000hR2p4p710p8P0P2p4p7210p8P0p1001ER0p4p7210p8p1001Yp4p710R2p10026p4p710R3p8P2p1002Rp4p710R2p8p10030p4p710R4p1003NR5p4p710R6p8P4P5p4p7210R5p8p1003gp4p70R7g00QIR8p4p710p8P7P1p8P7p10058p4p710p8P7P3p8P7p1005dp4p710p8P7p1006Bp4p7210p8P7P2p8P7p1006_R1p4p710p8P7p10076R9p4p710p8P7p1007RR:p4p710p8P7p1007op4p710p8P7p1008HR;p4p710p8P7P;p4p7210p8P7P0p4p710R;p8P7p1008ep4p710p8P7p1009Ap4p710p8p1009]R7p4p73101R<p100:7R=p4p73110p8P<p100:PR>p4p73110p8P<p100:lp4p710p8P<p100;?R?p4p7201p8P<p100;Qp4p7201p8P<P0p4p73110p8P<p100;cR0p4p73110p8P<p100<7R@p4p73110p8P<p100<Qp4p7201p8P7p4p710R<P=p4p710p8P<P>p4p710p8P<P6p8P<P5p8P<P;p8P<P0p4p710p8P<P@p4p710p8p100<dR@p4p710R<P4p8P<P6p8P<P5p8P<p100=8p4p73110p8P@p4p741110R@P9p4p73101p8p100=Jp4p7210P2p8P:p4p7210P3p8p100>6p4p7<111111111110R:P3p8P:P2p8p100>Xp4p7<111111111110R:P3p8P:P2p8p100?:p4p741110R2P7p4p7511100R:p8P:P2p8p100?Sp4p741110R2P7p4p76111100R:p8P:P2p8p100?kp4p741110R2P7p4p771111100R:p8P:P2p8P1p4p741110R1P7p4p7:1111111100R7p8P7P1p8P?p4p7200R?P@p8P@P?p8g00]=j3yTg00Bcj12Tg00CHj1;Tg00D\j20Tg00A@j1oTg00B>j17Tg00Cfj1^Tg00^4j2BTg00F0j21Tg00ESj2?Tg00E8R?j28Tg00^Tj2dTg00_Ej2cTg00_fj1aTg00`?j2STP8j3LTg00`\j2`Tg00aCj2KTg00a_j2_Tg00bFj2]Tg00blj2\Tg00cRj2[Tg00Fgj1JTg00GFj2GTg00Goj3NTg00HXj2ZTg00IDj1xTg00Idj3YTg00JDj1wTg00dNj1vTg00Jdj2XTg00KBj4HTg00K`j1uTg00L>j1tTg00Lij2PTg00N0j1rTg00OXj3MTg00dlj7qTg00P;j2pTg004^j2nTg00P]j2mTg00Qcj3lTg00RBj4kTg00NRj2UTg00O5j3OTg00S4j4VTg00MLj6iTg00ePj4TTg00YNR8j2WTg00FMj2hTg00SNj4gTg00T9j7fTg00T]j7sTg00UAj8eTf0R@#2#2p=D%2@#2#2#2#2#2#2#2p=5%7@#7#7#7p=9%7@#7p=b%2@#2#2#2p=@f2R1f1R7/0@'8p=Eg00UeR2g00YhR:7L@p=Qf3R3/01107@'Wp=3187@,81p=R1017/8@,83p=:10:@p=C1117/0@p=F107@,81,83p=I1h2@p=A1017/8@p=61U2@p==P1g00VCR9g00VbR<P<g00WBR5P2P7g00WbP@Cgg00XIFfp=4P1P9P<P<P5P7P@Fsp=>P3P9P<P<P5P1P7P@Gep=<1W7@,81p=jp,2rcR6?y7@g00XiR4#2R0#2R;#D#5R>#2R=#2#DRA#;RB/07RC%o6%74RD#7#9#9#9RE#2#7#bRF#7#9#2#D#@#5#5#;%^6R6'0RG%7E#9#9#2#D#@#5#5#;RE7E6P?f4RH%;>R>'B#Q10>HRI11H3RJP6PJ%@F#5#;RF%9=#9#9#9#2#D#@#5#;R=PHC3PJPB%74#2#@#9#@#5#;RJPHC37RIC:f5RI11IH%C@%;4RK7E@RLf6RM%5A#5#5#5#5#5#;RA,?@,1FRN7FI1?=@ROPMCIX32#A76656JP11BM>#Qf7RP,0>RQ11PMRRP6PRPFP=PPC3PRPBPJPPC37RQC:P?f8RQ,0>RR11QPRPPPPFP=PQC3PPPBPJPQC37RR766f9RR11RQPLf:RP?FRNPOPPCIX32#A76656JP@10>Pf;RR/1PRPPPPFP=PRC3P>PRPPPBPJPRC3C:766P?f<RP/1RRR/06PRPFP=PPC3P>PPPRPBPJPPC3C:f=RR11RPPLf>RS/1RRRPN10OSC:X32#A76656JP@10R6f?RR/1SRSPFP=PRC3P>PRPSPBPJPRC3C:P?f@R?/1RRRPFP=P?C3PRPBPJP?C396>?fARR11R?PLfBR?/1RRSPN10O?C:X32#A76656JP@PSPFP=P?C3fCRS11S?PBPJPSC356>fDR?,0J11?SRT/06RUPLfERV/1?RWPN10OVC:X32#ARX'81d?>%C?%C>fFRY/B>RZ#C[[1cV>%Q>R[#a1SY>,?>/1Z9L2Y[1`Y>1K:>fGRZ/B>R\#C1K\>'8[1_Z>1K>:fHR\/B>R],K>?E]:[1]\>fIR\/S>#Q\[1\\>fJR]/B>=L2]\[g00ek1[]>R]eP]g00ZFR]g00[2R[#JR^#JR_#JR`#J,G21G2^R^1G2_5N25N2g00[QR_'Z%x]Ra3Y%w]RbP2%v2RcP71X21RdCH%u2Re%t2Rf%=BRg1P2DRD54f%r<RhPf%=>1P24R454fRiPfP9P<P<P5AM24D=4fg%=J=4f4RgFq5>fPhPfPiPhPgC<C<C<1pf5RgP@P1g00\=Rjg00\]Rk'n1m@1=LjkdAl2:7CkRkb5b6b7X02X1210>7Rj1171Rl/0B10J73j10>110J3[[\C^02^12P@fKRCfLP\PQPRO5b410JCeb<bDbCbBbAb2bFPUPXPaPbP2PdP71X23RXCHPePf1P209M24R0=4fDRDPhPDC<PgPkb5b6b7X02X12X8211@7RD/0110l3[^02^12^82P@P6P?PVPMO4b4P810TF10=?PLAFYVNPOPYCIX32#AP710WFP2PLAFZYNPOPZCIX32ROP:PaPbP2PdP7PcCHPePf%=FRd94f0PhPfPiPh1U2:Ri=4fi%=KRN94fiRL5>f%=ARW9O2i9M2d94f0%==R?=O2i=4f45>f5>fC<C<PgPkb5b6b7X02X1210DF%CKRD96::1113Ri1?:A,1F1?=:/01C:\j[^02^12P@PYPZP7PPO4b4CVW2P@O110=VP2POPKp-0RO1G2`1G2[9N2^5N2/Z_=Y]aPbP2P2PXP1PcCHP7PcCHPePfPfP9P<P<P5PIEi1P2;R;%=E54f5>fPhPfA4f?4PhPfA4f0;PhA4fNN9>fLAO2NW9M2d94f0AO2?N=4f45>f5>fC<C<C<PgPkb5b6b7X02X12X82W9AE31E10=710iHAEDKK1?KA,1F9F3H1?=KP3CI[[[^02^12^82^9OP@PGP6PYPZPSP7PQO7b4CVW2P@O1n200100001021100011000CTCTW@W?P7P@O2n2001000010121000000W2W>P7P@O2n2001000010121000000W2W=P7P@O2n2011000010121000000W2W;P7P@O2n2011000010121000000b:WEW2XH2XG2o"). Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6352896 * j <= a).
Proof.
ltac2:(KReplay.run1 (kr_t_ARepStore ()) ["CANSEC1"] "h04__x1h11jh21Hh31kh47__arithh54__ffh68__varmaph75__with84__x2h94__p1h:2H5h;2H0h<2H1h=2H2h>2H3h?2H4h@2_HhA1ap;1p;3p;2p;4p;6p;7p;8p-1R0p10000p4p710R1p8P0p1000Gp4p710p8P0p1000hR2p4p710p8P0P2p4p7210p8P0p1001ER0p4p7210p8p1001Yp4p710R2p10026p4p710R3p8P2p1002Rp4p710R2p8p10030p4p710R4p1003NR5p4p710R6p8P4P5p4p7210R5p8p1003gp4p70R7g00QIR8p4p710p8P7P1p8P7p10058p4p710p8P7P3p8P7p1005dp4p710p8P7p1006Bp4p7210p8P7P2p8P7p1006_R1p4p710p8P7p10076R9p4p710p8P7p1007RR:p4p710p8P7p1007op4p710p8P7p1008HR;p4p710p8P7P;p4p7210p8P7P0p4p710R;p8P7p1008ep4p710p8P7p1009Ap4p710p8p1009]R7p4p73101R<p100:7R=p4p73110p8P<p100:PR>p4p73110p8P<p100:lp4p710p8P<p100;?R?p4p7201p8P<p100;Qp4p7201p8P<P0p4p73110p8P<p100;cR0p4p73110p8P<p100<7R@p4p73110p8P<p100<Qp4p7201p8P7p4p710R<P=p4p710p8P<P>p4p710p8P<P6p8P<P5p8P<P;p8P<P0p4p710p8P<P@p4p710p8p100<dR@p4p710R<P4p8P<P6p8P<P5p8P<p100=8p4p73110p8P@p4p741110R@P9p4p73101p8p100=Jp4p7210P2p8P:p4p7210P3p8p100>6p4p7<111111111110R:P3p8P:P2p8p100>Xp4p7<111111111110R:P3p8P:P2p8p100?:p4p741110R2P7p4p7511100R:p8P:P2p8p100?Sp4p741110R2P7p4p76111100R:p8P:P2p8p100?kp4p741110R2P7p4p771111100R:p8P:P2p8P1p4p741110R1P7p4p7:1111111100R7p8P7P1p8P?p4p7200R?P@p8P@P?p8g00Bcj12Tg00CHj1>Tg00]=j3mTg00A@j1lTg00B>j1:Tg00Cfj1\Tg00D\j20Tg00^4j2TTP8j3ITg00F0j21Tg00ESj2?Tg00E8R8j26Tg00IDj1aTg00JDj1_Tg00Jdj2OTg00K`j1^Tg00L>j1]Tg00Lij2JTg00N0j1[Tg00P;j2ZTg004^j2YTg00P]j2XTg00Qcj3WTg00RBj4VTg00dNj1UTg00KBj4STg00OXj3ETg00NRj2RTg00S4j4GTg00Fgj1NTg00GFj2KTg00Goj3QTg00HXj2kTg00Idj3jTg00MLj6iTg00ePj4MTg00YNR?j2gTg00FMj2fTg00SNj4eTg00T9j7dTg00UAj8cTg00T]j7hTg00O5j3bTf0R@#2#2p=F%2@#2#2#2#2#2#2#2p=8%:@#:#:#:p=<%:@#:p=`%2@#2#2#2p=Bf2R1f1R7/0@'6p=Hf3R2/01107@'gp=4167@,61p=L1017/6@,62p=D1017/6@p=7f4R:1021107@'6'6p=5g00UeR3/f@p=91R3@p=@P1g00VCR9g00VbR<P<g00WBR5P3P7g00WbP@Ceg00XIFdp=3P2P9P<P<P5P1P7P@Gcp=;1117/0@p=CP1P9P<P<P5P7P@Fhp==Ab37@p=A107@,61,62p=Pp,2rcR6g00XiR4#2R0#2#F#8R;#>R>7m@%l6%:4R=#:#<#<#<RA#2#:#`RB#:#<#2#F#B#8#8#>%\6R6'0RC%:A#<#<#2#F#B#8#8#>RA7H6P81T1>g00YhRD5I310>1RE111>RFP6PF%BB#8#>RB%2;R;#<#<#<#<#2#F#B#8#>RGP1C4PF%2;#FR;#>RH%:4#2#B#<#B#8#>RIP1C47LECD112>RE%>4RJ,0@97D@RK11:>RL%8;#8#8#8#8#8#>R;,?@RM,1BRN1?G@ROP:D5X33#9PKPL11HMRM1?I@RLP:D5X13#9'677697>2P71T:>=I3Df5RP,0>RQ11P>RRP6PRPBPGPPC4PRPHPIPPC47LQCDP8f6RQ,0>RP11Q>RRPRPBPGPQC4PRPHPIPQC47LP776f7RP11P>PKf8RP/1>RRPNPOPPD5X33#9PKPRPMPLPPD5X13#9'677657>P@10>Pf9RR/1>RSPSPBPGPRC4P>PRPSPHPIPRC4CD776P8f:RR/1>RS/06PSPBPGPRC4P>PRPSPHPIPRC4CDf;RS11S>PKf<RS/1>RTPNPOPSD5X33#9PKPTPMPLPSD5X13#9'677657>P@10T6f=RT/1>RUPBPGPTC4P>PTPUPHPIPTC4CDP8f>RT/1>RUPBPGPTC4PUPHPIPTC497>Tf?RT11T>PKf@RT/1>RUPNPOPTD5X33#9PKPUPMPLPTD5X13#9'677657>P@PUPBPGPTC4fARU11U>PHPIPUC457>fBRU,0>RV11U>RW/06RXPKfCRY/1>RZPNPOPYD5X33#9R[PKPZPMPLPYD5X13#9R\'6R]'6g00ZFR^#aR_%_^R`1O37Ra%^3Rb%]3Rc%@>Rd1J34R453cRe%[<RfPeC;1Zc5RgP@P1g00\=Rhg00\]Ri'Y1X@1=IhidAW3D7CVRib5b6b7X0310>@10>7Rh[^03P@PYPRO2b4PXP]P_P`P31O31R]P7%U3RXCSPbPcAE34dRd1J3053cR0PfP0C;PgPib5b6b7X03X8311@>R0/07AC7>1[^03^83P@P6PYPQO3b4P[P\P?10WB10GUPKfDR\/1>R[PNPOP\D5X33#9P710ZBP3PKfERZ/1>RQPNPOPZD5X33ROPDP_P`PaPbPc%@BRN93cdPfPcPePf1R3DRR=3cR%@JRj93cRRk5=cRl%@;Rm,ARRn9E3N93cd%@GRo/AR=3c45=c5=cC;C;PgPib5b6b7X03100B10DJRp97DDRqPF1?D;Rr,1B1?GDP1D5\h[^03P@PZP7PSO3b4CGW2P@O110GYP3POPJp-0ROg00[2Rs#NRt#N#N,K31K3t1K3s5Q35Q3g00[Q'k=j^_R^P`P3PXP7P]CSR]PbPcPcP9P<P<P5P:Ei1J3=R=%@A53c5=cR:PfPcA3co4PfPcA3cd=R=PfA3cjj9=ckRk1AjmRm9E3N93cd1Aoj=3c45=c5=cC;C;C;PgPib5b6b7X03X83W9AH17ARA10G710F2RoAHpJJRpPE1?J;R;,1B1?GJP2D5[[[^03^83^9OP@PCP6PZPYP7PPO6b4CGW2P@O1n200100001021100011000P8PVPWPHPIPUC4PKP[PMPLP\D5X13#9P@10>\PQPHPIPZC4P?fFR??C>H10I?PKfHR??C>MPLP?CPX13#9P@fGR??C>HP3PKfIRK?C>MPLPKCPX13RLPDP_P`PaPbPc%@HRa93cdPfPcPePfAE3an93cd%@IRn/AR=3c45=c9=clC;C;PgPib5b6b7X03100HPqPF11Hr1?IDP1D5\h[^03P@PKP7PTO3b4CGW:P@O110I?P3PLPJP^P`P]PbPcP:PfPcA3cn4PfPcP=PfAE3am93cd1Anj=3c45=c9=ckC;C;C;PgPib5b6b7X03X83X9O10I7PpPE11H;1?IJP2D5\o[\A^03^83^9OP@PCP6PKP?P7PSO6b4CGW:P@O1n200100000021100011000W2W@P7P@O2n2001000000121000000CMCMCMW:W?P7P@O2n2001000010121000000W2W>P7P@O2n2011000010121000000W2W=P7P@O2n2011000010121000000W2W<P7P@O2n2011000010121000000b;W2XA3o"). Qed.
Section Kinds.
Variables (sp t c AB S UB PGE n nodes store res ctx lo grz ssz : Z).

Definition kfacts : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      
  /\ (1 <= c <= 16)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ UB - 16 >= AB /\ 1 <= n /\ UB + n <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ shad UB + 1 <= PGE /\ PGE <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6352896 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6352896 <= store /\ store + 8388608 <= ATOP)
  /\ (sclr ctx 65536 /\ 6352896 <= ctx /\ ctx + 65536 <= ATOP).
Hypothesis KF : kfacts.

Ltac kind := pose proof KF as KF'; unfold kfacts, AIMG_HI in *; unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in KF';
  destruct KF' as (F_lo & F_t & F_c & F_res & F_slot & F_sh & F_ns & F_ctx);
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma K_img : forall A k, 0x10000 <= A -> 0 <= k -> (A + k <= ADEPOT_LO \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI)) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma K_low : forall A k, 2147450880 <= A -> A + k <= 2148244992 -> 0 <= k ->      
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma K_hi : forall A k, sp <= A -> 0 <= k ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma K_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ PGE <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma K_ctx : 
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma K_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k ->
  (A + k <= t + 208 + c * 80 \/ t + 208 + c * 80 + 4 <= A) -> (A + k <= t + 2784 \/ t + 2792 <= A) -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma K_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k ->
  (A + k <= AB \/ (AB + 16 <= A /\ A + k <= UB - 16) \/ UB + n <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

Lemma K_obj : forall A k, ((6352896 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepStore ()) ["CANSEC1"; "Kinds"] "h04__x1h14__x2h24__x3h32H6h44__p1h57__arithh64__ffh78__varmaph85__with94__p2h:4__x4h;4__x5h<4__p3h=4__p4h>4__x6h?4__x7h@4__p5hA4__p6hB5__x10hC4__x8hD4__x9hE4__p7hF5__x11hG1AhH3F_chI5F_ctxhJ4F_lohK4F_nshL5F_reshM4F_shhN6F_slothO3F_thP3KF'hQ1kp%0p%1p&0p;1p;2p;3p;4p;5p;7p;6p;8p-1R0p10000p4p710R1p8P0p1000Gp4p710p8P0p1000hR2p4p710p8P0P2p4p7210p8P0p1001ER0p4p7210p8p1001Yp4p710R2p10026p4p710R3p8P2p1002Rp4p710R2p8p10030p4p710R4p1003NR5p4p710R6p8P4P5p4p7210R5p8p1003gp4p70R7g00QIR8p4p710p8P7P1p8P7p10058p4p710p8P7P3p8P7p1005dp4p710p8P7p1006Bp4p7210p8P7P2p8P7p1006_R1p4p710p8P7p10076R9p4p710p8P7p1007RR:p4p710p8P7p1007op4p710p8P7p1008HR;p4p710p8P7P;p4p7210p8P7P0p4p710R;p8P7p1008ep4p710p8P7p1009Ap4p710p8p1009]R7p4p73101R<p100:7R=p4p73110p8P<p100:PR>p4p73110p8P<p100:lp4p710p8P<p100;?R?p4p7201p8P<p100;Qp4p7201p8P<P0p4p73110p8P<p100;cR0p4p73110p8P<p100<7R@p4p73110p8P<p100<Qp4p7201p8P7p4p710R<P=p4p710p8P<P>p4p710p8P<P6p8P<P5p8P<P;p8P<P0p4p710p8P<P@p4p710p8p100<dR@p4p710R<P4p8P<P6p8P<P5p8P<p100=8p4p73110p8P@p4p741110R@P9p4p73101p8p100=Jp4p7210P2p8P:p4p7210P3p8p100>6p4p7<111111111110R:P3p8P:P2p8p100>Xp4p7<111111111110R:P3p8P:P2p8p100?:p4p741110R2P7p4p7511100R:p8P:P2p8p100?Sp4p741110R2P7p4p76111100R:p8P:P2p8p100?kp4p741110R2P7p4p771111100R:p8P:P2p8P1p4p741110R1P7p4p7:1111111100R7p8P7P1p8P?p4p7200R?P@p8P@P?p8g00B>j16Tg00Bcj13Tg00Cfk10FTg00D\j21Tg00F0j22Tg00CHj1UTg00fGj2ZTg00E8R?j24Tg00fdj2kTg00g@j1zTP8j3jTg00h8k20;Tg00ESj2xTg00IDj1wTg00hXj3PTg00A@k103Tg00Fgj1?Tg00GFj2rTg00JDk100Tg00dNj1~Tg00K`k10ETg00L>k10DTg00iTj3qTg00N0k10CTg00Lij2}Tg00P;k20BTg004^k20ATg00P]k20@Tg00Qck30?Tg00RBk40>Tg00j7k20=Tg00j`j3lTg00NRj2{Tg00O5k30<Tg00YNj2VTg00SNj4OTg00kIk108Tg00kgk207Tg00lHk306Tg00m1k505Tg00mUj4vTg00Idj3]Tg00Goj3[Tg00HXj2yTg00Jdk204Tg00KBj4gTg00T9j7aTg00OXj3tTg00MLk602Tg00dlj7_Tg00UAj8bTg00T]j7hTg00ePj4sTf0R8#3#3#3#3p=Y%38#6p=X%68#6p=R%68#3p=N%38#3#3#3#3#3#3#3p=T%38#3#3#Up=>%68#6#6#6p=Gf2R@f1R1'2/18p=K11@1/48p=7%38#3p=i1118,V@p=Mf3R7/1@1118'Vp=;%68#3#3#3p=o1418,4@p=E1V@1/48p=Ff6R2g00UeR:P:f5R3f4R9CvP:P:P@P1Cv=]783]p=c1r:8p==A[:189[:@9[:7g00[QR<'yp=Jg00ZFR5?]18p>01204:8p=IP:P@P1P8Cgp=WP:P:P9P7P@CgP1P8Cgp=D1}:8p=@P@g00VCR6g00VbR4P4g00WBR0P:P1g00WbR;P8COg00XIR>Fap=51{:8p=9At:18p=8P1P6P4P4P0P8J02p=AP3P6P4P4P0P9P7P@P6P4P4P0P1P8F_Gbp=pP3P6P4P4P0P9P6P4P4P0P7P@FhP1P8Gbp=C11@1/V8p=nA[:18p=:A[:18/y<p=<A]5189]5@9]579]59p=0P:P9P7P:P@P1P8CgCgp=|P2P6P4P4P0P3P6P4P4P0P:P9P;P7COP>FaP@P6P4P4P0P:P1P;P8COP>FaF_p=SP:P1P;P8COp=QP7P6P4P4P0P@P6P4P4P0P1P>FaP8Fhp=HP9P6P4P4P0P7P@P6P4P4P0P1P8FhFhp=fP7P6P4P4P0P@P1P6P4P4P0P8P>FaF_p=`P@P6P4P4P0P1P8Fhp=\P3P6P4P4P0P9P6P4P4P0P7P@F_P1P8Gbp=^P2P6P4P4P0P3P9P7P6P4P4P0P@P1P8GbGbp=L119712@1/18'Vp=BA[:189[:@p=mP:At:@1P;P8COp=eP9P6P4P4P0P7P6P4P4P0P:P@P;P1COP>FaP8F_p>0:P@P6P4P4P0P1P8F_p>09P7P6P4P4P0P@P1P8Gbp=uP2P3P9P7P@P1P8CsCsp=dg00XiR>#6#Y#X#R#N#T#>R;%6>R<#6S00#6S01#6#R#G#GR=#X#RRA#3#T#>RB9K18771%3>RC#3RD#3S02#3S03#3#YRE#3#iRF#3RG#G#G#G#G#Y#T#>RH;M1p,2rcRI$0FRJ9K@1g00YhRK/1@1297p,1tRL%UFRF,2LRMP9C;1239p,3resRN%3G#iRG#YRO#o#N#T#>RP,2NRQP3C;1223p,5nodesRR%UORS,2RRTP2C;f7RU/22p,5storeRV%>ORO,2VRWPUC;p,2KFg00nmP?p,2loRXp,2spRY/ZFRZ,1X57JS0411MB11HL11FLR[PM%UGRGP;PLC;'411MJ7E[S053FS06%U>R[p,1cRMQ03#UR\,1M37S0711QJS0897HNS0912NFp,2ABR]p,1SS0:,2]R^p,2UBR_/Z\R`/k]p,1nS0;,1[S0<Q0;,2_Ra/1^3E77Q37S0=%6E#i#X#R#G#G#N#R#N#T#>S0>%z]S0?%z_S0@Q0?p,3grzS0A'25j:%UCS0BQ0A'1Q0@p,3PGES0C7K[S0DQ0CQ0?p,3sszS0E'2RE'111EH3E3E37S0F11TB11HR11;RS0G11TJS0H11WB11HV11WJS0I97;VS0J3F3E3FS0Kp,3ctxRE/2GRG/1B11HE11GJ97;E3FS0L'4S0M'4S0N'4S0O'4S0P'4S0Q'4S0R20;::REPZPYPE%3<RG#N#>RQ,2L%6CS0S#3S0T#>R^,xM'2Rb%UDS0U,2bRcPEQ0T#6#RRd#3Re#3#>Rf,2LRg%6e#>S0V,2LRePE%Nd#>Rd,2LRh%3GS0W#X#o#X#US0X,2LRGPEP`PaPEP]12]\RiPEQ0@Q0CPE%6>#i#X#N#Y#R#N#X#>S0Y%3>#R#N#R#o#X#Y#N#>S0ZPEPRPTPEPVPW%wEFcFcFcFcFcREf:Rjf9Rk3PP8Q04Q0RP?Q06Q0Qf>Rlf=Rm5PEP8Q06Q0QP?Q07Q0PfBS0[fARn5PEP8Q07Q0PP?Q09Q0OfFfE5PEP8Q09Q0OP?Q0=Q0NfJfIS0\5PEP8Q0=Q0NP?Q0FQ0MfNfM5PEP8Q0FQ0MP?Q0KQ0LfRS0]fQS0^5PEP8Q0KQ0LfUR?fTS0_'2RoPZPYP?C;PoPbPcP?C;RcPoPgPeP?C;S0`PoPhPGP?C;S0aPoP`PaP?C;S0bPoP]PiP?C;S0cPoQ0@Q0CP?C;S0dPoQ0YQ0ZP?C;S0ePoPRPTP?C;S0fPoPVPWP?C;S0gg00ohS0h'4S0i'4S0j'4S0k'4S0l'4S0m'4S0n'4S0o'4RW'4&03IRI%6A#G#Y#T#T#>%6=#G#G#Y#T#T#>,1J77JR=p-0RAg00[2Ro#?RT#?Ri#?Ra#=R`%=iS0p%=TRT1r:oS0qCJ%w5Ro+01&005R5%I9P@%~:RiP1%I3RG?W7iDD&0E:Rh&0D:RePe%@DRgQ0S#@Rb55e%@<R<%9FRZ5q:Rp95eb&0C4RbPe1}:>Rq%@CS0r'8RC=5egPbPeA5eCp1AeUEpEC20Be0RpP8P@g00\=Rrg00\]Rs+0A20@8@=jrsdB0?:K1H0>Rsb6b7b8X0:X1:X2:X::X;:W41Z@F,199779121@S0s/1912@71Z9F;nU[[^0:^1:^2:^::^;:^4AP8fWRr,1YPXPJPYfVRYPrfKQ0_O8b5b3PcPWPIP=20=:^RW%?aRa#?Rc#?RJ#?RX#?Rt#?Ru#=Rv5l:Rw%=cRcQ0q':S0t'<Rx%=tRt9l:W%=aRaQ0q':'<Ry1:aTS0u,<wRw%?uRu#=S0v9l:W1:cTS0w'<RWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPx%?uS0x#?Ru#=Rz%=JRJQ0p,:`R{':S0y'<R|P|PWPWP|P|PxPxP|P|PWPWP|P|PxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxPyPwPWPWPwPyPxPxP|P|PW%?uRu#?S0z#?#=S0{%=uRu%=XRX1:JaCJR}P|P|P}P}P|P|P}PWP|P|PxPxPyPwPWPWPwPyPxPoD0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0P5AWG9iP@%I2PUPiPUPiDDP1PiP7%IUS0|?WUiPUPiD|DDPhPePePePe%6DS0}#3#@RD%9SS0~'8S10%9BRxPe%9HRyPDFSS11PePe%9;Rw/QDPe1AekPePePeQ0}#6#@RW%9OS12'8S13PxPePyPWFSS14PePe1QwW1AejCHDfCHPbPePeQ02#@S1595eyS16f;R|,AePbPePe%9[S17=5eg%9\R}95egPbPePePePe18<ZS18PxPePyP<FSf<R~,AeS19PbPePePePCPWPeQ13PqFSS13PbPePePePCPDPeQ10PqFSS10PbPePeA5eC<S1:PeQ18/QqC`S18PbPe1{:KQ0r55eS0rPbPePeA5ewqS1;A5eCxRw5\eA5eyqS1<PbPePePC%9Q,8<%9^:0<:g'8RDPeQ0U#9,8DPqFSE^FLFLECECECECPpPsb6b7b8X0:X1:X2:X::X;:X>:X?:X4AX9AX<AX=AAK3SB11H3RD122O11H2S1=7nBf8RW97;25EU97;33F14Dj113\97[3123FS1>/1B?FDm1293S1?Pj12jOS1@P9C;1232S1APjPjPSP3DB122US1BPWPWPFP2DB11KWS1CAKWkBS1D97;W11HWS1E'V12kjS1F12|Q1x~^'2R^P^Q0UPkDB[[[[[[[[[^0:^1:^2:^::^;:^>:^?:^4A^9A^<A^=AP8Q05Q08Q0IQ0HPVPRPNPMPLPYPrP7f?RMfCS0IfGS0UfOS1GfPS1HQ0]fSS1IP?ODb5b3Q0`Q0oPIP=PoP5%I@%I77W1S0oPhPeQ18PbPe%9f,8<95eCQ0V#9,8<=5eqEpPpPsb6b7b8X0:X1:X2:AK81@S0`12@F;M8R^Q0s127fP7Q0VP1DB[^0:^1:^2:P8PLPYPrQ0]O4Rfb5b3Q0aQ0nPIP=PoP5Q0oPhPeQ18PbPe%9d,8<95eCQ0X#9,8<=5eqEpPpPsb6b7b8X0:X1:X2:Q0s127dP7Q0XP1DB\^^0:^1:^2:Pfb5b3Q0bQ0mPIP=Q0vQ0t':S0t,<zRfPfPfPfQ0x#=R^Q0p/:TS0x,:vS0m':,<uRdQ0w,:^,<uRQPQPdPdPQPQPdPfPfPfPfPfPfPfPfPdPQPQPdPdPQPQPdPfPfPfPfPfPfPfPfQ0u9mvtS0b,:^,<uRD1:a{S0X,<tRtPQPdPdPQPtPDPfPfPfPfPfPfPfPfPDPtPQPdPdPQPtPDPfPfPfPfPfPfPfPfPdPQPQPdPdPQPQPdPfPfPfPfQ0z#=RaPvPX1:c`S0zCJRc1:X{,<aR{P{PcPaPuP^AmvXTS18CJR`P{P{P`P`P{P{P`PcP{P{PcPcP{P{PcP`P{P{P`P`P{P{P`PcP{P{PcPfPfPfPfPDPtPQPdPdPQPtPDPfPfPfPfPfPfPfPfPDPtPQPdPdPQPtPDPfPfPfPfPfPfPfPfPDPtPQPdPdPQPtPDPfPfPfPfPfPfPfPfPdPQPQPdPdPQPQPdPfPfPfPfPfPfPfPfPdPQPQPdPdPQPQPdPfPfPfPfPfPfPfPfPDPtPQPdPdPQPtPDPfPfPfPfPcP{P{PcP`P{P{P`P`P{P{P`PcP{P{PcPcP{P{PcP`P{P{P`P`P{P{P`PcP{P{PcPfPfPfPfPdPQPQPdPdPQPQPdPfPfPfPfPoD0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0P5%IWS0n9WG9P@%IkS0aP2PiPjPiDDS0VP1PiP7%IjS1J?WUiS1KPjPiD|DDPhPePeQ11PeQ19Pe1AemS19PeQ141AelS1LDfDfS1MPbPePePeQ0T#@RfQ0S#6#@Rd7eZPePeQ0W#@S0W,8dS0S%9PS0T,8fRQ'QPePeP:Aq:<}Rcg010DS1NPdCO1AeMS1O18<gR{Q0S55e5\eCHCHCHPbPePeA5eyfS1Pf@R`,AeS1QPbPePePePeQ15/8ZRDPxQ16I0:S161AenS1RPbPeQ13PbPeQ10PbPePeA5eCfA5eQqPbPePePePCQ15PePDPqFSS15PbPeQ0rPbPePeQ0[,AeS1S=\ewQ1<PbPePePCPcPeP{PqFSE^FLE^FLECECFLPpPsb6b7b8X0:X1:X2:X::X;:X>:X?:XC:XD:XB:X4AX9AX<AX=AX@AXAAXEAAKWSBQ1EAKkOB11HkR{;F~9Ej|3FS1T122FS1U12UWRc122P1Z7\/kUAK79c7El3777U11HUS1V/4`12UFQ1V7nBS1WQ0['4Q1?PmPmPOP9DBS0[Q1APmPmPSP3DBS1XQ1BP|P|PPP2DBPcP|P|PFPUDB11KkS1YQ0\Q1F/1BS1Z'4/V{12j|S1[1Z~\P~PmPjDB[[[[[[[[[[^0:^1:^2:^::^;:^>:^?:^C:^D:^B:^4A^9A^<A^=A^@A^AA^EAP811;rS1\Q05Q08Q0<Q0JQ0HQ0GPVPRQ0:P]PNPLQ0;P_PYPrP7P|PMQ0UQ1GQ1HQ0^Q0]Q1IP?OKb5b3Q0cQ0lPIP=PuPzP^Q0tCJRKPKPKPKQ0m,<aR`Q0w,<aRDPDP`P`PDPDP`PKPKPKPKPKPKPKPKP`PDPDP`P`PDPDP`PKPKPKPKPKPKPKPKQ0b,<aRQPQPDP`P`PDPQPQPKPKPKPKPKPKPKPKPQPQPDP`P`PDPQPQPKPKPKPKPKPKPKPKP`PDPDP`P`PDPDP`PKPKPKPKQ0{Q18,:a'<RtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPKPKPKPKPQPQPDP`P`PDPQPQPKPKPKPKPKPKPKPKPQPQPDP`P`PDPQPQPKPKPKPKPKPKPKPKPQPQPDP`P`PDPQPQPKPKPKPKPKPKPKPKP`PDPDP`P`PDPDP`PKPKPKPKPKPKPKPKP`PDPDP`P`PDPDP`PKPKPKPKPKPKPKPKPQPQPDP`P`PDPQPQPKPKPKPKPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPtPKPKPKPKP`PDPDP`P`PDPDP`PKPKPKPKPoD0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0P5Q0n9WijP@Q0VP1PGPjPiP7Q1K?W9iDDDDPhPeQ1MPbPePePeQ0}#@RG?eZ<PePe18<fRfQ0T,8GRK'QPePeP:Aq:d}Q1NP<COPePeQ17Q0W'QQ0S=5efCHCHCHCHPbPePeA5eyGQ1OPbPePePePeQ00#@Rf/8ZRZPxPePyPfFSQ1QPbPeQ13PbPeQ10PbPePeA5eCGA5eKqPbPePeA5eCfA5eZqPbPeQ0rPbPeQ1R=\ewQ1<609ePbPeQ1:PeAe<}qC`FLE^E^FLECECFLPpPsb6b7b8X0:X1:X2:X::X;:X>:X?:XC:XD:XB:X4AX9AX<AX=AX@AXAAQ1TQ1>1272R}123P1ZU\/k711[W11c}3E37777Q1=/4MQ1U/1BQ1=;FnQ0[Q1XQ1B/1jR}12jP;M2PcPj12jFRFPUC;Q1YfHQ1Z'4/V{Q1[P~P~P\PjDB[[[[[[[[[[^0:^1:^2:^::^;:^>:^?:^C:^D:^B:^4A^9A^<A^=A^@A^AAP8Q1\Q05Q08Q0JQ0HQ0GPVPRQ0;P_Q0:PNPLP]PYPrP7P|PMQ0UQ1GQ1HQ0^Q0]Q1IP?OJb5b3Q0dQ0kPIP=Pu&08>-07:>06:zRzP^Q0xCJR>Q0vPvQ0pQ0qCJRvPvP>P>PvPvP>P>PvPvP>P>PvPvP>P>PvQ0X,<XR]PuPzP^Q0u,:XCJRXPXP]PvP>P>PvP]PXPXP]PvP>P>PvPvP>P>PvPvP>PaPuPzAm^JTCJR^Q0y,<aRTPTP^P^PTPTP^P^PTPTP^P^PTPTP^P>PvP]PXPXP]PvP>P>PvP]PXPXP]PvP>P>PvP]PXPXP]PvP>P>PvPvP>P>PvPvP>P>PvPvP>P>PvPvP>P>PvP]PXPXP]PvP>P^PTPTP^Q0{PaPJQ0zCJRJPTPTPJPJPTPTPJP^PTPTP^P>PvPvP>P>PvPvP>PoD0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0P5Q0nP3PiP9PiDDP@Q1JP2PiP|PiDDP1Q0a?W|iP|PiP7%I|P|PiP|Q0|DDDDDDPhPePeQ11PeQ19PeQ1LQ14Q1O5\eDfPbPePeQ0>#9Q01#@R>55ePePeP:P<g010kQ03#@Rv,8>COPePeQ0B#9/QvPeQ1QPeQ02#6#@,8>R>95egA5e>yDfCHCHPbPePeQ1PQ1RPbPePeQ16Q1SPbPeQ13PbPeQ10PbPeQ15PbPeQ0rPbPePeQ0I,Ae=\ewQ1<PbPeQ1:Pe1QgqC`E^FLFLECECECECPpPsb6b7b8X0:X1:X2:X::X;:X>:X?:XC:XD:XB:XF:X4AX9AX<AX=AX@AXAAXEAAKkSBQ1@/1B11Hj;Fm9E|~7F{Q0>Aj:7cQ0B/1W12UkRc,1911cH5EM3E77UQ1V/4nQ1WQ0I'4Q1?PlPlPOP9DBQ1APlPlPSP3DBAM}F2Q1CQ0\Q1D'4Q1E'VQ1FP|P~PkC;[[[[[[[[[^0:^1:^2:^::^;:^>:^?:^C:^D:^B:^F:^4A^9A^<A^=A^@A^AA^EAP8Q1\Q05Q08Q0DQ0JQ0HQ0GPVPRQ0EQ0AQ0?PNPLQ0CQ0@PYPrP7PUPMQ0UQ1GQ1HQ0]Q1IP?OKb5b3Q0eQ0jPIP=PoP5%I1PhPePeQ1;1Ae75\eQ1<PbPe1Ae9PeQ0Z#9/QqC`E^PpPsb6b7b8X0:X4AX9AA7;81?MH8Q0Z=M71[^0:^4A^9AP812rYRAQ0Y'111ABPrP?O4b5b3Q0fQ0iPIP=PoP5Q0oPhPePeQ1:PeQ0~=e<qC`RAPbPACuPpPsb6b7b8X0:X1:X2:Q0`12@S;M8Q0s/17RA127S;M1[^0:^1:^2:P8PRPYPrQ1HO4b5b3Q0gQ0hPIP=PoP5Q0oPhPePeQ1:PeQ12=e<qC`RqPbPqCuPpPsb6b7b8X0:X1:X2:Q0`12@O;M8127O=MA1[^0:^1:^2:P8PVPYPrQ1GO4b5b3PIP=PoP5PiPhPeP6P4P4P0I05PpPsb6b7b8Q0hP8b5b3FdFdFdFdFdQ0_9PE?eWIWKP1P8O2n2101000010121000000W3WMP1P8O2n2011000010121000000W3WNP1P8O2n2011000010121000000W3WLP1P8O2n2011000010121000000W3WHP1P8O2n2011000010121000000W3WOP1P8O2n2111000010121000000W3WJP1P8O2n2011000010121000000APEkWebPUUUUUUUXQ:XG:o"). Qed.
End Kinds.




Definition bnew (c k n : Z) (p : aptr) (b1 ctx : Z) : xbusy := mkXBusy c k n (BLive p) b1 ctx.
Definition xfast (X : aconc) (c k n : Z) (p : aptr) (b1 ctx : Z) : aconc :=
  mkAConc (fun c' => if c' =? c then mkXClass (xc_free (x_cls X c)) (removelast (xc_cache (x_cls X c))) else x_cls X c')
          (bnew c k n p b1 ctx :: x_busy X).

Lemma xfast_busy_of : forall X c k n p b1 ctx c' k',
  busy_of (xfast X c k n p b1 ctx) c' k' = if (c =? c') && (k =? k') then Some (bnew c k n p b1 ctx) else busy_of X c' k'.
Proof. intros. unfold xfast, busy_of. cbn. destruct ((c =? c') && (k =? k')); reflexivity. Qed.
Lemma xfast_busy_slots : forall X c k n p b1 ctx c',
  busy_slots (xfast X c k n p b1 ctx) c' = (if c =? c' then [k] else []) ++ busy_slots X c'.
Proof. intros. unfold xfast, busy_slots. cbn. destruct (c =? c'); reflexivity. Qed.
Lemma xfast_cls : forall X c k n p b1 ctx c',
  x_cls (xfast X c k n p b1 ctx) c' = if c' =? c then mkXClass (xc_free (x_cls X c)) (removelast (xc_cache (x_cls X c))) else x_cls X c'.
Proof. reflexivity. Qed.




Lemma awf_fast : forall L st X c k n cnt b1 ctx,
  awf L st X -> 1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k -> busy_of X c k = None ->
  1 <= n <= AREQMAX -> rounded_size n + rz_size n <= size_of_class c -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  awf L (st_fast st c n cnt) (xfast X c k n (a_next st) b1 ctx).
Proof.
  intros L st X c k n cnt b1 ctx WF HC CNT POS NK NB N FIT B1 AT1 CTX.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (st_fast_fields st c n cnt) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (CACHE : xc_cache (x_cls X c) = removelast (xc_cache (x_cls X c)) ++ [k]).
  { apply cache_split_last. rewrite <- NK. f_equal. clear -LENC CNT. lia. }
  assert (LRL : Z.of_nat (length (removelast (xc_cache (x_cls X c)))) = cnt - 1).
  { rewrite length_removelast; [clear -LENC CNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC CNT POS. lia. }
  assert (PNE : forall p ch, a_live st !! p = Some ch -> p <> a_next st).
  { intros p ch Hp E. pose proof (FRESH p ch Hp) as F. subst p. clear -F. lia. }
  unfold awf. rewrite E1, E2, E6, E7.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  { (* [comment removed for export] *)
    intros c' HC'. rewrite st_fast_cls, st_fast_max_count, st_fast_ndist, xfast_cls, xfast_busy_slots.
    destruct (Z.eqb_spec c' c) as [->|NE].
    - rewrite Z.eqb_refl. cbn [xc_free xc_cache c_allocated_user c_mapped_user c_num_freed c_mapped_free_array c_count cls_set_count app].
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
      split; [exact LENF|]. split; [exact LRL|]. split; [clear -CNTB CNT POS; lia|].
      rewrite CACHE in ND, RANGE. rewrite <- !app_assoc in ND, RANGE. cbn [app] in ND, RANGE.
      split; [exact ND | exact RANGE].
    - destruct (Z.eqb_spec c c') as [EQ|_]; [exfalso; clear -EQ NE; lia|]. cbn [app].
      destruct (PERC c' HC') as (B1' & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
      cbv zeta. repeat lazymatch goal with |- _ /\ _ => split end.
      all: first [exact B1' | exact B2 | exact B3 | exact B4 | exact B5 | exact B6 | exact B7 | exact BLENF | exact BLENC | exact BCNTB | exact BND | exact BRANGE
                 | exact (proj1 B1') | exact (proj2 B1') | exact (proj1 B6) | exact (proj2 B6) | exact (proj1 BCNTB) | exact (proj2 BCNTB)
                 | idtac]. }
  split.
  { intros c' HC'. rewrite st_fast_cls. destruct (Z.eqb_spec c' c) as [->|NE]; [exfalso; exact (HC' HC)| exact (OUTC c' HC')]. }
  split.
  { (* [comment removed for export] *)
    intros b [<-|Hb].
    - cbn. split; [exact HC|]. split; [exact N|]. split; [exact FIT|]. split; [exact B1|]. split; [exact AT1|]. split; [exact CTX|]. apply lookup_insert_eq.
    - destruct (BUSY b Hb) as [CL M]. split; [exact CL|]. destruct (xb_st b) as [p| |]; [| exact M | exact M].
      destruct M as (M1 & M2 & M3 & M3' & M4 & M5). split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M3'|]. split; [exact M4|].
      rewrite lookup_insert_ne by (symmetry; eapply PNE; exact M5). exact M5. }
  split.
  { (* [comment removed for export] *)
    intros p c0 n0 Hp. destruct (N.eq_dec p (a_next st)) as [->|NE].
    - rewrite lookup_insert_eq in Hp. injection Hp as <- <-. exists (bnew c k n (a_next st) b1 ctx). split; [left; reflexivity|]. cbn. auto.
    - rewrite lookup_insert_ne in Hp by congruence. destruct (LIVE p c0 n0 Hp) as (b & Hb & R). exists b. split; [right; exact Hb| exact R]. }
  split.
  { intros p ch Hp. destruct (N.eq_dec p (a_next st)) as [->|NE]; [clear; lia|].
    rewrite lookup_insert_ne in Hp by congruence. pose proof (FRESH p ch Hp) as F. clear -F. lia. }
  (* [comment removed for export] *)
  intros b0 b2 [<-|H0] [<-|H2] EQ [p Hp]; [reflexivity| exfalso | exfalso | exact (UNIQ b0 b2 H0 H2 EQ (ex_intro _ p Hp))].
  - cbn in EQ. destruct (BUSY b2 H2) as [_ M]. rewrite <- EQ in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (PNE _ _ M5 eq_refl).
  - cbn in EQ. destruct (BUSY b0 H0) as [_ M]. rewrite EQ in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (PNE _ _ M5 eq_refl).
Qed.




Lemma ablocks_fast : forall L st X LB c k n cnt b1 ctx,
  awf L st X -> ablocks L st X LB ->
  ablocks L (st_fast st c n cnt) (xfast X c k n (a_next st) b1 ctx) (HB (a_next st) (aslot_addr L c k + rz_size n) n :: LB).
Proof.
  intros L st X LB c k n cnt b1 ctx WF (BH & BF & NDI & NDL).
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _ & FRESH & _).
  assert (OLD : forall p A n', In (HB p A n') LB -> (p < a_next st)%N).
  { intros p A n' Hin. destruct (BH p A n' Hin) as [(b & Hb & Sb & _)|(mb & ms & Lp & _)].
    - destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (FRESH _ _ M5).
    - exact (FRESH _ _ Lp). }
  split; [| split; [| split]].
  - intros p A n' [E|Hin].
    + injection E as <- <- <-. left. exists (bnew c k n (a_next st) b1 ctx). split; [left; reflexivity|]. cbn. unfold xb_user, xb_alloc. cbn. auto.
    + destruct (BH p A n' Hin) as [(b & Hb & R)|(mb & ms & Lp & R)].
      * left. exists b. split; [right; exact Hb| exact R].
      * right. exists mb, ms. split; [| exact R]. pose proof (st_fast_fields st c n cnt) as (_ & _ & _ & _ & _ & E6 & _). rewrite E6.
        rewrite lookup_insert_ne; [exact Lp|]. intros E. pose proof (OLD _ _ _ Hin) as F. rewrite E in F. clear -F. lia.
  - intros cls A n' [E|Hin]; [discriminate| exact (BF cls A n' Hin)].
  - cbn. constructor; [| exact NDI]. intros Hin. unfold hb_ids in Hin. apply in_flat_map in Hin. destruct Hin as (b & Hb & Hp).
    destruct b as [[p|cls] A n']; cbn in Hp; [| destruct Hp]. destruct Hp as [E|[]]. subst p. pose proof (OLD _ _ _ Hb) as F. clear -F. lia.
  - constructor; [| exact NDL]. intros Hin. pose proof (OLD _ _ _ Hin) as F. clear -F. lia.
Qed.




Definition unbx {P : Prop} (b : boxed P) : P := match b with Box _ p => p end.

Lemma aheap_pres_fast : forall (CI : list (Z * Z)) sp t c AB S UB PGE n nodes store res ctx lo grz ssz (LB : list ablock) m m',
  kfacts sp t c AB S UB PGE n nodes store res ctx lo grz ssz ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI ->
  munch (Wn sp t c AB UB PGE n nodes store) m m' -> wmono bsegs m m' ->
  (forall b, In b LB -> disjoint_from (Wn sp t c AB UB PGE n nodes store) (ab_addr b) (ab_size b)) ->
  (forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
       disjoint_from (Wn sp t c AB UB PGE n nodes store) (shad a') 1) ->
  PGE <= shad ATOP ->
  aheap_pres CI LB sp m m'.
Proof.
  intros CI sp t c AB S UB PGE n nodes store res ctx lo grz ssz LB m m' KF CIOK MU WM HBK HFK PSP a Ha CL.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha.
  pose proof KF as KF'. destruct KF' as (F_lo & F_t & F_c & F_res & F_slot & F_sh & F_ns & F_ctx).
  destruct CL as [ST | [CIa | [BLK | SH]]].
  - eapply disjoint_outside; [eapply (K_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); lia | lia].
  - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
    eapply disjoint_outside; [eapply (K_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); unfold AIMG_HI in *; lia | lia].
  - destruct BLK as (b & Hb & R). eapply disjoint_outside; [exact (HBK b Hb) | lia].
  - destruct SH as (a' & Ha' & ->).
    pose proof (shad_div a') as SD. pose proof (shad_div ATOP) as SDs. unfold ASHOFF in *.
    destruct Ha' as [ST | [CIa | FK]].
    + eapply disjoint_outside; [eapply (K_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: clear -ST SD SDs F_sh PSP; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
    + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (K_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: unfold AIMG_HI in *; clear -R SD Q1 Q3; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
    + destruct FK as (cls & FA & sz & Hin & R). eapply disjoint_outside; [exact (HFK cls FA sz Hin a' R) | lia].
Qed.

Lemma b1'_range : forall b1, 0 <= b1 -> 0 <= Z.lor (Z.land (hdr_b1_mid b1) 243) 0 < 256.
Proof.
  intros b1 Hb. rewrite Z.lor_0_r. pose proof (hdr_b1_mid_range b1 Hb) as [R0 R1].
  assert (A0 : 0 <= Z.land (hdr_b1_mid b1) 243) by (apply Z.land_nonneg; right; lia).
  split; [exact A0|].
  destruct (Z.eq_dec (Z.land (hdr_b1_mid b1) 243) 0) as [->|NZ]; [lia|].
  change 256 with (2^8). apply lt_pow2_of_log2; [lia|].
  pose proof (Z.log2_land (hdr_b1_mid b1) 243 R0 ltac:(lia)) as L1.
  replace (Z.log2 243) with 7 in L1 by reflexivity. lia.
Qed.

Lemma b1'_at1 : forall b1, 0 <= b1 < 256 -> Z.land (Z.lor (Z.land (hdr_b1_mid b1) 243) 0) 3 = 1.
Proof.
  intros b1 Hb.
  assert (C : forallb (fun i => Z.land (Z.lor (Z.land (hdr_b1_mid (Z.of_nat i)) 243) 0) 3 =? 1) (seq 0 256) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) C (Z.to_nat b1) ltac:(apply in_seq; lia)) as C1. cbn beta in C1.
  rewrite Z2Nat.id in C1 by lia. apply Z.eqb_eq. exact C1.
Qed.



Lemma arng_fast : forall L RNG st X c n cnt, awf L st X -> arng L RNG st -> arng L RNG (st_fast st c n cnt).
Proof.
  intros L RNG st X c n cnt WF (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RC & RPA & RSC & RPSH).
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _).
  pose proof (st_fast_fields st c n cnt) as (_ & _ & E3 & _ & _ & E6 & _ & E8 & _ & E10 & _).
  unfold arng. repeat (split; [assumption|]). split; [| split].
  - intros c' Hc'. pose proof (st_fast_counters st c n cnt c') as (E1 & E2 & _ & E4 & E5). cbv zeta. rewrite E1, E4. exact (RC c' Hc').
  - rewrite E3. exact RPA.
  - split; [| exact RPSH]. eapply RSEC_perm; [apply Permutation_sym; eapply (sec_chunks_of_insert_prim st _ (a_next st) c n); [| exact E6| exact E8| exact E10]| exact RSC].
    destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as F. clear -F. lia.
Qed.




Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

Theorem store_fast : store_fast_stmt DI AQ ASEC AFK CI.
Proof.
  unfold store_fast_stmt. intros L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X n lo c cnt k b1 maxc csz. cbv zeta.
  intros ALO ARNG AR BL HFK N HC0 HCNT POS NK NB KR HMX HCSZ B1 CEIL LO LHJ TL SHpre SHsuf CSa CSc ms' PM.
  clear SHpre SHsuf. unfold AMALLOC_STACK in LO.
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  pose proof (class_small_facts n c N HC0) as (C16 & HC & SZC & NSZ).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & STATS0 & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5). clear CL5.
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10). clear DL9 DL10.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT TBND] & [jT TIMG]). pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (_ & _ & [kC CBND]).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (_ & _ & [kN NBND]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (_ & _ & [kS SBND]). unfold AIMG_HI in DL3, DL6, CL3.
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (ao_res L ALO) as RES. unfold aobj in RES. pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t.
  word_range sp SPR.
  assert (CIN : a_cinit st = true).
  { unfold max_count in CNTB. destruct (a_cinit st); [reflexivity| exfalso]. rewrite HCNT in CNTB. clear -CNTB POS. lia. }
  pose proof (max_cached_le16 c ltac:(clear -C16; lia)) as MC16.
  assert (CNT16 : 0 < cnt <= 16) by (unfold max_count in CNTB; rewrite CIN, HCNT in CNTB; clear -CNTB POS MC16; lia).
  set (S := size_of_class c) in *.
  pose proof (slot_in_region L st c k ltac:(clear -SZC C16; subst S; lia) (proj1 A1) KR) as (G5 & G4 & KS0). fold S in G5, G4, KS0.
  set (AB := aslot_addr L c k) in *.
  assert (G1 : al_space_beg L <= AB) by (unfold aregion, K_REGION in G5; clear -G5 C16; lia).
  assert (G2 : AB + S <= al_space_beg L + K_SPACE_SIZE).
  { unfold aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF in *. generalize G4 A1 A2 C16; clear; intros. change (2^37) with 137438953472. lia. }
  assert (G3 : AB mod 16 = 0) by (subst AB; apply slot_aligned; [exact SAL| exact HCK]).
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.
  pose proof (rz_size_small_cases n N) as RZC.
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
  set (grz := shlen (rz_size n)) in *. set (g := shlen (n - n mod 8)) in *. set (room := if n mod 8 =? 0 then 0 else 1) in *.
  assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8) by (subst grz g; rewrite !shlen_div; split; reflexivity).
  destruct GR12 as [GR1 GR2].
  assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
  assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
  assert (RMQ : room = (if n mod 8 =? 0 then 0 else 1)) by reflexivity. clearbody room.
  assert (GR5 : 0 <= room <= 1) by (rewrite RMQ; clear; destruct (n mod 8 =? 0); lia).
  assert (SS8 : shlen S = S / 8) by (rewrite shlen_div; reflexivity).
  assert (GR6 : grz + g + room <= shlen S).
  { rewrite GR1, GR2, SS8, RMQ. generalize NSZ NS RSR RSM SZC C16 N RZC. clear. intros.
    destruct RZC as [E|[E|E]]; rewrite E in *; destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
  assert (GR7 : shad UB = shad AB + grz).
  { rewrite GR1, EUB. rewrite !shad_div. generalize G3 RZC. clear. intros. destruct RZC as [E|[E|E]]; rewrite E; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
  assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000 /\ shad AB + shlen S = shad (AB + S)).
  { rewrite SS8, !shad_div. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 G3 SP1 SP2 SZC C16 ES. clear. intros. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
  destruct GR89 as (GR8 & GR9 & GR10).
  set (PG := shad UB + g) in *.
  assert (PGE_ : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
  assert (ROOM : granules n = g + room) by (subst g; rewrite RMQ; apply granules_eq; clear -N; lia).
  assert (GR11 : 1 <= g + room).
  { subst g. rewrite RMQ, shlen_div. generalize N; clear; intros. destruct (Z.eqb_spec (n mod 8) 0); first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
  assert (BB : forall b, In b (x_busy X) ->
      al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104
      /\ (xb_alloc L b + size_of_class (xb_class b) <= AB \/ UB + n <= xb_alloc L b)
      /\ xb_alloc L b mod 16 = 0 /\ 16 <= size_of_class (xb_class b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc. split; [| split; [| split; [| split; [apply slot_aligned; [exact SAL| exact CLB] | clear -QS; lia]]]].
    - unfold aregion, K_REGION in P5. clear -P5 CLB RSP. unfold K_NUM_CLASSES in CLB. lia.
    - unfold aregion, K_REGION, K_FREEARR_OFF in *. clear -P4 Q1 Q2 CLB RSP. unfold K_NUM_CLASSES in CLB. lia.
    -
      destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
      + rewrite EC in *. assert (NKb : xb_slot b <> k).
        { intros EK. enough (busy_of X c k <> None) by congruence. unfold busy_of.
          destruct (List.find _ _) eqn:FE; [discriminate|]. exfalso.
          apply (find_none _ _ FE) in Hb. rewrite EC, EK, !Z.eqb_refl in Hb. discriminate. }
        destruct (slots_disjoint L c (xb_slot b) k ltac:(clear -KB; lia) ltac:(clear -KR; lia) NKb ltac:(clear -SZC C16; lia)) as [D|D];
          rewrite <- EAB in D; fold S in D; [left; exact D| right].
        clear -D EUB RZR N NSZ NS RSR ES. subst S. lia.
      + assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
        unfold K_REGION, K_FREEARR_OFF in *.
        destruct (proj1 (Z.lt_gt_cases (xb_class b) c) NC) as [LT|GT]; [left | right].
        * specialize (RC _ _ LT). clear -RC P4 Q1 Q2 G5. lia.
        * specialize (RC _ _ GT). clear -RC P5 G4 A1 A2 EUB N NSZ NS RSR RZR ES. subst S. lia. }
  destruct PM as (id & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & sj' & stj'
                  & -> & MU & WM & MI' & ST' & IDR & CR' & STS' & STATS' & LSJ' & UW' & HDR' & UF' & LH' & SHU' & SHP' & DEP').
  assert (MUn : munch (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) m m').
  { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. subst PG. generalize GR3 GR4 GR5 GR7. clear. intros. lia. }
  clear MU.
  assert (KF : kfacts (bv_unsigned sp) (al_t L) c AB S UB (PG + room) n (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo grz (shlen S)).
  { unfold kfacts. subst PG. unfold AMALLOC_STACK, K_SPACE_SIZE in *. change (2^37) with 137438953472 in G2.
    generalize CEIL LO TL1 TL2 TL4 C16 RES RHI RSP G1 G2 EUB RZR N NSZ NS RSR ES GR8 GR7 GR3 GR4 GR5 GR6 GR9 GR11 DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *.
    repeat split; first [lia | assumption | match goal with |- ?G => idtac "KF-LEFT" G end]. }
  pose proof (K_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (K_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (K_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (K_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (K_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_c_t) (unbx D_c_res) (unbx D_c_n) (unbx D_c_s)) as Kctx.
  pose proof (K_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_t_res) (unbx DL7) (unbx DL8)) as Kt.
  pose proof (K_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_t_res) (unbx D_n_res) (unbx D_s_res)) as Kres.
  pose proof (K_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  change (set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st)) (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)))
    with (st_fast st c n cnt).
  set (b1' := Z.lor (Z.land (hdr_b1_mid b1) 243) 0) in *.
  pose proof (b1'_range b1 ltac:(clear -B1; lia)) as B1R. fold b1' in B1R.
  set (X' := xfast X c k n (a_next st) b1' id).
  pose proof (st_fast_fields st c n cnt) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (WF' : awf L (st_fast st c n cnt) X').
  { apply awf_fast; [exact WF | exact HCK | exact HCNT | exact POS | exact NK | exact NB | clear -N; unfold AREQMAX; lia | | exact B1R | apply b1'_at1; clear -B1; lia | clear -IDR; lia].
    fold S. clear -NS NSZ. lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L (st_fast st c n cnt) m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact E3 | exact E4 | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (THR' : athread L (st_fast st c n cnt) X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear -C16; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear -C16; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      + destruct (CACHES c HCK) as [tail (CR & CH & LCH)]. unfold acache_cells. cbv zeta.
        pose proof (st_fast_counters st c n cnt c) as (_ & _ & _ & _ & EC5). rewrite Z.eqb_refl in EC5.
        rewrite EC5, st_fast_max_count, E5, CIN. unfold X'. rewrite xfast_cls, Z.eqb_refl. cbn [xc_cache].
        exists (Z_to_bv 64 (acompact c k) :: tail).
        assert (CACHE : xc_cache (x_cls X c) = removelast (xc_cache (x_cls X c)) ++ [k]).
        { apply cache_split_last. rewrite <- NK. f_equal. clear -LENC HCNT. lia. }
        split; [| split].
        * unfold acache_addr. rewrite HMX, HCSZ in CR'. fold S. exact CR'.
        * eapply u32arr_frame; [| exact MUn | exact WM |].
          -- rewrite CACHE, map_app in CH. cbn [map] in CH. rewrite <- app_assoc in CH. cbn [app] in CH. exact CH.
          -- rewrite length_app, length_map. cbn [length]. unfold acache_addr.
             assert (LRL : (length (removelast (xc_cache (x_cls X c))) + Datatypes.S (length tail) = 16)%nat).
             { rewrite length_removelast; [clear -LCH LENC HCNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC HCNT POS. lia. }
             rewrite LRL. apply Kt; clear -C16; lia.
        * cbn [length]. rewrite length_removelast; [clear -LCH LENC HCNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC HCNT POS. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | | exact E5 | |].
        * pose proof (st_fast_counters st c n cnt c') as (_ & _ & _ & _ & EC5). rewrite EC5. destruct (Z.eqb_spec c' c) as [EQ'|_]; [exfalso; clear -EQ' NE; lia| reflexivity].
        * unfold X'. rewrite xfast_cls. destruct (Z.eqb_spec c' c) as [EQ'|_]; [exfalso; clear -EQ' NE; lia| reflexivity].
        * unfold acache_addr. unfold K_NUM_CLASSES in Hc'. apply Kt; clear -C16 Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact CSa | exact MUn | exact WM | intros _; apply Kt; clear -C16; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [exact CSc | exact MUn | exact WM | intros _; apply Kt; clear -C16; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (UBN : AB + 16 <= UB /\ UB + n <= AB + S) by (clear -EUB RZR N NSZ NS RSR; lia).
  assert (PGB : PG + room <= shad (AB + S)) by (subst PG; rewrite GR7, <- GR10; clear -GR6; lia).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L (st_fast st c n cnt) m' c'' /\ afreearray L (st_fast st c n cnt) X' m' c''
      /\ aslots L (st_fast st c n cnt) X' m' c'' /\ aslot_shadow L (st_fast st c n cnt) X' m' c'').
  { intros c'' Hc''. destruct (CLS c'' Hc'') as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (st_fast_counters st c n cnt c'') as (EC1 & EC2 & EC3 & EC4 & EC5).
    pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (SIDE : c'' <> c -> aregion L c'' + K_REGION <= AB \/ AB + S <= aregion L c'').
    { intros NE. destruct (proj1 (Z.lt_gt_cases c'' c) NE) as [LT|GT].
      - left. specialize (RC _ _ LT). clear -RC G5. lia.
      - right. specialize (RC _ _ GT). unfold K_REGION, K_FREEARR_OFF in *. clear -RC G4 A1 A2. lia. }
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC3 | exact EC4 | exact EC2 | exact EC1 |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *; change (2^37) with 137438953472 in *; clear -Hc'' RSP G2 EUB NSZ NS RSR RZR N; lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC3 | exact EC4 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + unfold X'. rewrite xfast_cls. destruct (Z.eqb_spec c'' c) as [->|_]; reflexivity.
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *.
        * clear -RI1. lia.
        * clear -RI2 RI3 Q6. lia.
        * clear -Q5 Q6; lia.
        * destruct (Z.eq_dec c'' c) as [->|NE].
          -- right; right. clear -G4 A1 A2 UBN. lia.
          -- destruct (SIDE NE) as [D|D]; [left; clear -D Q6; lia | right; right; clear -D UBN; lia].
      + apply Kshad.
        * rewrite shad_div. unfold ASHOFF, afreearr, K_FREEARR_OFF in *. clear -RI1 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
        * rewrite shad_div, shlen_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -RI2 RI3 Q6 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * destruct (Z.eq_dec c'' c) as [->|NE].
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -G4 A1 A2. lia.
          -- destruct (SIDE NE) as [D|D].
             ++ left. apply shad_sep; [| unfold afreearr, K_FREEARR_OFF; clear -RM''; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]].
                unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -D Q6 UBN. lia.
             ++ right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -D. lia.
    -
      eapply (aslots_update L _ m m' MUn WM st _ X X' c'' (if c'' =? c then k else -1));
        [exact SLOTS | apply st_fast_ndist | exact EC2 | exact EC1 | | |].
      + intros k'' Hk'' NEk. pose proof (slot_in_region L st c'' k'' ltac:(clear -QS; lia) (proj1 Q1) Hk'') as (P5 & P4 & P0).
        split; [| split].
        * unfold X'. rewrite xfast_busy_of. destruct (Z.eqb_spec c c'') as [<-|NE]; [| reflexivity].
          rewrite Z.eqb_refl in NEk. destruct (Z.eqb_spec k k'') as [<-|NK']; [exfalso; exact (NEk eq_refl)| reflexivity].
        * apply Kres; [clear -P5 RI1; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION in *; lia | clear -QS; lia |].
          destruct (Z.eqb_spec c'' c) as [->|NE].
          -- destruct (slots_disjoint L c k'' k ltac:(clear -Hk''; lia) ltac:(clear -KR; lia) NEk ltac:(clear -QS; lia)) as [D|D]; rewrite <- EAB in D; fold S in D;
               [left; exact D | right; right; clear -D EUB RZR N NSZ NS RSR ES; subst S; lia].
          -- destruct (SIDE NE) as [D|D]; [left; clear -D P4 Q1 Q2; unfold K_FREEARR_OFF, K_REGION in *; lia | right; right; clear -D P5 UBN; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c'' k'' b Hb) as (IB & CB' & KB'). split; [exact CB'|]. split; [exact KB'|].
          exact (awf_fits L st X b WF IB).
      + intros POS''. apply Kres; [clear -Q1 RI1; unfold aregion in *; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION in *; lia | clear -POS''; lia |].
        destruct (Z.eqb_spec c'' c) as [->|NE]; [right; right; clear -G4 UBN; lia|].
        destruct (SIDE NE) as [D|D]; [left; clear -D Q1 Q2; unfold K_FREEARR_OFF, K_REGION in *; lia | right; right; clear -D Q1 UBN; lia].
      +
        destruct (Z.eqb_spec c'' c) as [->|NE]; [| intros Hk0; exfalso; clear -Hk0; lia]. intros _.
        unfold X'. rewrite xfast_busy_of, !Z.eqb_refl. cbn [andb].
        unfold aslot_busy, bnew. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot xb_alloc xb_user xb_hdr].
        unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n]. rewrite <- EAB. fold S. rewrite <- EUB.
        split; [| split].
        * intros R16. split.
          -- replace (UB - 16) with (UB + -16) by (clear; lia). unfold AMAGIC. exact (LH' R16).
          -- eapply junk_frame; [exact (LHJ R16) | exact MUn | exact WM |]. intros Hp.
             unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
             apply Kres; clear -Hp R16 RZR G1 RSP G2 EUB RI3 N NSZ NS RSR; lia.
        * exists 2. split; [reflexivity|]. replace (UB - 16) with (UB + -16) by (clear; lia). exact HDR'.
        * replace (S - rz_size n) with (n + (S - rz_size n - n)) by (clear; lia).
          apply (junk_merge m' UB n (S - rz_size n - n)); [| | clear -N; lia | clear -NSZ NS RSR N; lia].
          -- pose proof (junk_of_cells m' _ _ UF') as J. cbn [cells_size csize] in J. rewrite Nat.add_0_r, Z2Nat.id in J by (clear -N; lia). exact J.
          -- eapply junk_frame; [exact TL | exact MUn | exact WM |]. intros Hp.
             unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
             apply Kres; [| | clear -Hp; lia | right; right; clear; lia].
             ++ clear -G1 RSP EUB RZR N. lia.
             ++ clear -G2 RI3 EUB NSZ NS RSR N RZR. lia.
    -
      eapply (aslot_shadow_update L _ m m' MUn WM st _ X X' c'' (if c'' =? c then k else -1));
        [exact SHADOW | apply st_fast_ndist | exact EC2 | exact EC1 | | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk'' NEk. pose proof (slot_in_region L st c'' k'' ltac:(clear -QS; lia) (proj1 Q1) Hk'') as (P5 & P4 & P0).
        pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
        split.
        * unfold X'. rewrite xfast_busy_of. destruct (Z.eqb_spec c c'') as [<-|NE]; [| reflexivity].
          rewrite Z.eqb_refl in NEk. destruct (Z.eqb_spec k k'') as [<-|NK']; [exfalso; exact (NEk eq_refl)| reflexivity].
        * apply Kshad.
          -- rewrite shad_div. unfold ASHOFF. clear -P5 RI1 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
          -- rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -P4 Q1 Q2 RI2 RI3 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
          -- apply shlen_nonneg. clear -QS; lia.
          -- destruct (Z.eqb_spec c'' c) as [->|NE].
             ++ destruct (slots_disjoint L c k'' k ltac:(clear -Hk''; lia) ltac:(clear -KR; lia) NEk ltac:(clear -QS; lia)) as [D|D]; rewrite <- EAB in D; fold S in D.
                ** left. apply shad_sep; [clear -D UBN; lia| clear -AL''; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]].
                ** right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. exact D.
             ++ destruct (SIDE NE) as [D|D].
                ** left. apply shad_sep; [| clear -AL''; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]]. unfold K_FREEARR_OFF, K_REGION in *. clear -D P4 Q1 Q2 UBN. lia.
                ** right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D P5. lia.
      + intros POS''. apply Kshad.
        * rewrite shad_div. unfold ASHOFF, aregion in *. clear -Q1 RI1 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
        * clear -POS''; lia.
        * destruct (Z.eqb_spec c'' c) as [->|NE].
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. exact G4.
          -- destruct (SIDE NE) as [D|D].
             ++ left. apply shad_sep.
                ** unfold K_FREEARR_OFF, K_REGION in *. clear -D Q1 Q2 UBN. lia.
                ** pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM. clear -AM RM''. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
             ++ right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D Q1. lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE]; [| intros Hk0; exfalso; clear -Hk0; lia]. intros _.
        unfold X'. rewrite xfast_busy_of, !Z.eqb_refl. cbn [andb]. rewrite <- EAB. fold S.
        unfold slot_shadow_bytes, bnew. cbn [xb_n xb_st]. unfold block_shadow_bytes.
        change (shlen (rz_size n)) with grz. rewrite <- (shlen_floor n). change (shlen (n - n mod 8)) with g. rewrite ROOM.
        destruct SHADOW as [SHK _]. specialize (SHK k KR). rewrite NB in SHK. rewrite <- EAB in SHK. fold S in SHK. cbn [slot_shadow_bytes] in SHK.
        change (rw_cells bsegs m (shad AB) [CB (Z.to_nat (shlen S)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S)))]) with (fill_at m (shad AB) (shlen S) 250) in SHK.
        destruct (fill_split m (shad AB) grz (shlen S - grz) 250 ltac:(replace (grz + (shlen S - grz)) with (shlen S) by (clear; lia); exact SHK)
                    ltac:(clear -GR3; lia) ltac:(clear -GR6 GR4 GR5; lia)) as [F1 R1].
        destruct (fill_split m (shad AB + grz) (g + room) (shlen S - grz - (g + room)) 250
                    ltac:(replace (g + room + (shlen S - grz - (g + room))) with (shlen S - grz) by (clear; lia); exact R1)
                    ltac:(clear -GR4 GR5; lia) ltac:(clear -GR6 GR4 GR5; lia)) as [_ F2].
        eapply fill_frame in F1; [| exact MUn | exact WM | intros _; apply Kshad; [clear -GR8; lia | clear -GR9 GR6 GR4 GR5 GR3; lia | clear -GR3; lia | left; clear -GR7; lia]].
        replace (shad AB + grz + (g + room)) with (PG + room) in F2 by (subst PG; clear -GR7; lia).
        eapply fill_frame in F2; [| exact MUn | exact WM | intros Hp; apply Kshad; [subst PG; clear -GR8 GR7 GR3 GR4 GR5; lia | clear -GR9 GR6 GR7 GR3 GR4 GR5 Hp; subst PG; lia | clear -Hp; lia | right; clear; lia]].
        unfold fill_at in F1, F2. change (shlen (n - n mod 8)) with g in SHU'.
        replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat grz)) in SHU' by (clear -GR7 GR3; lia).
        destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
        * assert (R0 : room = 0) by (rewrite RMQ; reflexivity). clearbody PG. subst room. rewrite app_nil_r.
          replace (PG + 0) with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g)) in F2 by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          pose proof (cb_app m' _ _ _ _ _ F1 (cb_app m' _ _ _ _ _ SHU' F2)) as FIN.
          replace (Z.to_nat grz + (Z.to_nat g + Z.to_nat (shlen S - grz - (g + 0))))%nat with (Z.to_nat (shlen S)) in FIN by (clear -GR3 GR4 GR6; lia).
          exact FIN.
        * assert (RM1 : room = 1) by (rewrite RMQ; reflexivity). clearbody PG. subst room. specialize (SHP' M0). apply cb_of_C1 in SHP'.
          replace PG with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g)) in SHP' by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          replace (PG + 1) with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g) + Z.of_nat 1) in F2 by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          pose proof (cb_app m' _ _ _ _ _ F1 (cb_app m' _ _ _ _ _ SHU' (cb_app m' _ _ _ _ _ SHP' F2))) as FIN.
          replace (Z.to_nat grz + (Z.to_nat g + (1 + Z.to_nat (shlen S - grz - (g + 1)))))%nat with (Z.to_nat (shlen S)) in FIN by (clear -GR3 GR4 GR6; lia).
          rewrite <- app_assoc. cbn [app] in FIN. exact FIN. }
  assert (HQ' : AQ L (st_fast st c n cnt) X' m').
  { eapply (hq_frame _ HL L st (st_fast st c n cnt) X X' m m'); [exact HQ | exact MUn | exact WM | |].
    - unfold quar_untouched. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      do 10 (apply Forall_cons; [cbn [fst snd];
        split; [clear -CEIL LO TL1 TL2 C16 G1 G2 RSP RES EUB RZR N UBN GR8 GR7 GR3 GR11 PGB GR10 GR9 DL1 DL2 DL4 DL5 D_t_res DL7 DL8 TBND TIMG NBND DL3 SBND DL6 RHI; unbox D_t_res; unbox DL7; unbox DL8; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5); destruct (xb_st b); [exact I| |];
        clear -Bb1 Bb2 Bb3 CEIL LO RES C16 EUB RZR N GR8 GR7 GR3 GR11 PGB GR10 GR9 G2 DL1 DL2 DL4 DL5 D_t_res D_n_res D_s_res UBN NBND DL3 SBND DL6 RHI;
        unbox D_t_res; unbox D_n_res; unbox D_s_res; lia |]).
      apply Forall_nil.
    - unfold quar_same. rewrite E1, E8, E9, E10, E11. repeat (split; [reflexivity|]). split.
      + intros b Hb. destruct (xb_st b); [exact I| right; exact Hb | right; exact Hb].
      + intros b [<-|Hb]; [exact I|]. destruct (xb_st b); [exact I| exact Hb | exact Hb]. }
  assert (HS' : ASEC L (st_fast st c n cnt) X' m').
  { eapply (hs_frame _ HL L st (st_fast st c n cnt) X X' m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad AB).
      { rewrite !shad_div. unfold aregion, K_REGION in G5. change (2^32) with 4294967296 in G5. clear -G5 C16. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
      assert (SHB2 : shad (AB + S) <= shad (al_space_beg L) + 17179869184).
      { rewrite !shad_div. clear -G2. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 3 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL2 C16 TBND TIMG; lia |]).
      do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G1 G2 UBN N RSP; lia |]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha GR7 GR3 PGB SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; unfold AIMG_HI; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_nil.
    - unfold sec_same. rewrite E2, E3, E4, E6. repeat (split; [reflexivity|]).
      assert (NONE : (a_live st) !! (a_next st) = None).
      { destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as FF. clear -FF. lia. }
      split.
      + intros p mb ms n'. destruct (N.eq_dec p (a_next st)) as [->|NE].
        * rewrite lookup_insert_eq. split; [intros HH; discriminate| intros HH]. exfalso. rewrite NONE in HH. discriminate.
        * rewrite lookup_insert_ne by congruence. tauto.
      + eapply (sec_chunks_of_insert_prim st _ (a_next st) c n); [exact NONE| exact E6| exact E8| exact E10]. }
  assert (AR' : AREP (AH DI AQ ASEC AFK) L (st_fast st c n cnt) X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|].
    split; [eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUn | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
    split; [| eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
    intros c'' Hc''. pose proof (st_fast_counters st c n cnt c'') as (EC1 & EC2 & EC3 & EC4 & EC5).
    destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). pose proof (aregion_mod L c'' SAL) as RM''. unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    assert (SIDE : c'' <> c -> aregion L c'' + K_REGION <= AB \/ AB + S <= aregion L c'').
    { intros NE. destruct (proj1 (Z.lt_gt_cases c'' c) NE) as [LT|GT].
      - left. specialize (RC _ _ LT). clear -RC G5. lia.
      - right. specialize (RC _ _ GT). unfold K_REGION, K_FREEARR_OFF in *. clear -RC G4 A1 A2. lia. }
    eapply (ashadow_avail_frame L _ m m' MUn WM st); [exact (AVL c'' ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) | exact EC1 | exact EC4 | |].
    - intros POS''. apply Kshad.
      + rewrite shad_div. unfold ASHOFF, aregion in *. clear -Q1 RI1 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
      + clear -POS''; lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE].
        * right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold K_FREEARR_OFF in *. clear -G4 A1. lia.
        * destruct (SIDE NE) as [D|D].
          -- left. apply shad_sep; [| clear -RM'' Q4; unfold K_USER_MAP in *; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]]. unfold K_FREEARR_OFF, K_REGION in *. clear -D Q1 Q2 UBN. lia.
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D Q1. lia.
    - intros POS''. apply Kshad.
      + rewrite shad_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, aregion in *. clear -Q5 Q6 RI1 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
      + rewrite shad_div, shlen_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3 RES RHI. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
      + clear -POS''; lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE].
        * right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -G4 A1 A2 Q5 Q6. lia.
        * destruct (SIDE NE) as [D|D].
          -- left. apply shad_sep; [| unfold afreearr, K_FREEARR_OFF; clear -RM'' Q7; unfold K_FREEARR_MAP in *; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]].
             unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -D Q5 Q6 UBN. lia.
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -D Q1 Q5 Q6. lia. }
  pose proof (ablocks_fast L st X LB c k n cnt b1' id WF BL) as BL'. rewrite <- EAB, <- EUB in BL'. fold X' in BL'.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as (FKi & _ & [kF FKs]). unfold aobj in FKO.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HBK : forall b, In b LB -> disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) (ab_addr b) (ab_size b)).
  { intros [[p|cls] A n'] Hin; cbn [ab_addr ab_size].
    - destruct (proj1 BL p A n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EUA & Gs)].
      + destruct (BB b Hb) as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5).
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
        apply Kres; clear -Bb1 Bb2 Bb3 FIT; lia.
      +
        cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
        destruct (ablk_int _ _ Gs2) as [kB GB].
        apply Kobj; clear -GB Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - destruct (FKD cls A n' Hin) as (K1 & K2 & K3). atop_facts.
      apply Kobj; [clear -K1 K3 FKO FKi FKs; lia | clear -K3 FKO FKi FKs; lia | exact K2 | clear -K1 K3 D_t_f; unbox D_t_f; lia
                  | clear -K1 K3 D_f_res; unbox D_f_res; lia | clear -K1 K3 D_n_f; unbox D_n_f; lia | clear -K1 K3 D_s_f; unbox D_s_f; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO Ha' FKi FKs; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO Ha' FKi FKs; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ] | clear; lia |].
    pose proof D_f_res as DF. unbox DF. destruct DF as [D|D].
    - left. rewrite GR7, (shad_div a'), (shad_div AB). clear -D Ha' K3 RSP G1 GR3. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
    - right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G2. lia. }
  assert (HFK' : AFK L (HB (a_next st) UB n :: LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. unfold aobj in DTO. pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & [kD DTs] & [jD DTi]).
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ PG + room <= shad (al_fake L))
                    /\ 2148244992 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; clear -FKO FKi FKs; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]].
        pose proof D_f_res as DF. unbox DF. destruct DF as [D|D].
        - left. rewrite GR7, shlen_div, (shad_div (al_fake L)), (shad_div AB). clear -D RSP G1 GR3. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
        - right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D RSP G2. lia. }
      destruct SHF as (SHF1 & SHF2 & SHF3).
      do 10 (apply Forall_cons; [cbn [fst snd];
        clear -CEIL LO TL1 TL2 C16 G1 G2 RSP RES EUB RZR N GR8 GR7 GR3 GR11 PGB GR10 GR9 DL1 DL2 DL4 DL5 FKO DTO D1 D2 D3 D4 D_t_f D_f_res D_n_f D_s_f SHF1 SHF2 SHF3 UBN TBND TIMG NBND DL3 SBND DL6 RHI FKi FKs DTs DTi;
        first [ lazymatch goal with
                | |- context [al_t _] => unbox D_t_f; clear D_f_res D_n_f D_s_f
                | |- context [al_nodes _] => unbox D_n_f; clear D_t_f D_f_res D_s_f
                | |- context [al_store _] => unbox D_s_f; clear D_t_f D_f_res D_n_f
                | |- _ => unbox D_f_res; clear D_t_f D_n_f D_s_f
                end; unfold AIMG_HI in *; repeat (split; [lia|]); lia
              | unbox D_t_f; unbox D_f_res; unbox D_n_f; unbox D_s_f; unfold AIMG_HI in *; repeat (split; [lia|]); lia ] |]).
      apply Forall_nil.
    - intros cls FA sz. cbn. split; [intros [E|Hin]; [discriminate| exact Hin] | intros Hin; right; exact Hin]. }
  assert (PSP : PG + room <= shad ATOP).
  { eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. clear -G2 SP2. lia. }
  split; [apply fp_le_refl|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { eapply (aheap_pres_fast CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP]. }
  cbn [fst snd]. exists UB, (repeat (Z_to_bv 8 190) (Z.to_nat n)).
  split; [reflexivity|]. split.
  { unfold ablock_range. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    split; [unfold ablk; right; clear -G1 SP1 EUB RZR UBN G2 SP2 N; lia|]. split; [clear -N; lia|]. split; [clear -UBN G2 SP2; lia|].
    rewrite EUB. clear -G3 RZC. destruct RZC as [E|[E|E]]; rewrite E; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
  split.
  { split; [exact ALO|]. split; [eapply arng_fast; [exact WF| exact ARNG]|]. split; [| exact HFK']. exists X'. split; [exact AR' | exact BL']. }
  split; [exact UF'|].
  destruct ARNG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RCLS & _). destruct (RCLS c HCK) as (RREG & RSREG & _ & _).
  lazymatch type of RSREG with rng ?R (?X - 4096) (?M + 8192) =>
    pose proof (rng_sub' R (X - 4096) (M + 8192) X M RSREG ltac:(clear; lia)) as RSREG_; clear RSREG; rename RSREG_ into RSREG end.
  split; [| split].
  - eapply rng_sub'; [exact RREG|]. clear -G5 G4 A1 UBN. lia.
  - eapply rng_sub'; [exact RSREG|]. pose proof (aregion_mod L c SAL) as RM.
    split; [apply shad_mono; clear -G5 UBN; lia|].
    rewrite <- (shad_add_shlen (aregion L c) (c_mapped_user (get_cls st c))) by (clear -RM; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
    rewrite (shad_div UB), shlen_div, (shad_div (aregion L c + c_mapped_user (get_cls st c))).
    pose proof (size_of_class_facts c HCK) as [_ S16]. fold S in S16.
    clear -UBN G4 A1 G3 S16. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ].
  - intros NP. exfalso. rewrite PRIM in NP. discriminate.
Qed.


Definition amalloc_fastP := amalloc_fast DI AQ ASEC AFK CI store_fast.
End S.

End CANSEC1.
