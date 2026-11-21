(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (1 recorded proof replaced by written proofs (amalloc_fast)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepKit
     AKit AKit2 AModelFacts F_apoison F_aalloc1 F_aalloc2 F_aalloc F_amalloc_icpt.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_amalloc_arep () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstK59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto9implS_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C35stdpp4base4fmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec8AsanCtrl;needed_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8class_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7AHEAP_PC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00I59OSSVerify5KrLib5BothW5ABase6uchain00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib5BothW5ABase4al_UC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7amallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface<amalloc_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib5BothW;AModelFacts;small_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6rz_logC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC59OSSVerify5KrLib5BothW;AModelFactsAclass_small_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib5BothW7ARepKit=kit_cache_popC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_botC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC59OSSVerify5KrLib5BothW7ALayout=alayout_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9alayout_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout;alayout_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rC56Stdlib6ZArith6BinInt1Z:mul_div_leC56Stdlib6ZArith6BinInt1Z?mul_add_distr_rC56Stdlib6ZArith6BinInt1Z7mul_1_lC56Stdlib6ZArith6BinInt1Z8mul_commC46Stdlib6ZArith4Zdiv:Z_mod_multK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init5Logic3and01C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4AKit5boxed01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4AKit5boxed00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AModelFactsCrz_size_small_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:slot_carveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes7reflect00K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5BothW7ARepKit<shadow_carveC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:junk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:c8_of_junkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AModelFacts?max_cached_le16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:max_cachedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8acompactC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayoutAalayout_slot_disjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC59OSSVerify5KrLib5BothW>F_amalloc_icpt@malloc_fast_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_aalloc1<allocA_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_apoison<poison_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5BothW>F_amalloc_icpt@malloc_fast_specC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5BothW;AModelFacts>a_live_put_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AModelFacts>a_next_put_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AModelFacts?amalloc_fast_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4AREPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_fakeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffI47Corelib4Init5Logic2or00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C35stdpp4base6lookupC56Stdlib6NArith6BinNat1N2ltC47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z8eqb_specC59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4RSECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec8AsanCtrl8set_liveC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec8AsanCtrl8set_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib5BothW>F_amalloc_arep2AHC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<ASTATS_WORDSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib5BothW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ATSDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase=AMALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase:AMALLOC_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6UDEPTHC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5BothW5ABase;AMALLOC_SYMC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I59OSSVerify5KrLib4Spec8AsanCtrl3aev00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AINITEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_aalloc_s7ARSSLIMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATSDIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATSDKC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section S.
(* [comment removed for export] *)
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Definition AH : aholes := mkAHoles AQ ASEC (ADEPOT DI) AFK.
Hypothesis HL : ahole_laws AH.
(* [comment removed for export] *)
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_fast_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (n lo c cnt k b1 : Z) (maxc csz : word),
  let S := size_of_class c in let AB := aslot_addr L c k in let UB := AB + rz_size n in let PG := shad UB + shlen (n - n mod 8) in
  alayout_ok L -> arng L RNG st -> AREP AH L st X m -> ablocks L st X LB -> AFK L LB m ->
  1 <= n <= 448 -> class_id (needed_size n) = c -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k -> busy_of X c k = None -> 0 <= k < ndist st c ->
  maxc = Z_to_bv 64 (max_count st c) -> csz = Z_to_bv 64 S -> 0 <= b1 < 256 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  (* [comment removed for export] *)
  (16 < rz_size n -> junk_at m (AB + 16) (rz_size n - 32)) ->
  junk_at m (UB + n) (S - rz_size n - n) ->
  fill_at m (shad AB + 1) (shlen (rz_size n) - 1) 0xfa ->
  fill_at m (PG + (if n mod 8 =? 0 then 0 else 1)) (shlen S - shlen (rz_size n) - shlen (n - n mod 8) - (if n mod 8 =? 0 then 0 else 1)) 0xfa ->
  junk_at m (al_t L + 2768) 16 -> junk_at m (al_t L + 2792) 8 ->
  forall ms',
    malloc_fast_post DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG (if n mod 8 =? 0 then 0 else 1) lo b1 maxc csz m ms' ->
    amalloc_post CI (AHEAP_P AH) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m
      (set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st))
         (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)), Some (a_next st)) RNG ms'.
Hypothesis STORE : store_fast_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem amalloc_fast : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  (* [comment removed for export] *)
  1 <= n <= 448 -> 0 < c_count (get_cls st (class_id (needed_size n))) ->
  (* [comment removed for export] *)
  AHEAP_P AH L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  bv_unsigned sp + 16 < al_top L ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 0 <= n <= AREQMAX ->
  uchain m (al_top L) AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr ->
  In (AMALLOC_PC :: bv_unsigned ra :: tr) (al_U L) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC -> (length tr <= 28)%nat ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (al_top L - lo) ->
  implS bsegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI (AHEAP_P AH) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until RESV. intros N POS AH MI ST BOT LO TOP TP Ha0 NR UC TRU S0NE RA4 RANE LTR SP16 RSTK.
  destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
  remember (class_id (needed_size n)) as c eqn:HC0. symmetry in HC0.
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  pose proof (class_small_facts n c N HC0) as (C16 & HC & SZC & NSZ).
  remember (c_count (get_cls st c)) as cnt eqn:HCNT. symmetry in HCNT.
  destruct (kit_cache_pop AH L st X m c cnt AR ltac:(unfold K_NUM_CLASSES; lia) HCNT POS)
    as (k & chunks & NK & NB & KR & CR & CH & LCH & NTH & JK & FSH).
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c ltac:(unfold K_NUM_CLASSES; lia)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  (* [comment removed for export] *)
  set (S := size_of_class c) in *.
  set (AB := aslot_addr L c k) in *.
  assert (KSF : 0 <= k * S /\ k * S + S <= c_allocated_user (get_cls st c) /\ (k * S) mod 16 = 0).
  { unfold ndist in KR. fold S in KR. rewrite SZC in *.
    assert (P0 : 0 <= k * (32 * c)) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Q1 : k + 1 <= c_allocated_user (get_cls st c) / (32 * c)) by lia.
    assert (M1 : (k + 1) * (32 * c) <= c_allocated_user (get_cls st c) / (32 * c) * (32 * c)) by (apply Z.mul_le_mono_nonneg_r; lia).
    pose proof (Z.mul_div_le (c_allocated_user (get_cls st c)) (32 * c) ltac:(lia)) as M2.
    split; [exact P0|]. split.
    - rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. rewrite (Z.mul_comm (32 * c)) in M2. lia.
    - replace (k * (32 * c)) with ((k * 2 * c) * 16) by lia. apply Z_mod_mult. }
  destruct KSF as (KS0 & KS1 & KS2).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [lia|]. split; [lia|]. split; [| lia].
    clear -SP3 C16 KS2. (Z.div_mod_to_equations; lia). }
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.
  box CL5. box DL7. box DL8. box DL9. box DL10.
  (* [comment removed for export] *)
  pose proof (rz_size_small_cases n N) as RZC.
  destruct (slot_carve m AB S n (rz_size n) JK RZC ltac:(lia) ltac:(fold S in NSZ; lia))
    as (b0 & b1 & szh & szl & ctxj & uj & j1 & j2 & HDR & B1 & UJ & LH & TL).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
  (* [comment removed for export] *)
  set (grz := shlen (rz_size n)). set (g := shlen (n - n mod 8)). set (room := if n mod 8 =? 0 then 0 else 1).
  assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8).
  { subst grz g. unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct GR12 as [GR1 GR2].
  assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR5 : 0 <= room <= 1) by (subst room; clear; destruct (n mod 8 =? 0); lia).
  assert (GR6 : grz + g + room <= shlen S).
  { rewrite GR1, GR2. subst room. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. generalize NSZ NS RSR RSM SZC C16 N RZC. clear. intros.
    destruct RZC as [E|[E|E]]; rewrite E in *;
      destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; Z.div_mod_to_equations; lia. }
  assert (GR7 : shad UB = shad AB + grz).
  { rewrite GR1, EUB. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    generalize G3 RZC. clear. intros. destruct RZC as [E|[E|E]]; rewrite E; Z.div_mod_to_equations; lia. }
  assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 SP1 SP2. clear. intros. Z.div_mod_to_equations. lia. }
  destruct GR89 as [GR8 GR9].
  destruct (shadow_carve m (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) as (SHA & SHpre & [sjunk SHU] & SHP & SHsuf).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.
  (* [comment removed for export] *)
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKx. clear HKx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  destruct (c8_of_junk m _ CS8) as [stj STS].
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  destruct ARNG as (RIMG & RT4 & RCTX & RNO & RST & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c ltac:(unfold K_NUM_CLASSES; lia)) as (RREG & RSREG & RFA & RSFA).
  pose proof (max_cached_le16 c ltac:(lia)) as MC16.
  (* [comment removed for export] *)
  assert (ACK : bv_unsigned (Z_to_bv 64 (acompact c k)) = k * 2 * c /\ k * 2 * c < 2^32).
  { unfold acompact. fold S. rewrite SZC. replace (32 * c / 16) with (2 * c) by (generalize C16; clear; intros; Z.div_mod_to_equations; lia).
    replace (k * (2 * c)) with (k * 2 * c) by lia.
    assert (B : 0 <= k * 2 * c < 2^32).
    { unfold K_FREEARR_OFF in A2. rewrite SZC in KS1, KS0. generalize KS0 KS1 A1 A2 C16; clear; intros. lia. }
    rewrite unsigned_lit by lia. lia. }
  destruct ACK as [ACK1 ACK2].
  assert (HABf : AB = al_space_beg L + c * 2 ^ 32 + 16 * bv_unsigned (Z_to_bv 64 (acompact c k))).
  { rewrite ACK1, EAB. unfold aslot_addr, aregion, K_REGION. fold S. rewrite SZC. generalize C16; clear; intros; lia. }
  destruct (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 A1 A2 C16 SP1 SZC; clear; intros; change (2^37) with 137438953472; lia) ltac:(lia))
    as (DJT & DJC & DJN & DJS & DJF).
  assert (RUf : rng RNG (UB - 16) (n + 16)) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 A1 RZR N EUB KS0 NSZ NS RSR; clear; intros; lia).
  assert (RABf : rng RNG AB 16) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 A1 RZR N NSZ NS RSR; clear; intros; lia).
  assert (REG8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st c) mod 8 = 0).
  { unfold aregion, K_REGION, K_USER_MAP, K_ALIGN in *. generalize SP3 A4; clear; intros. Z.div_mod_to_equations; lia. }
  assert (SHM : shad (aregion L c) <= shad AB /\ shad UB + g + room <= shad (aregion L c) + shlen (c_mapped_user (get_cls st c))).
  { rewrite GR7, GR2, GR1. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. subst room. generalize G4 G5 A1 N NSZ RSR RSM NS RZR RZC G3 EUB REG8; clear; intros.
    destruct RZC as [E|[E|E]]; rewrite E in *; destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. }
  destruct SHM as [SHM1 SHM2].
  assert (RSAf : rng RNG (shad AB) 1) by (eapply rng_sub'; [exact RSREG|]; generalize SHM1 SHM2 GR3 GR4 GR5 GR7; clear; intros; lia).
  assert (RSUf : rng RNG (shad UB) (shlen (n - n mod 8))).
  { eapply rng_sub'; [exact RSREG|]. fold g. generalize SHM1 SHM2 GR3 GR4 GR5 GR7. clear. intros. lia. }
  assert (RSPf : n mod 8 <> 0 -> rng RNG PG 1).
  { intros NE. eapply rng_sub'; [exact RSREG|]. subst PG.
    assert (R1 : room = 1) by (subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity]).
    rewrite R1 in SHM2. generalize SHM1 SHM2 GR3 GR4 GR7; clear; intros. lia. }
  assert (SB34 : 0 <= shlen (n - n mod 8) <= 56 /\ PG + 1 <= 0x10007fff8000).
  { subst PG. fold g. rewrite GR7. generalize GR2 GR6 GR9 GR3 GR5 N; clear; intros. split; [Z.div_mod_to_equations; lia| lia]. }
  destruct SB34 as [SB3 SB4].
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  assert (DJC4 : al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) by (generalize DJC; clear; intros; lia).
  assert (CNT16 : 0 < cnt <= 16).
  { unfold max_count in CNTB. generalize POS HCNT CNTB MC16; clear. destruct (a_cinit st); intros; lia. }
  assert (PGE : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
  (* [comment removed for export] *)
  rewrite (amalloc_fast_eq RESV st n c N HC0 ltac:(rewrite HCNT; exact POS)). rewrite HCNT.
  apply implS_ret.
  eapply evtF_mono.
  { eapply (malloc_fast_spec DI L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n (al_t L) c cnt (al_space_beg L) AB UB PG room lo b0 b1 szh szl ctxj
              (al_top L) (al_bot L) (Z_to_bv 64 (max_count st c)) (Z_to_bv 64 S) stj (Z_to_bv 64 (acompact c k)) j1 j2 (Z_to_bv 8 0xfa)
              chunks sj sjunk uj tr).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- uchain _ _ _ _ _ _ _ => exact UC
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- u32arr _ _ _ _ => exact CH
         | |- nth_error _ _ = _ => exact NTH
         | |- (16 < _) -> _ => let R16 := fresh in intros R16; exact (proj1 (LH R16))
         | |- ~ _ -> rng _ _ _ => exact RSPf
         | |- ~ _ -> _ => let NE := fresh in intros NE; apply SHP; subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity]
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ (_ + -16) _ => exact HDR
         | |- rw_cells _ _ (shad _) [C1 _] => exact SHA
         | |- rw_cells _ _ (shad _) [CB _ _] => exact SHU
         | |- rw_cells _ _ _ [CB _ _] => exact UJ
         | |- rw_cells _ _ (_ + 2784) _ => exact STS
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         | |- _ \/ _ => first [exact DJT | exact DJN | exact DJS | exact DJC4 | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- @eq Z _ _ => first [assumption | reflexivity | exact HABf | exact PGE | subst room; reflexivity]
         | |- @eq word _ _ => first [assumption | reflexivity]
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT TOP STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         G1 G2 G3 G4 G5 EUB ES SZC NSZ NS RSR RZR GR3 GR7 GR8 GR9 SB3 SB4 B1 POS HCNT CNT16 ACK1 ACK2 KS0 KS1 HC0 C16 LTR RA4;
              clear; intros; rewrite ?HC0 in *; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia).
    }
  cbv beta. intros ms' PM.
  rewrite !a_next_put_cls, !a_live_put_cls.
  cbv delta [PG g grz room] in PM, SHpre, SHsuf. subst UB. subst AB.
  eapply (STORE L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X n lo c cnt k b1
            (Z_to_bv 64 (max_count st c)) (Z_to_bv 64 (size_of_class c))).
  all: try lazymatch goal with
       | |- malloc_fast_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact PM
       | |- alayout_ok _ => exact ALO
       | |- arng _ _ _ => split; [exact RIMG|]; split; [exact RT4|]; split; [exact RCTX|]; split; [exact RNO|]; split; [exact RST|]; split; [exact RRI|]; split; [exact RFK|]; split; [exact RSFK|]; split; [exact RDTLS|]; split; [exact RCLS|]; split; [exact RPA|]; split; [exact RSECS| exact RPSH]
       | |- AFK _ _ _ => exact HFK
       | |- AREP _ _ _ _ _ => exact AR
       | |- ablocks _ _ _ _ => exact BL
       | |- nth_error _ _ = _ => exact NK
       | |- busy_of _ _ _ = _ => exact NB
       | |- (16 < _) -> _ => let R16 := fresh in intros R16; exact (proj2 (LH R16))
       | |- junk_at _ (_ + 2768) _ => exact CSa
       | |- junk_at _ (_ + 2792) _ => exact CSc
       | |- junk_at _ _ _ => first [exact TL | rewrite ES; exact TL]
       | |- fill_at _ (_ + 1) _ _ => exact SHpre
       | |- fill_at _ _ _ _ => first [exact SHsuf | rewrite ES; exact SHsuf]
       end.
  all: try assumption.
  all: try reflexivity.
  all: try (generalize N KR B1 LO BOT STK3 POS; clear; intros; unfold AMALLOC_STACK in *; lia).
Qed.
End S.
End CANSEC1.
