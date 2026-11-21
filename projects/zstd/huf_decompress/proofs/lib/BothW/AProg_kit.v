(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (58 recorded proofs replaced by written proofs (implMA_fold, implMA_unfold, implMA_ret and 55 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto AMalloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AProg_kit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit6implMAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdI46Stdlib7Sorting;Permutation;Permutation00C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib4Spec<AsanProgDeps5aliftC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation>Permutation_inC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appC45stdpp;list_basics4list9app_inj_1C59OSSVerify5KrLib4LibA6ITreeA@implF_epost_monoC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_mapC46Stdlib5Lists4List8flat_mapI46Stdlib5Lists4List5NoDup00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec<AsanProgDeps3APS00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit;implMA_foldC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit=implMA_unfoldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA<implF_ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib5BothW9AProg_kit:implMA_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA=implF_ret_unrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit:implMA_unrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA;implF_ebindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit;implMA_bindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit;implMA_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA:implF_evtFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit;implMA_evtFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit@implMA_from_evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8SysStepF@implF_epost_evtFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit@implMA_post_evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec5Monad5mwhenC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps8aps_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib5BothW9AProg_kit<implMA_aliftC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec<AsanProgDeps8aps_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps5aps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7amallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps6aset_mC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01c59OSSVerify5KrLib5BothW9AProg_kit:implMA_getC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit:implMA_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps9amalloc_MC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps7afree_MC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec8AsanCtrl5afreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps6aps_soC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K59OSSVerify5KrLib4Spec<AsanProgDeps3APS01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit8aps_restC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit6aps_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface8aresv_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit@aps_resv_of_restC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit@aps_atop_of_restC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree?magree_of_munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree;magree_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega5Tauto8GFormula03C47Corelib5Lists7ListDef6firstnI47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C47Corelib5Lists7ListDef:Forall_indI47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib5BothW9AProg_kit>Forall_firstnAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnc59OSSVerify5KrLib5BothW9AProg_kit=Forall_skipnAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5nshadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase=ablock_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow6blockfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow<shadow_bytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib4LibA6Shadow8shad_divC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib4LibA6Shadow9nshad_divC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00c59OSSVerify5KrLib5BothW9AProg_kitCablock_shadow_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ShadowGshadow_block_unpoisonedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06c59OSSVerify5KrLib5BothW9AProg_kit7hull_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit7hull_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit:hull_propsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit=hull_in_arenaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit>shad_sub_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit9shlen_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit9wr_at_subC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C46Stdlib5Lists4List2InC59OSSVerify5KrLib5BothW=AMalloc_iface5AHEAPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit5aunw5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface9AI_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_botC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_UC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface4aunwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I47Corelib4Init5Peano2le00I59OSSVerify5KrLib5BothW5ABase6uchain00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6UDEPTHC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5AUMAXC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface3aciC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:afree_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit8aunw_of5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface7AI_freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit<implMA_afreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8AFREE_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase;AFREE_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AFREE_SYMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface<AI_free_nullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface<amalloc_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface9AI_mallocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit>implMA_amallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase:AMALLOC_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase=AMALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase;AMALLOC_SYMC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revK59OSSVerify5KrLib5BothW5ABase6uchain01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z6inj_ltc59OSSVerify5KrLib5BothW9AProg_kit;uchain_dataC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib5BothW=AMalloc_iface<aclient_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:aheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7ab_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7ab_sizeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib5BothW5ABase8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9in_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7in_fakeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kitCaheap_pres_of_munchC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind02C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib4LibA6Shadow@ov_read1_of_byteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7ab_kindC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<flat_map_appC59OSSVerify5KrLib5BothW5ABase6hb_idsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6abkind00C1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC46Stdlib5Lists4List:in_app_iffC45stdpp;list_basics4list;filter_consC59OSSVerify5KrLib5BothW5ABase9lb_removeC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC35stdpp4base6decideC45stdpp;list_basics4list;list_filterC35stdpp4base6filterC47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms@subrelation_reflI47Corelib4Init6Specif7sumbool00C56Stdlib6NArith6BinNat1N8eqb_specC56Stdlib6NArith6BinNat1N3eqbI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib5BothW5ABase:abkind_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Program6Basics4implC47Corelib7Classes9MorphismsDiff_impl_subrelationC47Corelib7Classes>Morphisms_Prop@not_iff_morphismI47Corelib7Numbers7BinNums1N00C46Stdlib5Lists4List>NoDup_cons_iffC56Stdlib6NArith6BinNat1N8eqb_reflc59OSSVerify5KrLib5BothW9AProg_kit?lb_remove_notinC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit?lb_remove_headAC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C46Stdlib7Sorting;PermutationAPermutation_NoDupC46Stdlib7Sorting;PermutationDPermutation_flat_mapC59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC59OSSVerify5KrLib4LibA6Shadow7gran_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow?unpoisoned_fullC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8add_commC59OSSVerify5KrLib4LibA6Shadow>unpoisoned_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit>unpoisoned8_rdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4KENDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5KHIGHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ShadowCrw_cells_C1_of_byteC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit:c1_of_byteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit=shad_lt_KHIGHC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AProg_kit>unpoisoned8_c1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step=rw_cells_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_r".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Notation MA := (Monad.M APS).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition implMA {A} (RNG : footprint) (c : MA A) (s : APS)
    (Q : A -> APS -> footprint -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implS bsegs RNG (c s) (epostF (fun p => Q (fst p) (snd p))) ms.

Section ImplMA.

(* [comment removed for export] *)
Lemma implMA_fold : forall {A} RNG (c : MA A) s Q ms,
  implS bsegs RNG (c s) (epostF (fun p => Q (fst p) (snd p))) ms -> implMA RNG c s Q ms.
Proof. intros. exact H. Qed.
Lemma implMA_unfold : forall {A} RNG (c : MA A) s Q ms,
  implMA RNG c s Q ms -> implS bsegs RNG (c s) (epostF (fun p => Q (fst p) (snd p))) ms.
Proof. intros. exact H. Qed.

Lemma implMA_ret : forall {A} RNG (a : A) (s : APS) (Q : A -> APS -> footprint -> machine_state -> Prop) ms,
  evtF bsegs RNG (Q a s RNG) ms -> implMA RNG (mret a) s Q ms.
Proof. intros A RNG a s Q ms H. unfold implMA, mret. apply implF_ret_ok. exact H. Qed.

Lemma implMA_unr : forall {A} RNG (s : APS) (Q : A -> APS -> footprint -> machine_state -> Prop) ms,
  implMA RNG (munr (A:=A)) s Q ms.
Proof. intros. unfold implMA, munr. apply implF_ret_unr. Qed.

Lemma implMA_bind : forall {A B} RNG (ma : MA A) (f : A -> MA B) (s : APS)
    (Q1 : A -> APS -> footprint -> machine_state -> Prop) (Q : B -> APS -> footprint -> machine_state -> Prop) ms,
  implMA RNG ma s Q1 ms ->
  (forall a s' RNG' ms', Q1 a s' RNG' ms' -> implMA RNG' (f a) s' Q ms') ->
  implMA RNG (mbind ma f) s Q ms.
Proof.
  intros A B RNG ma f s Q1 Q ms Hm Hf. unfold implMA, mbind in *.
  eapply implF_ebind; [exact Hm|]. intros [a s'] RNG' ms' H. cbn in *. apply Hf. exact H.
Qed.

Lemma implMA_mono : forall {A} RNG (ma : MA A) (s : APS) (Q Q' : A -> APS -> footprint -> machine_state -> Prop) ms,
  implMA RNG ma s Q ms -> (forall a s' RNG' ms', Q a s' RNG' ms' -> Q' a s' RNG' ms') -> implMA RNG ma s Q' ms.
Proof.
  intros A RNG ma s Q Q' ms H HQ. unfold implMA in *. eapply implF_epost_mono; [exact H|]. intros [a s'] RNG' ms'; cbn; auto.
Qed.

(* [comment removed for export] *)
Lemma implMA_evtF : forall {A} RNG (ma : MA A) (s : APS) (Q : A -> APS -> footprint -> machine_state -> Prop) P ms,
  evtF bsegs RNG P ms -> (forall ms', P ms' -> implMA RNG ma s Q ms') -> implMA RNG ma s Q ms.
Proof. intros A RNG ma s Q P ms H K. unfold implMA in *. eapply implF_evtF; eauto. Qed.

Lemma implMA_from_evtF : forall {A} RNG (ma : MA A) (s : APS) (Q : A -> APS -> footprint -> machine_state -> Prop) ms,
  evtF bsegs RNG (fun ms' => implMA RNG ma s Q ms') ms -> implMA RNG ma s Q ms.
Proof. intros A RNG ma s Q ms H. eapply implMA_evtF; [exact H|]. cbv beta. intros ms' H'; exact H'. Qed.

(* [comment removed for export] *)
Lemma implMA_post_evtF : forall {A} RNG (ma : MA A) (s : APS) (Q Q' : A -> APS -> footprint -> machine_state -> Prop) ms,
  implMA RNG ma s Q' ms ->
  (forall a s' RNG' ms', Q' a s' RNG' ms' -> evtF bsegs RNG' (Q a s' RNG') ms') ->
  implMA RNG ma s Q ms.
Proof.
  intros A RNG ma s Q Q' ms H HQ. unfold implMA in *. eapply implF_epost_evtF; [exact H|]. intros [a s'] RNG' ms'; cbn; auto.
Qed.

Lemma implMA_get : forall RNG (s : APS) (Q : APS -> APS -> footprint -> machine_state -> Prop) ms,
  evtF bsegs RNG (Q s s RNG) ms -> implMA RNG mget s Q ms.
Proof. intros. unfold implMA, mget. apply implF_ret_ok. exact H. Qed.
Lemma implMA_upd : forall RNG f (s : APS) (Q : unit -> APS -> footprint -> machine_state -> Prop) ms,
  evtF bsegs RNG (Q tt (f s) RNG) ms -> implMA RNG (mupd f) s Q ms.
Proof. intros. unfold implMA, mupd. apply implF_ret_ok. exact H. Qed.

(* [comment removed for export] *)
Lemma implMA_mwhen_false : forall RNG (mu : MA unit) s Q ms,
  evtF bsegs RNG (Q tt s RNG) ms -> implMA RNG (mwhen false mu) s Q ms.
Proof. intros. unfold mwhen. apply implMA_ret. exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma implMA_alift : forall {R} RNG (t : AM R) (s : APS) (Q : R -> APS -> footprint -> machine_state -> Prop) ms,
  aps_atop s = ATOP ->
  implS bsegs RNG (aembed ATOP t) (epostF (fun r RNG' ms' => Q r s RNG' ms')) ms ->
  implMA RNG (alift t) s Q ms.
Proof.
  intros R RNG t s Q ms AT H. unfold implMA, alift. rewrite AT. eapply implF_ebind; [exact H|].
  intros r RNG' ms' HQ. apply implF_ret_ok. cbn. apply evtF_done. exact HQ.
Qed.

(* [comment removed for export] *)
Lemma implMA_amalloc : forall RNG n (s : APS) (Q : option AsanCtrl.aptr -> APS -> footprint -> machine_state -> Prop) ms,
  aps_atop s = ATOP ->
  implS bsegs RNG (aembed ATOP (AsanCtrl.amalloc ATOP (aps_resv s) (aps_m s) n))
        (epostF (fun (r : astate * option AsanCtrl.aptr) RNG' ms' => Q (snd r) (aset_m (fst r) s) RNG' ms')) ms ->
  implMA RNG (amalloc_M n) s Q ms.
Proof.
  intros RNG n s Q ms AT H. unfold amalloc_M.
  eapply (implMA_bind RNG mget _ s (fun s0 s' RNG' ms' => s0 = s /\ s' = s /\ RNG' = RNG /\ ms' = ms)).
  { apply implMA_get. apply evtF_done. repeat split; reflexivity. }
  cbv beta. intros s0 s' RNG1 ms1 (-> & -> & -> & ->).
  eapply (implMA_bind RNG (alift _) _ s (fun x s' RNG' ms' => s' = s /\ Q (snd x) (aset_m (fst x) s) RNG' ms')).
  { apply implMA_alift; [exact AT|]. rewrite AT. eapply implF_epost_mono; [exact H|]. cbv beta. intros; split; [reflexivity| assumption]. }
  cbv beta. intros x s2 RNG2 ms2 [-> H2].
  eapply (implMA_bind RNG2 (mupd _) _ s (fun _ s' RNG' ms' => s' = aset_m (fst x) s /\ RNG' = RNG2 /\ ms' = ms2)).
  { apply implMA_upd. apply evtF_done. repeat split; reflexivity. }
  cbv beta. intros [] s3 RNG3 ms3 (-> & -> & ->).
  apply implMA_ret. apply evtF_done. exact H2.
Qed.

(* [comment removed for export] *)
Lemma implMA_afree : forall RNG p (s : APS) (Q : unit -> APS -> footprint -> machine_state -> Prop) ms,
  aps_atop s = ATOP ->
  implS bsegs RNG (aembed ATOP (AsanCtrl.afree (aps_m s) (Some p)))
         (epostF (fun (st' : astate) RNG' ms' => Q tt (aset_m st' s) RNG' ms')) ms ->
  implMA RNG (afree_M p) s Q ms.
Proof.
  intros RNG p s Q ms AT H. unfold afree_M.
  eapply (implMA_bind RNG mget _ s (fun s0 s' RNG' ms' => s0 = s /\ s' = s /\ RNG' = RNG /\ ms' = ms)).
  { apply implMA_get. apply evtF_done. repeat split; reflexivity. }
  cbv beta. intros s0 s' RNG1 ms1 (-> & -> & -> & ->).
  eapply (implMA_bind RNG (alift _) _ s (fun x s' RNG' ms' => s' = s /\ Q tt (aset_m x s) RNG' ms')).
  { apply implMA_alift; [exact AT|]. eapply implF_epost_mono; [exact H|]. cbv beta. intros; split; [reflexivity| assumption]. }
  cbv beta. intros x s2 RNG2 ms2 [-> H2].
  apply implMA_upd. apply evtF_done. exact H2.
Qed.

(* [comment removed for export] *)
Lemma aps_m_aset_m : forall st s, aps_m (aset_m st s) = st.
Proof.
ltac2:(KReplay.run1 (kr_t_AProg_kit ()) ["CANSEC1"; "ImplMA"] "h01sh12stp;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001:p4p710R1p9P0p1001XR2p4p7210R3p8P0p10025p4p710R0p8p1002lp6051002R4p1003gp4p7210R5p8P4P2p4p710R2p8P4p1004Xp4p7511110R6p8P4P0p8p100I;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p100J;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p1005Np4p70R7p1006Ep4p710p8P7p1006\p4p710p8P7p1007Gp4p710p8P7p1007cp4p710p8P7p1008@p4p710p8P7p1008^p4p7210p8P7p1009;p4p710R8p8P7P4p8P7p100:7R9p4p710p8P7P9p4p7210p8P7P1p8P7p100NBp6051001R9p8P7p100ScR:p6051003R;p8P7p100:Tp4p7210R<p8P7P:p60521002R:p8P7p100;Np4p710p8P7P3p8P7p100eep60521001R3p8P7P6p8P7p100<:p4p710p8P7p100<\p4p710p8P7p100=9p4p710R=p8P7P0p8P7p100=\p4p7511110R>p8P7p100>]R?p4p710p8P7P?p4p7210p8P7p100?JR?p4p710p8P7P?p4p7210R?p8P7p100?gp4p710p8P9p100K=p4p7210p8P9P4p8P9p100L1p4p7511110R9p8p100Q3p6051001R7P4p8P7p100OAp4p7210p8P7p100P5p4p7511110p8P;P5p8P;P4p8P;p100R2R7p4p7210p8P;P2p8P;p100RgR;p4p7511110R@p8P:P5p8P:P4p8P:P7p4p73110p8P:P2p8P:P6p8P:P0p8P:P;p4p76111110R;p8p100Tcp6051002R:P5p8P:P4p8P:P2p8P:P>p8p100V^p6051002R>P5p8P>P4p8P>p100Ucp4p7511110p8p100W^p6051001R:P5p8P:P4p8P:P>p8p100Yfp6051002R>P5p8P>P4p8P>p100Xcp4p7511110p8P>P2p8P3P8p8P3P4p8P3p100^hp4p710p8P3P<p8P3P6p8P3P0p8P3P9p8P3P@p8P3P;p8p100@Cp4p7210P1p8P=P1p8P?P1p8g00kUj20Tg00oHR1g00DVf1,01W0W1o"). Qed.
Lemma aps_so_aset_m : forall st s, aps_so (aset_m st s) = aps_so s.
Proof.
ltac2:(KReplay.run1 (kr_t_AProg_kit ()) ["CANSEC1"; "ImplMA"] "h01sh12stp;1p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001:p4p710R1p9P0p1001XR2p4p7210R3p8P0p10025p4p710R0p8p1002lp6051002R4p1003gp4p7210R5p8P4P2p4p710R2p8P4p1004Xp4p7511110R6p8P4P0p8p100I;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p100J;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p1005Np4p70R7p1006Ep4p710p8P7p1006\p4p710p8P7p1007Gp4p710p8P7p1007cp4p710p8P7p1008@p4p710p8P7p1008^p4p7210p8P7p1009;p4p710R8p8P7P4p8P7p100:7R9p4p710p8P7P9p4p7210p8P7P1p8P7p100NBp6051001R9p8P7p100ScR:p6051003R;p8P7p100:Tp4p7210R<p8P7P:p60521002R:p8P7p100;Np4p710p8P7P3p8P7p100eep60521001R3p8P7P6p8P7p100<:p4p710p8P7p100<\p4p710p8P7p100=9p4p710R=p8P7P0p8P7p100=\p4p7511110R>p8P7p100>]R?p4p710p8P7P?p4p7210p8P7p100?JR?p4p710p8P7P?p4p7210R?p8P7p100?gp4p710p8P9p100K=p4p7210p8P9P4p8P9p100L1p4p7511110R9p8p100Q3p6051001R7P4p8P7p100OAp4p7210p8P7p100P5p4p7511110p8P;P5p8P;P4p8P;p100R2R7p4p7210p8P;P2p8P;p100RgR;p4p7511110R@p8P:P5p8P:P4p8P:P7p4p73110p8P:P2p8P:P6p8P:P0p8P:P;p4p76111110R;p8p100Tcp6051002R:P5p8P:P4p8P:P2p8P:P>p8p100V^p6051002R>P5p8P>P4p8P>p100Ucp4p7511110p8p100W^p6051001R:P5p8P:P4p8P:P>p8p100Yfp6051002R>P5p8P>P4p8P>p100Xcp4p7511110p8P>P2p8P3P8p8P3P4p8P3p100^hp4p710p8P3P<p8P3P6p8P3P0p8P3P9p8P3P@p8P3P;p8p100@Cp4p7210P1p8P=P1p8P?P1p8g012[j11Tg00kUj20Tg00oHg00DVg013Xf0#1'0W0W1o"). Qed.
Lemma aset_m_aset_m : forall st st' s, aset_m st (aset_m st' s) = aset_m st s.
Proof.
ltac2:(KReplay.run1 (kr_t_AProg_kit ()) ["CANSEC1"; "ImplMA"] "h01sh12sth23st'p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001:p4p710R1p9P0p1001XR2p4p7210R3p8P0p10025p4p710R0p8p1002lp6051002R4p1003gp4p7210R5p8P4P2p4p710R2p8P4p1004Xp4p7511110R6p8P4P0p8p100I;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p100J;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p1005Np4p70R7p1006Ep4p710p8P7p1006\p4p710p8P7p1007Gp4p710p8P7p1007cp4p710p8P7p1008@p4p710p8P7p1008^p4p7210p8P7p1009;p4p710R8p8P7P4p8P7p100:7R9p4p710p8P7P9p4p7210p8P7P1p8P7p100NBp6051001R9p8P7p100ScR:p6051003R;p8P7p100:Tp4p7210R<p8P7P:p60521002R:p8P7p100;Np4p710p8P7P3p8P7p100eep60521001R3p8P7P6p8P7p100<:p4p710p8P7p100<\p4p710p8P7p100=9p4p710R=p8P7P0p8P7p100=\p4p7511110R>p8P7p100>]R?p4p710p8P7P?p4p7210p8P7p100?JR?p4p710p8P7P?p4p7210R?p8P7p100?gp4p710p8P9p100K=p4p7210p8P9P4p8P9p100L1p4p7511110R9p8p100Q3p6051001R7P4p8P7p100OAp4p7210p8P7p100P5p4p7511110p8P;P5p8P;P4p8P;p100R2R7p4p7210p8P;P2p8P;p100RgR;p4p7511110R@p8P:P5p8P:P4p8P:P7p4p73110p8P:P2p8P:P6p8P:P0p8P:P;p4p76111110R;p8p100Tcp6051002R:P5p8P:P4p8P:P2p8P:P>p8p100V^p6051002R>P5p8P>P4p8P>p100Ucp4p7511110p8p100W^p6051001R:P5p8P:P4p8P:P>p8p100Yfp6051002R>P5p8P>P4p8P>p100Xcp4p7511110p8P>P2p8P3P8p8P3P4p8P3p100^hp4p710p8P3P<p8P3P6p8P3P0p8P3P9p8P3P@p8P3P;p8p100@Cp4p7210P1p8P=P1p8P?P1p8g00j=j21Tg00kUj20Tg00oHR1g00DVR?f2f0'1,0?W0X21W1o"). Qed.
Lemma aset_m_eta : forall s, aset_m (aps_m s) s = s.
Proof.
ltac2:(KReplay.run1 (kr_t_AProg_kit ()) ["CANSEC1"; "ImplMA"] "p'0h01ai001ah18aps_atopi018aps_atoph21bh31ch41si025aps_mi038aps_resvi046aps_sop;1p;2p;3p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001:p4p710R1p9P0p1001XR2p4p7210R3p8P0p10025p4p710R0p8p1002lp6051002R4p1003gp4p7210R5p8P4P2p4p710R2p8P4p1004Xp4p7511110R6p8P4P0p8p100I;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p100J;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p1005Np4p70R7p1006Ep4p710p8P7p1006\p4p710p8P7p1007Gp4p710p8P7p1007cp4p710p8P7p1008@p4p710p8P7p1008^p4p7210p8P7p1009;p4p710R8p8P7P4p8P7p100:7R9p4p710p8P7P9p4p7210p8P7P1p8P7p100NBp6051001R9p8P7p100ScR:p6051003R;p8P7p100:Tp4p7210R<p8P7P:p60521002R:p8P7p100;Np4p710p8P7P3p8P7p100eep60521001R3p8P7P6p8P7p100<:p4p710p8P7p100<\p4p710p8P7p100=9p4p710R=p8P7P0p8P7p100=\p4p7511110R>p8P7p100>]R?p4p710p8P7P?p4p7210p8P7p100?JR?p4p710p8P7P?p4p7210R?p8P7p100?gp4p710p8P9p100K=p4p7210p8P9P4p8P9p100L1p4p7511110R9p8p100Q3p6051001R7P4p8P7p100OAp4p7210p8P7p100P5p4p7511110p8P;P5p8P;P4p8P;p100R2R7p4p7210p8P;P2p8P;p100RgR;p4p7511110R@p8P:P5p8P:P4p8P:P7p4p73110p8P:P2p8P:P6p8P:P0p8P:P;p4p76111110R;p8p100Tcp6051002R:P5p8P:P4p8P:P2p8P:P>p8p100V^p6051002R>P5p8P>P4p8P>p100Ucp4p7511110p8p100W^p6051001R:P5p8P:P4p8P:P>p8p100Yfp6051002R>P5p8P>P4p8P>p100Xcp4p7511110p8P>P2p8P3P8p8P3P4p8P3p100^hp4p710p8P3P<p8P3P6p8P3P0p8P3P9p8P3P@p8P3P;p8p100@Cp4p7210P1p8P=P1p8P?P1p8g00hGj16Tg00j=j25Tg00aRj30Tg00Ahj21Tg014Sj14Tg0153j42Tg00kUj23Tg00DVR1P1f0R?#6/5?=01?P?g00oHg013Xg00eGR=/1=#4f3R;f2R3f1R@P?C2,31X1=W3W2W0P;P3P@P?O4n01100000140102104103101W4o"). Qed.

(* [comment removed for export] *)
Definition aps_rest (s : APS) := (aps_so s, aps_resv s, aps_atop s).      (* [comment removed for export] *)
Lemma aps_rest_aset_m : forall st s, aps_rest (aset_m st s) = aps_rest s.
Proof.
ltac2:(KReplay.run1 (kr_t_AProg_kit ()) ["CANSEC1"; "ImplMA"] "h01sh12stp;2p;1p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001:p4p710R1p9P0p1001XR2p4p7210R3p8P0p10025p4p710R0p8p1002lp6051002R4p1003gp4p7210R5p8P4P2p4p710R2p8P4p1004Xp4p7511110R6p8P4P0p8p100I;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p100J;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p1005Np4p70R7p1006Ep4p710p8P7p1006\p4p710p8P7p1007Gp4p710p8P7p1007cp4p710p8P7p1008@p4p710p8P7p1008^p4p7210p8P7p1009;p4p710R8p8P7P4p8P7p100:7R9p4p710p8P7P9p4p7210p8P7P1p8P7p100NBp6051001R9p8P7p100ScR:p6051003R;p8P7p100:Tp4p7210R<p8P7P:p60521002R:p8P7p100;Np4p710p8P7P3p8P7p100eep60521001R3p8P7P6p8P7p100<:p4p710p8P7p100<\p4p710p8P7p100=9p4p710R=p8P7P0p8P7p100=\p4p7511110R>p8P7p100>]R?p4p710p8P7P?p4p7210p8P7p100?JR?p4p710p8P7P?p4p7210R?p8P7p100?gp4p710p8P9p100K=p4p7210p8P9P4p8P9p100L1p4p7511110R9p8p100Q3p6051001R7P4p8P7p100OAp4p7210p8P7p100P5p4p7511110p8P;P5p8P;P4p8P;p100R2R7p4p7210p8P;P2p8P;p100RgR;p4p7511110R@p8P:P5p8P:P4p8P:P7p4p73110p8P:P2p8P:P6p8P:P0p8P:P;p4p76111110R;p8p100Tcp6051002R:P5p8P:P4p8P:P2p8P:P>p8p100V^p6051002R>P5p8P>P4p8P>p100Ucp4p7511110p8p100W^p6051001R:P5p8P:P4p8P:P>p8p100Yfp6051002R>P5p8P>P4p8P>p100Xcp4p7511110p8P>P2p8P3P8p8P3P4p8P3p100^hp4p710p8P3P<p8P3P6p8P3P0p8P3P9p8P3P@p8P3P;p8p100@Cp4p7210P1p8P=P1p8P?P1p8g00Ahj20Tg014Sj13Tg015oj12Tg00kUj21Tg00oHg00DVg013Xg00eGR1/01#3'0/01f0#2'1W0W1o"). Qed.
Lemma aps_so_of_rest : forall s' s, aps_rest s' = aps_rest s -> aps_so s' = aps_so s.
Proof. intros s' s H. exact (f_equal (fun x => fst (fst x)) H). Qed.
Lemma aps_resv_of_rest : forall s' s, aps_rest s' = aps_rest s -> aps_resv s' = aps_resv s.
Proof. intros s' s H. exact (f_equal (fun x => snd (fst x)) H). Qed.
Lemma aps_atop_of_rest : forall s' s, aps_rest s' = aps_rest s -> aps_atop s' = aps_atop s.
Proof. intros s' s H. exact (f_equal snd H). Qed.
(* [comment removed for export] *)
Definition aps_ok (L : alayout) (s : APS) : Prop := aresv_ok L (aps_resv s) /\ aps_atop s = ATOP.
Lemma aps_ok_rest : forall L s' s, aps_rest s' = aps_rest s -> aps_ok L s -> aps_ok L s'.
Proof. intros L s' s H [R A]. split; [rewrite (aps_resv_of_rest _ _ H); exact R| rewrite (aps_atop_of_rest _ _ H); exact A]. Qed.
Lemma aps_ok_resv : forall L s, aps_ok L s -> aresv_ok L (aps_resv s).
Proof.
ltac2:(KReplay.run1 (kr_t_AProg_kit ()) ["CANSEC1"; "ImplMA"] "h01Hh11Lh21Rh32_Hh41sp;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001:p4p710R1p9P0p1001XR2p4p7210R3p8P0p10025p4p710R0p8p1002lp6051002R4p1003gp4p7210R5p8P4P2p4p710R2p8P4p1004Xp4p7511110R6p8P4P0p8p100I;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p100J;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p1005Np4p70R7p1006Ep4p710p8P7p1006\p4p710p8P7p1007Gp4p710p8P7p1007cp4p710p8P7p1008@p4p710p8P7p1008^p4p7210p8P7p1009;p4p710R8p8P7P4p8P7p100:7R9p4p710p8P7P9p4p7210p8P7P1p8P7p100NBp6051001R9p8P7p100ScR:p6051003R;p8P7p100:Tp4p7210R<p8P7P:p60521002R:p8P7p100;Np4p710p8P7P3p8P7p100eep60521001R3p8P7P6p8P7p100<:p4p710p8P7p100<\p4p710p8P7p100=9p4p710R=p8P7P0p8P7p100=\p4p7511110R>p8P7p100>]R?p4p710p8P7P?p4p7210p8P7p100?JR?p4p710p8P7P?p4p7210R?p8P7p100?gp4p710p8P9p100K=p4p7210p8P9P4p8P9p100L1p4p7511110R9p8p100Q3p6051001R7P4p8P7p100OAp4p7210p8P7p100P5p4p7511110p8P;P5p8P;P4p8P;p100R2R7p4p7210p8P;P2p8P;p100RgR;p4p7511110R@p8P:P5p8P:P4p8P:P7p4p73110p8P:P2p8P:P6p8P:P0p8P:P;p4p76111110R;p8p100Tcp6051002R:P5p8P:P4p8P:P2p8P:P>p8p100V^p6051002R>P5p8P>P4p8P>p100Ucp4p7511110p8p100W^p6051001R:P5p8P:P4p8P:P>p8p100Yfp6051002R>P5p8P>P4p8P>p100Xcp4p7511110p8P>P2p8P3P8p8P3P4p8P3p100^hp4p710p8P3P<p8P3P6p8P3P0p8P3P9p8P3P@p8P3P;p8p100@Cp4p7210P1p8P=P1p8P?P1p8g016lj25Tg00gHj11Tg017gj20Tg00_]j12Tg00`\j14Tg00aRj33Tg01;2g00DVf1R1f0R?'5g00k:f2R=%11'0g00eGR;%21p,2rc#4R333f3R@%1='0P?f4R=%1@'0%2==3;3P1W3W2P1P?O2n2001000000120000000W0W4W1o"). Qed.
Lemma aps_ok_atop : forall L s, aps_ok L s -> aps_atop s = ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_AProg_kit ()) ["CANSEC1"; "ImplMA"] "h01Ah11Hh21Lh32_Hh41sp;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001:p4p710R1p9P0p1001XR2p4p7210R3p8P0p10025p4p710R0p8p1002lp6051002R4p1003gp4p7210R5p8P4P2p4p710R2p8P4p1004Xp4p7511110R6p8P4P0p8p100I;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p100J;p6051001R7P5p8P7P4p8P7P2p8P7P6p8P7P0p8p1005Np4p70R7p1006Ep4p710p8P7p1006\p4p710p8P7p1007Gp4p710p8P7p1007cp4p710p8P7p1008@p4p710p8P7p1008^p4p7210p8P7p1009;p4p710R8p8P7P4p8P7p100:7R9p4p710p8P7P9p4p7210p8P7P1p8P7p100NBp6051001R9p8P7p100ScR:p6051003R;p8P7p100:Tp4p7210R<p8P7P:p60521002R:p8P7p100;Np4p710p8P7P3p8P7p100eep60521001R3p8P7P6p8P7p100<:p4p710p8P7p100<\p4p710p8P7p100=9p4p710R=p8P7P0p8P7p100=\p4p7511110R>p8P7p100>]R?p4p710p8P7P?p4p7210p8P7p100?JR?p4p710p8P7P?p4p7210R?p8P7p100?gp4p710p8P9p100K=p4p7210p8P9P4p8P9p100L1p4p7511110R9p8p100Q3p6051001R7P4p8P7p100OAp4p7210p8P7p100P5p4p7511110p8P;P5p8P;P4p8P;p100R2R7p4p7210p8P;P2p8P;p100RgR;p4p7511110R@p8P:P5p8P:P4p8P:P7p4p73110p8P:P2p8P:P6p8P:P0p8P:P;p4p76111110R;p8p100Tcp6051002R:P5p8P:P4p8P:P2p8P:P>p8p100V^p6051002R>P5p8P>P4p8P>p100Ucp4p7511110p8p100W^p6051001R:P5p8P:P4p8P:P>p8p100Yfp6051002R>P5p8P>P4p8P>p100Xcp4p7511110p8P>P2p8P3P8p8P3P4p8P3p100^hp4p710p8P3P<p8P3P6p8P3P0p8P3P9p8P3P@p8P3P;p8p100@Cp4p7210P1p8P=P1p8P?P1p8g016lj25Tg00gHj13Tg017gj22Tg00_]j10Tg00`\j14Tg00aRj31Tg01;2g00DVf1R1f0R?'5g00k:f2R=%31'2g00eGR;%01p,2rc#4R331%0==1;3P?f4R=f3#3'2%0==1;3P?W0W3P1P?O2n2001000000120000000W1W4W2o"). Qed.
(* [comment removed for export] *)
Lemma aresv_ok_rest : forall L s' s, aps_rest s' = aps_rest s -> aresv_ok L (aps_resv s) -> aresv_ok L (aps_resv s').
Proof. intros L s' s H R. rewrite (aps_resv_of_rest _ _ H). exact R. Qed.

End ImplMA.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma munch_magreeA : forall W m m' (P : Z -> Prop),
  munch W m m' -> wmono bsegs m m' -> (forall a, P a -> outside W a) -> magree bsegs P m m'.
Proof. intros W m m' P MU WM HO. eapply magree_mono; [eapply magree_of_munch; eauto| exact HO]. Qed.



Lemma wr_at_range_splitA : forall m a n1 n2,
  0 <= n1 -> 0 <= n2 -> wr_at bsegs m a (n1 + n2) -> wr_at bsegs m a n1 /\ wr_at bsegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2 (Ha & Hb & HW). split; (split; [lia|]; split; [lia|]); intros i Hi.
  - apply HW. lia.
  - replace (a + n1 + i) with (a + (n1 + i)) by lia. apply HW. lia.
Qed.
Lemma wr_at_range_joinA : forall m a n1 n2,
  0 <= n1 -> wr_at bsegs m a n1 -> wr_at bsegs m (a + n1) n2 -> wr_at bsegs m a (n1 + n2).
Proof.
  intros m a n1 n2 H1 (Ha & Hb & HW1) (_ & Hb2 & HW2). split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Z.ltb_spec i n1); [apply HW1; lia|]. replace (a + i) with (a + n1 + (i - n1)) by lia. apply HW2. lia.
Qed.





Lemma Forall_firstnA : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof. intros A P n l H. revert n. induction H; intros [|n]; cbn; constructor; auto. Qed.
Lemma Forall_skipnA : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof. intros A P n l H. revert n. induction H; intros [|n]; cbn; try constructor; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shlenE : forall L, shlen L = L / 8.
Proof. intros. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shlen_nshad : forall n, shlen (n + 7) = nshad n.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ablock_shadow_block : forall m A n,
  ablock_shadow m A n -> A mod 8 = 0 -> 0 <= A -> 0 <= n -> A + n <= 2^64 -> shadow_block m A n.
Proof.
  intros m A n H HA A0 N0 AN. split; [exact HA|]. split; [exact A0|]. split; [exact N0|]. split; [exact AN|].
  split. { rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  split. { rewrite shad_div, nshad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  intros s Hs. unfold ablock_shadow in H.
  specialize (H (s - shad A) ltac:(lia) ltac:(rewrite nshad_div in Hs; Z.div_mod_to_equations; lia)).
  replace (shad A + (s - shad A)) with s in H by lia. rewrite H. reflexivity.
Qed.

Lemma ablock_unpoisoned : forall m A n,
  ablock_shadow m A n -> A mod 8 = 0 -> 0 <= A -> 0 <= n -> A + n <= 2^64 -> unpoisoned m A (A + n).
Proof. intros. apply shadow_block_unpoisoned. apply ablock_shadow_block; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hull_lo (A : Z) : Z := A - A mod 64 - 64.
Definition hull_hi (A n : Z) : Z := A + n + (- (A + n)) mod 64 + 64.

Lemma hull_props : forall A n, 0 <= n ->
  hull_lo A <= A /\ A + n <= hull_hi A n /\ hull_lo A mod 64 = 0 /\ hull_hi A n mod 64 = 0
  /\ A - 128 < hull_lo A /\ hull_hi A n < A + n + 128.
Proof. intros A n Hn. unfold hull_lo, hull_hi. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma hull_in_arena : forall A n RLO RHI, 0 <= n ->
  RLO mod 4096 = 0 -> RHI mod 4096 = 0 -> RLO + 64 <= A -> A + n + 64 <= RHI ->
  RLO <= hull_lo A /\ hull_hi A n <= RHI.
Proof. intros A n RLO RHI Hn R1 R2 R3 R4. unfold hull_lo, hull_hi. Z.div_mod_to_equations. lia. Qed.

Lemma shad_sub_range : forall RLO RHI lo hi,
  RLO <= lo -> lo <= hi -> hi <= RHI -> RLO mod 8 = 0 -> lo mod 8 = 0 -> hi mod 8 = 0 -> RHI mod 8 = 0 ->
  shad RLO <= shad lo /\ shad hi <= shad RHI /\ shad lo <= shad hi
  /\ shad hi - shad lo = (hi - lo) / 8 /\ shad RHI - shad RLO = (RHI - RLO) / 8.
Proof. intros. rewrite !shad_div. Z.div_mod_to_equations. lia. Qed.

Lemma shlen_div : forall L, shlen L = L / 8.
Proof. intros. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma wr_at_sub : forall m s n s' n', wr_at bsegs m s n -> s <= s' -> 0 <= n' -> s' + n' <= s + n -> wr_at bsegs m s' n'.
Proof.
  intros m s n s' n' (A & B & W) H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  replace (s' + i) with (s + (s' - s + i)) by lia. apply W. lia.
Qed.

(* [comment removed for export] *)
Lemma block_hull : forall (RNG : footprint) m A n RLO RHI,
  0 <= n -> RLO mod 4096 = 0 -> RHI mod 4096 = 0 -> RLO + 64 <= A -> A + n + 64 <= RHI -> 64 <= A ->
  rng RNG (shad RLO) (shlen (RHI - RLO)) -> wr_at bsegs m (shad RLO) (shlen (RHI - RLO)) ->
  rng RNG (shad (hull_lo A)) (shad (hull_hi A n) - shad (hull_lo A))
  /\ wr_at bsegs m (shad (hull_lo A)) (shad (hull_hi A n) - shad (hull_lo A))
  /\ hull_lo A <= A /\ A + n <= hull_hi A n /\ hull_lo A mod 64 = 0 /\ hull_hi A n mod 64 = 0 /\ 0 <= hull_lo A /\ hull_hi A n <= RHI.
Proof.
  intros RNG m A n RLO RHI Hn R1 R2 R3 R4 A64 RR WR.
  pose proof (hull_props A n Hn) as (P1 & P2 & P3 & P4 & P5 & P6).
  pose proof (hull_in_arena A n RLO RHI Hn R1 R2 R3 R4) as [Q1 Q2].
  pose proof (shad_sub_range RLO RHI (hull_lo A) (hull_hi A n) Q1 ltac:(lia) Q2
                ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia))
    as (S1 & S2 & S3 & S4 & S5).
  rewrite shlen_div in RR, WR.
  split; [| split; [| repeat split; lia]].
  - eapply rng_sub'; [exact RR| lia].
  - eapply wr_at_sub; [exact WR| lia| lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section AllocCalls.
Variable AI : AMallocIface.

(* [comment removed for export] *)
Definition aunw5 (m : amem) (L : alayout) (PC : Z) (sp s0 ra : word) (tr : list Z) : Prop :=
     (bv_unsigned sp + 16 < al_top L
      /\ uchain m (al_top L) PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr /\ (length tr <= 28)%nat
      /\ In (PC :: bv_unsigned ra :: tr) (al_U L))
  \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < al_top L /\ In [PC] (al_U L)).

Lemma aunw_of5 : forall L RNG0 st LB m RNG lo PC (sp s0 ra : word) tr,
  AHEAP AI L RNG0 st LB m ->
  aunw5 m L PC sp s0 ra tr -> rng RNG lo (al_top L - lo) -> aunw m L RNG lo PC sp s0 ra tr.
Proof.
  intros L RNG0 st LB m RNG lo PC sp s0 ra tr AH H5 HR. pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).
  destruct H5 as [(A & B & C & E)|(A & B & C)]; [left| right].
  - split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact E| exact HR].
  - split; [exact A|]. split; [lia| exact C].
Qed.

Lemma rng_below_sp : forall RNG lo L (sp : word) m, rng RNG lo (al_top L - lo) -> stk bsegs m lo (bv_unsigned sp) -> bv_unsigned sp <= al_top L ->
  rng RNG lo (bv_unsigned sp - lo).
Proof. intros RNG lo L sp m HR [_ _] TOP. eapply rng_sub'; [exact HR| lia]. Qed.

(* [comment removed for export] *)
Lemma implMA_afree_call : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z) (tr : list Z),
  AHEAP AI L RNG (aps_m s) LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw5 m L AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (al_top L - lo) ->
  aps_ok L s ->                                               (* [comment removed for export] *)
  implMA RNG (afree_M p) s
    (fun _ s' RNG' ms' => aps_rest s' = aps_rest s
       /\ afree_post (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (aps_m s) LB p lo m (aps_m s') RNG' ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. intros AH HIN MI ST BOT LOS TP A0 U5 NS8 RA4 RAPC SP16 RSTK [ROK AT].
  assert (TOPS : bv_unsigned sp < al_top L) by (destruct U5 as [(A5 & _)|(_ & A5 & _)]; lia).
  pose proof (aunw_of5 _ _ _ _ _ _ _ _ _ _ _ _ AH U5 RSTK) as UW.
  assert (RLO : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; lia]).
  apply implMA_afree; [exact AT|]. eapply implF_epost_mono; [eapply (AI_free AI); eauto|].
  cbv beta. intros st' RNG' ms' PO. split; [reflexivity| exact PO].
Qed.

(* [comment removed for export] *)
Lemma implMA_afree_null : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (tr : list Z),
  AHEAP AI L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0 ->
  aunw5 m L AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (al_top L - lo) ->
  evtF bsegs RNG (afree_null_post (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. intros AH MI ST BOT LOS TP A0 U5 NS8 RA4 RAPC SP16 RSTK.
  pose proof (aunw_of5 _ _ _ _ _ _ _ _ _ _ _ _ AH U5 RSTK) as UW.
  assert (RLO : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; destruct U5 as [(A5 & _)|(_ & A5 & _)]; lia]).
  eapply (AI_free_null AI); eauto.
Qed.

(* [comment removed for export] *)
Lemma implMA_amalloc_call : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (n lo : Z) (tr : list Z),
  AHEAP AI L RNG (aps_m s) LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw5 m L AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (al_top L - lo) ->
  aps_ok L s ->                                  (* [comment removed for export] *)
  implMA RNG (amalloc_M n) s
    (fun r s' RNG' ms' => aps_rest s' = aps_rest s
       /\ amalloc_post (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (aps_m s) LB n lo m (aps_m s', r) RNG' ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. intros AH MI ST BOT LOS TP A0 HN U5 NS8 RA4 RAPC SP16 RSTK [ROK AT].
  pose proof (aunw_of5 _ _ _ _ _ _ _ _ _ _ _ _ AH U5 RSTK) as UW.
  assert (RLO : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; destruct U5 as [(A5 & _)|(_ & A5 & _)]; lia]).
  apply implMA_amalloc; [exact AT|]. eapply implF_epost_mono; [eapply (AI_malloc AI); eauto|].
  cbv beta. intros [st' r] RNG' ms' PO. split; [reflexivity| exact PO].
Qed.

(* [comment removed for export] *)
Lemma uchain_data : forall m top pc sp fp k, fp <= sp -> uchain m top pc sp fp k [].
Proof. intros. apply uc_stop. lia. Qed.

(* [comment removed for export] *)
Lemma aunw_chain : forall m L PC (sp s0 ra : word) tr,
  bv_unsigned sp + 16 < al_top L -> uchain m (al_top L) PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr -> (length tr <= 28)%nat ->
  In (PC :: bv_unsigned ra :: tr) (al_U L) -> aunw5 m L PC sp s0 ra tr.
Proof. intros. left. auto. Qed.
Lemma aunw_data : forall m L PC (sp s0 ra : word),
  bv_unsigned sp + 16 < al_top L -> bv_unsigned s0 <= bv_unsigned sp -> In [PC; bv_unsigned ra] (al_U L) -> aunw5 m L PC sp s0 ra [].
Proof. intros. left. split; [assumption|]. split; [apply uchain_data; assumption|]. split; [cbn; lia| assumption]. Qed.


(* [comment removed for export] *)
Lemma aheap_pres_of_munch : forall CI LB SP W m m',
  munch W m m' -> wmono bsegs m m' ->
  (forall a, aclient_addr CI LB SP a -> outside W a) ->
  aheap_pres CI LB SP m m'.
Proof.
  intros CI LB SP W m m' MU WM HO a Ha Hc. split; [apply MU; rewrite wa_unsigned by lia; apply HO; exact Hc| intros Hw; apply WM; exact Hw].
Qed.

(* [comment removed for export] *)
Lemma aheap_pres_stack_writes : forall (CI : list (Z * Z)) L RNG st LB m0 W m m' SP lo,
  AHEAP AI L RNG st LB m0 ->
  (forall b, In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP) ->
  (forall iv, In iv CI -> snd iv <= AIMG_HI) ->
  munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => lo <= fst iv /\ snd iv <= SP) W -> ATOP <= lo ->
  aheap_pres CI LB SP m m'.
Proof.
  intros CI L RNG st LB m0 W m m' SP lo AH BB CIB MU WM FW CL.
  assert (OUT : forall a, a < lo \/ SP <= a -> outside W a).
  { clear MU WM. intros a HA. induction W as [|[wlo whi] W IH]; [exact I|]. cbn. inversion FW as [|x l [F1 F2] FW']; subst. cbn in F1, F2.
    split; [lia| apply IH; exact FW']. }
  eapply aheap_pres_of_munch; [exact MU| exact WM|].
  intros a Hc. apply OUT. unfold AIMG_HI in *.
  assert (HA : a < lo \/ SP <= a).
  { destruct Hc as [H|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - right; lia.
    - left. pose proof (CIB iv Hiv). lia.
    - left. pose proof (BB b Hb). lia.
    - left. rewrite shad_div. unfold ASHOFF.
      assert (A47 : a' < 2^47) by (destruct Ha' as [H|[(iv & Hiv & Hr)|(c & FA & fn & Hb & Hr)]]; [lia| pose proof (CIB iv Hiv); lia| pose proof (BB _ Hb); cbn in *; lia]).
      clear - A47 CL. Z.div_mod_to_equations. lia. }
  exact HA.
Qed.

End AllocCalls.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shadow_zero_rd : forall m s1 s2 a, shadow_bytes m s1 s2 (fun _ => 0) -> s1 <= shad a < s2 ->
  ov_read_bytes bsegs m (wa (Z.shiftr a 3 + ASHOFF)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m s1 s2 a SB Hs. replace (Z.shiftr a 3 + ASHOFF) with (shad a) by (unfold shad; lia).
  destruct SB as (A & B & H). apply ov_read1_of_byte; [lia| lia| apply H; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hb_ids_app : forall L1 L2, hb_ids (L1 ++ L2) = hb_ids L1 ++ hb_ids L2.
Proof. intros. unfold hb_ids. rewrite flat_map_app. reflexivity. Qed.

Lemma lb_remove_notin : forall p LB, ~ In p (hb_ids LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. induction LB as [|b LB IH]; intros NI; [reflexivity|].
  unfold lb_remove in *. rewrite filter_cons. unfold hb_ids in NI. cbn [flat_map] in NI. rewrite in_app_iff in NI.
  destruct (decide _) as [Y|N].
  - f_equal. apply IH. intros H; apply NI; right; exact H.
  - exfalso. apply N. destruct b as [[q|c] bA bn]; cbn [ab_kind abkind_eqb negb] in *; [| exact I].
    destruct (N.eqb_spec q p); [| exact I]. exfalso. apply NI. left. left. exact e.
Qed.

Lemma lb_remove_headA : forall p A n LB, List.NoDup (hb_ids (HB p A n :: LB)) -> lb_remove p (HB p A n :: LB) = LB.
Proof.
  intros p A n LB ND. unfold hb_ids in ND. cbn [flat_map ab_kind app] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
  unfold lb_remove. rewrite filter_cons. destruct (decide _) as [Y|N].
  - exfalso. revert Y. cbn [ab_kind abkind_eqb]. rewrite N.eqb_refl. cbn. intros Y; exact Y.
  - apply lb_remove_notin. exact NI.
Qed.

Lemma lb_remove_secondA : forall p A n b0 LB, List.NoDup (hb_ids (b0 :: HB p A n :: LB)) -> lb_remove p (b0 :: HB p A n :: LB) = b0 :: LB.
Proof.
  intros p A n b0 LB ND.
  assert (ND' : List.NoDup (hb_ids (HB p A n :: LB)) /\ ~ (exists q, ab_kind b0 = ABHeap q /\ q = p)).
  { unfold hb_ids in *. cbn [flat_map] in ND |- *. destruct b0 as [[q|c] bA bn]; cbn [ab_kind app] in *.
    - apply NoDup_cons_iff in ND. destruct ND as [NI ND]. split; [exact ND|]. intros (q' & E & ->). inversion E; subst. apply NI. left. reflexivity.
    - split; [exact ND|]. intros (q' & E & _). discriminate. }
  destruct ND' as [ND1 NB0].
  unfold lb_remove. rewrite filter_cons. destruct (decide _) as [Y|N].
  - f_equal. apply lb_remove_headA. exact ND1.
  - exfalso. apply N. destruct b0 as [[q|c] bA bn]; cbn [ab_kind abkind_eqb negb] in *; [| exact I].
    destruct (N.eqb_spec q p); [| exact I]. exfalso. apply NB0. exists q. auto.
Qed.

Lemma NoDup_hb_ids_perm : forall L1 L2, Permutation L1 L2 -> List.NoDup (hb_ids L1) -> List.NoDup (hb_ids L2).
Proof.
  intros L1 L2 P ND. eapply Permutation_NoDup; [| exact ND]. unfold hb_ids. apply Permutation_flat_map. exact P.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma unpoisoned8_rd : forall m P, unpoisoned m P (P + 8) -> P mod 8 = 0 ->
  ov_read_bytes bsegs m (wa (Z.shiftr P 3 + ASHOFF)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m P U P8. pose proof U as (A & B & _).
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.add_comm.
  apply ov_read1_of_byte; [unfold ASHOFF; Z.div_mod_to_equations; lia| unfold ASHOFF; Z.div_mod_to_equations; lia|].
  apply (unpoisoned_full m P (P + 8) (P / 8) U); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma unpoisoned8_rd_off : forall m lo hi P k, unpoisoned m lo hi -> lo <= P + k -> P + k + 8 <= hi -> (P + k) mod 8 = 0 ->
  ov_read_bytes bsegs m (wa (Z.shiftr (P + k) 3 + ASHOFF)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m lo hi P k U H1 H2 H8. apply unpoisoned8_rd; [| exact H8]. eapply unpoisoned_sub; [exact U| lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shad_lt_KHIGH : forall a, 0 <= a -> a < KEND -> Z.shiftr a 3 + ASHOFF + 1 <= KHIGH.
Proof. intros a A0 AK. rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF, KHIGH, KEND in *. Z.div_mod_to_equations. lia. Qed.

Lemma c1_of_byte : forall m s b, 0 <= s -> s + 1 <= 2^64 -> m (wa s) = Some b -> rw_cells bsegs m s [C1 b].
Proof. intros. apply rw_cells_C1_of_byte; assumption. Qed.

Lemma unpoisoned8_c1 : forall m P, unpoisoned m P (P + 8) -> P mod 8 = 0 -> P + 8 <= KEND ->
  rw_cells bsegs m (Z.shiftr P 3 + ASHOFF) [C1 (Z_to_bv 8 0)] /\ Z.shiftr P 3 + ASHOFF + 1 <= KHIGH.
Proof.
  intros m P U P8 PK. pose proof U as (A & B & _). split; [| apply shad_lt_KHIGH; unfold KEND in *; lia].
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  apply c1_of_byte; [unfold ASHOFF; Z.div_mod_to_equations; lia| unfold ASHOFF; Z.div_mod_to_equations; lia|].
  rewrite Z.add_comm. apply (unpoisoned_full m P (P + 8) (P / 8) U); Z.div_mod_to_equations; lia.
Qed.

Lemma unpoisoned8_c1_off : forall m lo hi P k, unpoisoned m lo hi -> lo <= P + k -> P + k + 8 <= hi -> (P + k) mod 8 = 0 -> hi <= KEND ->
  rw_cells bsegs m (Z.shiftr (P + k) 3 + ASHOFF) [C1 (Z_to_bv 8 0)] /\ Z.shiftr (P + k) 3 + ASHOFF + 1 <= KHIGH.
Proof.
  intros m lo hi P k U H1 H2 H8 HK. apply unpoisoned8_c1; [| exact H8| lia]. eapply unpoisoned_sub; [exact U| lia| lia].
Qed.


(* [comment removed for export] *)
Lemma c1_rd : forall m s b, rw_cells bsegs m s [C1 b] -> ov_read_bytes bsegs m (wa s) 1 = Some [b].
Proof. intros m s b H. pose proof (rw_cells_read bsegs m s [C1 b] 0 (C1 b) H eq_refl) as RD. rewrite Z.add_0_r in RD. exact RD. Qed.
End CANSEC1.
