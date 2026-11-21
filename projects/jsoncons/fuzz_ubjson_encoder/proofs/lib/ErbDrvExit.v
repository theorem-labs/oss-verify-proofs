(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the channel-reader premise of writev; addresses and numbers; taken in part from projects/jsoncons/fuzz_ubjson_encoder/proofs/lib/S9/ErbDrvExit.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, 832 lines within its lines 30-1068. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 DrvKitA DrvNodesLazyK As0DrvKitA Eb0DrvEntry Eb0Drv_defs Eb0DrvLib Eb0DrvRead Eb0DrvPiece Eb0DiagLoopK Eb0DrvStdio ErbDrvPrintfK ErbDrvPrintf1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require L5Defs L5KnA L5Core ArtMem EbrFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0DrvP_dpX Eb0DrvP_dpX2_pre Eb0DrvP_dpX3_pre Eb0DrvP_dpX4_pre Eb0DrvP_dpXd_2 Eb0DrvP_dpXd_3 Eb0DrvP_dpXd_4 Eb0DrvP_dpXe
  Eb0ExitCells.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ErbDrvExit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit8cells_atC13~~~C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6to_natC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List<nth_error_InC47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images9AsanUbsan1M?loaded_segmentsC13~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01C46Stdlib6ZArith4Zdiv9Zplus_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SeqExec7rdn_appC13~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9SymDriveX6ECALLWC13~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA5lzinvC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>H_off_segmentsC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct:lazy_coverC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4A_wfC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4MInv00C13~~~K47Corelib4Init9Datatypes6option02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct9mrestrictC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctEsame_but_materializedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct6hcleanC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct;munrestrictC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitAEmrestrict_munrestrictC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanAcctShapeGsrz_msteps_restricted_TC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I47Corelib4Init9Datatypes4bool00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0Drv_defs8asegs_wxC13~~~K47Corelib4Init9Datatypes4bool01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Eb0DrvLib4dinv00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Eb0DrvLib6di_invC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6vml_ofC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6ri_invC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<HeapIfaceAEx<aiob_staticsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA:asc_got_loC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA:asc_got_hiC13~~~C56Stdlib6ZArith6BinInt1Z2ltC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7hl_segsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7cell_isC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9asc_cellsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA4ahidC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Eb0DrvLib8dla_segsC13~~~C47Corelib4Init5Peano2ltC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0DrvStdio7vis_lowC13~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AgentLib7u64_litC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4woffC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct<range_avoidsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct@rdn_mrestrict_eqC13~~~I47Corelib4Init5Logic2or00C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz06I47Corelib4Init5Logic5False00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6fframeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0DrvStdio8EX_CELLSC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega:ZMicromega;ZArithProof01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ExitCells=atexit_cellsAC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ExitCells7ax_cellC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ExitCells8AX_CELLSC13~~~C47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsDiff_impl_subrelationC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ExitCells;ax_cells_inC13~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ExitCells3axv00C13~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ExitCells4AXLOC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ExitCells4AXHIC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ExitCells4SSLOC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ExitCells4SSHIC13~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic2or01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB0Baic_shadow_definedC13~~~C47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct=page_allowedbC13~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool>negb_false_iffC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB0;aic_globalsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA:shadow_blkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA>shadow_allowedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB0;icl_globalsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB0<aicl_globalsC13~~~C46Stdlib5Lists4List:Forall_invC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr04C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA<in_shadow_ofC13~~~C56Stdlib6ZArith6BinInt1Z3mulC35stdpp7tactics<f_equal_helpC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9hl_img_loC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Eb0DrvLib:dla_img_loC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9hl_img_hiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Eb0DrvLib:dla_img_hiC13~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB0:icl_poisonC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB0;aicl_poisonC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB0>aic_img_shadowC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7byte_atC13~~~C46Stdlib4Bool4BoolAandb_false_intro2C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57definedC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5CCwritable_of_definedC13~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C47Corelib7Classes>Morphisms_Prop?or_iff_morphismC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC47Corelib7Classes?RelationClasses=iff_ReflexiveC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB08LOWSH_LOC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB08LOWSH_HIC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB09HIGHSH_LOC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB09HIGHSH_HIC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9StreamSim7wseg_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk?store_ok_windowC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L58writableC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit8exit_preC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=ErbDrvPrintfK7stdoutAC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=ErbDrvPrintf18stdoutXAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit5exitAC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan;Eb0DrvP_dpX;AS0DRVP_dpX7alignedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Eb0DrvLib@store_ok_definedC13~~~C47Corelib4Init9Datatypes9andb_propc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit<wsg_writableC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit;sh_writableC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit;ex_cell_visC13~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6ArtMem:art_bytes1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit<cells_at_nthC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0DrvStdio8img_cellC13~~~C47Corelib4Init5Logic8f_equal2C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan;Eb0DrvP_dpX;AS0DRVP_dpX8dpX_concC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk9mem_growsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~I47Corelib4Init5Logic2ex00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Eb0DrvLib:dinv_lzinvC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA=sbm_halted_eqC13~~~K47Corelib4Init5Logic2or02C47Corelib4Init5Logic8eq_transC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=DrvNodesLazyKArz_exit_at_lit_lzC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Eb0DrvLib7sbm_fdsC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit=msteps_vis_fxC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_exitC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56u64_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56u32_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L55u8_atC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit8XC_CELLSC13~~~K47Corelib4Init5Logic4True01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=ErbDrvPrintfK5SOBUFC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan;Eb0DrvP_dpX;AS0DRVP_dpX6KS_dpXC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit;fetch_exitAC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9SymDriveX?is_ecall_ECALLWC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit9exit_preEC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit8stdoutPAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit5exitEC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan<Eb0DrvP_dpXe<AS0DRVP_dpXe7alignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan<Eb0DrvP_dpXe<AS0DRVP_dpXe9dpXe_concC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit:XC_CELLS_EC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan<Eb0DrvP_dpXe<AS0DRVP_dpXe7KS_dpXeC13~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec:zero_linesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec1WC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan@Eb0DrvP_dpX2_pre@AS0DRVP_dpX2_pre7alignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan@Eb0DrvP_dpX2_pre@AS0DRVP_dpX2_pre=dpX2_pre_concC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0DrvStdio6rdn_trC13~~~C47Corelib4Init3Nat3mulC47Corelib4Init3Nat3addc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:ErbDrvExit9rdn_cons1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=ErbDrvPrintf15nl_ptC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk=store_ok_monoC13~~~C47Corelib4Init9Datatypes3appK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C47Corelib5Lists7ListDef3mapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ShapeLaws>t_exit_has_nilC13~~~I47Corelib4Init5Peano2le00C47Corelib4Init9Datatypes6lengthC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA;sbm_lazy_eqC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DiagLoopK8sbm_fds'C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DiagLoopK7wv_regsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DiagLoopK6wv_iovC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DiagLoopK6wv_bufC13~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan>Eb0DrvP_dpXd_2>AS0DRVP_dpXd_27alignedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9u64_rangeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan>Eb0DrvP_dpXd_2>AS0DRVP_dpXd_2;dpXd_2_concC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctKsame_but_materialized_transC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA9lzinv_sbmC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DiagLoopK7wv_doneC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DiagLoopK7wv_loopC13~~~C46Stdlib5Lists4List9app_nil_rC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_emitC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK46Stdlib;setoid_ring<Ring_polynom5PExpr03C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan@Eb0DrvP_dpX2_pre@AS0DRVP_dpX2_pre;KS_dpX2_preC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I46Stdlib;setoid_ring<Ring_polynom3Mon00I47Corelib7Numbers7BinNums8positive00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DiagLoopK7WV_KEEPC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan>Eb0DrvP_dpXd_2>AS0DRVP_dpXd_29KS_dpXd_2C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan@Eb0DrvP_dpX3_pre@AS0DRVP_dpX3_pre7alignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan@Eb0DrvP_dpX3_pre@AS0DRVP_dpX3_pre=dpX3_pre_concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan>Eb0DrvP_dpXd_3>AS0DRVP_dpXd_37alignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan>Eb0DrvP_dpXd_3>AS0DRVP_dpXd_3;dpXd_3_concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan@Eb0DrvP_dpX3_pre@AS0DRVP_dpX3_pre;KS_dpX3_preC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan>Eb0DrvP_dpXd_3>AS0DRVP_dpXd_39KS_dpXd_3C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan@Eb0DrvP_dpX4_pre@AS0DRVP_dpX4_pre7alignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan@Eb0DrvP_dpX4_pre@AS0DRVP_dpX4_pre=dpX4_pre_concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan>Eb0DrvP_dpXd_4>AS0DRVP_dpXd_47alignedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan>Eb0DrvP_dpXd_4>AS0DRVP_dpXd_4;dpXd_4_concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan@Eb0DrvP_dpX4_pre@AS0DRVP_dpX4_pre;KS_dpX4_preC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan>Eb0DrvP_dpXd_4>AS0DRVP_dpXd_49KS_dpXd_4C13~~~". Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XC_CELLS : list (Z * Z * Z) :=
  [(6923248, 4, 0); (6923283, 1, 0); (6922720, 8, 6922728); (6922712, 4, 2); (6922736, 8, 1174352); (6922992, 8, 624400); (6922708, 4, 0); (6922728, 8, 0); (6924680, 8, 0); (1319832, 8, 1319600); (1319740, 4, 4294967295); (1319640, 8, 0); (1319656, 8, 0); (1319608, 8, 0); (1319616, 8, 0); (1319592, 8, 1319360); (1319352, 8, 1319120); (1319260, 4, 4294967295); (1319160, 8, 0); (1319176, 8, 0); (1319128, 8, 0); (1319136, 8, 0); (6922744, 8, 1174352); (6923000, 8, 692440); (6784852, 1, 0)].
(* [comment removed for export] *)
Definition XC_CELLS_E : list (Z * Z * Z) :=
  [(6923248, 4, 0); (6923283, 1, 0); (6922720, 8, 6922728); (6922712, 4, 1); (6922736, 8, 1174352); (6922992, 8, 624400); (6922708, 4, 0); (6922728, 8, 0); (6924680, 8, 0); (1319832, 8, 1319600); (1319740, 4, 4294967295); (1319640, 8, 0); (1319656, 8, 0); (1319608, 8, 0); (1319616, 8, 0); (1319592, 8, 1319360); (1319352, 8, 1319120); (1319260, 4, 4294967295); (1319160, 8, 0); (1319176, 8, 0); (1319128, 8, 0); (1319136, 8, 0)].

Definition cells_at (MV : word -> option byte) (l : list (Z * Z * Z)) : Prop :=
  Forall (fun c => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (Z.to_nat (snd (fst c))) = Some (word_to_le_bytes (Z.to_nat (snd (fst c))) (Z_to_bv 64 (snd c)))) l.
Lemma cells_at_nth : forall MV l (i : nat) a n v, cells_at MV l -> nth_error l i = Some (a, n, v) ->
  rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
Proof. intros MV l i a n v HC Hn. exact (proj1 (Forall_forall _ _) HC (a, n, v) (nth_error_In _ _ Hn)). Qed.

(* [comment removed for export] *)
Definition exitA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6791384) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x1423d0 <= i < 0x142a10 -> MV (Z_to_bv 64 i) = None).

Definition exitE (tid : Z) (MV : word -> option byte) : Prop :=   (* [comment removed for export] *)
  cells_at MV XC_CELLS_E
  /\ rdn ASEGS MV (Z_to_bv 64 6791384) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x1423d0 <= i < 0x142a10 -> MV (Z_to_bv 64 i) = None).


Lemma rdn_cons1 : forall (MV : word -> option byte) a b (n : nat) bs, 0 <= a ->
  rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [b] -> rdn ASEGS MV (Z_to_bv 64 (a + 1)) n = Some bs -> rdn ASEGS MV (Z_to_bv 64 a) (Datatypes.S n) = Some (b :: bs).
Proof.
  intros MV a b n bs Ha H1 H2. change (Datatypes.S n) with (1 + n)%nat. change (b :: bs) with ([b] ++ bs). apply (SeqExec.rdn_app ASEGS MV 1%nat n _ _ _ H1).
  replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1)); [exact H2|].
  apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Ltac img_rd := vm_compute; apply f_equal; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity.

Lemma fetch_exitA : fetch_word ASEGS (Z_to_bv 64 0x11e8b4) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma msteps_vis_fx : forall (scfg : SpuriousCfg) (H : word -> bool) (A : list (Z * Z)) (fx fx' : PropExec.FPState) R (pc : word) M R' (pc' : word) MV' (model : Model) T,
  lzinv ASEGS H A model ->
  msteps ASEGS (@mkst fx R pc (mrestrict H M) (seg_rom ASEGS)) (@mkst fx' R' pc' MV' (seg_rom ASEGS)) ->
  (forall M' (model' : Model), MInv A model' -> same_but_materialized model model' -> mrestrict H M' = MV' ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R' pc' M' (seg_rom ASEGS)) model') T) ->
  srealizes ASEGS scfg (mkCfg (@mkst fx R pc M (seg_rom ASEGS)) model) T.
Proof.
  intros scfg H A fx fx' R pc M R' pc' MV' model T (HH & HL & HA & HM & Hh) MS KONT.
  apply (srz_msteps_restricted_T ASEGS scfg H HH asegs_wx A (@mkst fx R pc M (seg_rom ASEGS)) (@mkst fx' R' pc' MV' (seg_rom ASEGS)) model T HL HA HM Hh MS).
  intros model1 MI1 SBM HC.
  change (unrestrict H (ms_mem (@mkst fx R pc M (seg_rom ASEGS))) (@mkst fx' R' pc' MV' (seg_rom ASEGS))) with (@mkst fx' R' pc' (munrestrict H M MV') (seg_rom ASEGS)).
  apply (KONT _ model1 MI1 SBM). apply As0DrvKitA.mrestrict_munrestrict. intros a Ha. exact (HC a Ha).
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Exit.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hex : incl EX_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation rom := (seg_rom ASEGS).

  (* [comment removed for export] *)
  #[using="scfg L C IL HIok Hsp DL Hex"] Lemma ex_cell_vis : forall LB LK cr A M (model : Model) a n v, dinvA LB LK cr A M model -> In (a, n, v) EX_CELLS ->
    rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
Proof.
    intros LB LK cr A M model a n v D Hin. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    destruct (aiob_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
    pose proof (proj1 (Forall_forall _ _) CS (a, n, v) (Hex _ Hin)) as X. unfold cell_is in X. cbn [fst snd] in X.
    rewrite rdn_mrestrict_eq; [exact X|].
    intros k Hk. unfold woff.
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x69c000).
    { unfold EX_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
    rewrite (u64_lit a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.
  #[using="scfg L C IL HIok Hsp DL"] Lemma ax_cells_vis : forall LB LK cr A M (model : Model) (ax : axv), dinvA LB LK cr A M model -> atexit_cellsA M ax ->
    atexit_cellsA (mrestrict (ahid A model) M) ax.
Proof.
    intros LB LK cr A M model ax D H. unfold atexit_cellsA in *. rewrite Forall_forall in *. intros c Hc.
    pose proof (ax_cells_in ax c Hc) as (BB & B3). specialize (H c Hc). unfold ax_cell in *.
    rewrite rdn_mrestrict_eq; [exact H|].
    intros k Hk. unfold woff. unfold AXLO, AXHI, SSLO, SSHI in *.
    rewrite (u64_lit (fst (fst c))) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="scfg L IL ICok ILY Hsp DL"] Lemma sh_writable : forall LB LK cr A M (model : Model) a n, dinvA LB LK cr A M model ->
    ((2147468892 <=? a) && (a + n <=? 2147469204) || (2147615866 <=? a) && (a + n <=? 2147616066)) = true ->
    L5Defs.L5.writable ASEGS (mrestrict (ahid A model) M) a n.
Proof.
    intros LB LK cr A M model a n D Hb. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    apply L5Core.L5C.writable_of_defined; [|rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb; lia | rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb; lia].
    intros i Hi. set (x := a + i).
    assert (Hx : 2147468892 <= x < 2147469204 \/ 2147615866 <= x < 2147616066) by (unfold x; rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb; lia).
    assert (DEF : M (Z_to_bv 64 x) <> None).
    { apply (aic_shadow_defined _ _ _ _ _ ICok _ _ _ _ _ _ _ HH x). left. unfold LOWSH_LO, LOWSH_HI. lia. }
    assert (VIS : ahid A model (Z_to_bv 64 x) = false).
    { unfold ahid, mkH. apply andb_false_intro2. apply negb_false_iff.
      pose proof (aic_globals _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) as G. rewrite (aicl_globals IL ILY) in G.
      destruct Hx as [Hx|Hx].
      - pose proof (proj2 (Forall_inv G)) as SA. cbn [fst snd] in SA.
        specialize (SA 2147468892 ltac:(unfold in_shadow_of, S, SB; cbn; lia)).
        replace (page_base (Z_to_bv 64 x)) with (page_base (Z_to_bv 64 2147468892)); [exact SA|].
        unfold page_base, page_base_of. rewrite !u64_lit by lia. f_equal. unfold page_size.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      - destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH 0x142a10 16) as (_ & SA);
          [rewrite (dla_img_lo _ _ _ _ DL); lia | rewrite (dla_img_hi _ _ _ _ DL); lia | lia
          | rewrite (aicl_poison IL ILY); repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil |].
        specialize (SA 2147616066 ltac:(unfold in_shadow_of, S, SB; cbn; lia)).
        replace (page_base (Z_to_bv 64 x)) with (page_base (Z_to_bv 64 2147616066)); [exact SA|].
        unfold page_base, page_base_of. rewrite !u64_lit by lia. f_equal. unfold page_size. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    unfold mrestrict. rewrite VIS. exact DEF.
  Qed.

  (* [comment removed for export] *)
  #[using="sp0 Hsp M0"] Lemma wsg_writable : forall (MV : word -> option byte) a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> 0 <= a -> a + Z.of_nat n <= 2 ^ 63 ->
    L5Defs.L5.writable ASEGS MV a (Z.of_nat n).
Proof.
    intros MV a n W Ha Hn d k Hd Hk.
    apply (store_ok_window ASEGS MV (Z_to_bv 64 a) (Z_to_bv 64 (a + d)) n k a (a + Z.of_nat n)); first [exact W | reflexivity | lia | rewrite u64_lit by lia; lia].
  Qed.

  (* [comment removed for export] *)
  Definition exit_pre (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1306624 -> MV (Z_to_bv 64 i) = None)
    /\ exitA tid MV.
  Definition exit_preE (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1306624 -> MV (Z_to_bv 64 i) = None)
    /\ exitE tid MV.

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_0 : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1172448 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6791552 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x11eba4) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
Proof.
    intros LB LK cr A M model R S st tid (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G1 G2 G4 G10 SO SOX.
    pose proof Hsp as Hsp'. destruct SO as (_ & _ & _ & SOwpos & SOwbase & SOlock & _). destruct SOX as (_ & _ & _ & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468892 <=? a) && (a + n <=? 2147469204) || (2147615866 <=? a) && (a + n <=? 2147616066)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x1423d0 <=? a) && (a + Z.of_nat n <=? 0x142a10) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpX.dpX_conc fx R MV V HS64 HT64
           G1 G2 G4 HSr HSa CWR
           CDF IMGc (WSG 1321536 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1321616 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1325488 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6922704 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6922712 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6922720 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6923248 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468892 1 eq_refl) (SHW 2147468893 1 eq_refl) (SHW 2147468894 1 eq_refl)
           (SHW 2147468895 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl)
           (SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl)
           (SHW 2147468935 1 eq_refl) (SHW 2147468936 1 eq_refl) (SHW 2147468937 1 eq_refl) (SHW 2147468938 1 eq_refl) (SHW 2147468939 1 eq_refl) (SHW 2147468940 1 eq_refl)
           (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl) (SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468948 1 eq_refl)
           (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl) (SHW 2147468952 1 eq_refl) (SHW 2147468952 4 eq_refl)
           (SHW 2147468953 1 eq_refl) (SHW 2147468954 1 eq_refl) (SHW 2147468955 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468964 1 eq_refl)
           (SHW 2147468964 4 eq_refl) (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468968 4 eq_refl)
           (SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468976 4 eq_refl) (SHW 2147468980 1 eq_refl)
           (SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 1 eq_refl) (SHW 2147468985 1 eq_refl)
           (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl)
           (SHW 2147468991 1 eq_refl) (SHW 2147468992 4 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl)
           (SHW 2147468999 1 eq_refl) (SHW 2147469000 1 eq_refl) (SHW 2147469000 4 eq_refl) (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl)
           (SHW 2147469004 4 eq_refl) (SHW 2147469008 4 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469013 1 eq_refl) (SHW 2147469014 1 eq_refl)
           (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl) (SHW 2147469019 1 eq_refl)
           (SHW 2147469020 4 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl)
           (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl)
           (SHW 2147469036 4 eq_refl) (SHW 2147469040 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469041 1 eq_refl) (SHW 2147469042 1 eq_refl) (SHW 2147469043 1 eq_refl)
           (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl) (SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl) (SHW 2147469048 4 eq_refl)
           (SHW 2147469052 1 eq_refl) (SHW 2147469052 4 eq_refl) (SHW 2147469053 1 eq_refl) (SHW 2147469054 1 eq_refl) (SHW 2147469055 1 eq_refl) (SHW 2147469056 1 eq_refl)
           (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl) (SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469064 1 eq_refl)
           (SHW 2147469064 4 eq_refl) (SHW 2147469065 1 eq_refl) (SHW 2147469066 1 eq_refl) (SHW 2147469067 1 eq_refl) (SHW 2147469068 1 eq_refl) (SHW 2147469068 4 eq_refl)
           (SHW 2147469069 1 eq_refl) (SHW 2147469070 1 eq_refl) (SHW 2147469071 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469080 1 eq_refl)
           (SHW 2147469080 4 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl)
           (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl)
           (SHW 2147469092 1 eq_refl) (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147469104 1 eq_refl) (SHW 2147469105 1 eq_refl)
           (SHW 2147469106 1 eq_refl) (SHW 2147469107 1 eq_refl) (SHW 2147469108 1 eq_refl) (SHW 2147469109 1 eq_refl) (SHW 2147469110 1 eq_refl) (SHW 2147469111 1 eq_refl)
           (SHW 2147469112 1 eq_refl) (SHW 2147469113 1 eq_refl) (SHW 2147469114 1 eq_refl) (SHW 2147469115 1 eq_refl) (SHW 2147469116 1 eq_refl) (SHW 2147469117 1 eq_refl)
           (SHW 2147469118 1 eq_refl) (SHW 2147469119 1 eq_refl) (SHW 2147469120 1 eq_refl) (SHW 2147469121 1 eq_refl) (SHW 2147469122 1 eq_refl) (SHW 2147469123 1 eq_refl)
           (SHW 2147469124 1 eq_refl) (SHW 2147469124 4 eq_refl) (SHW 2147469125 1 eq_refl) (SHW 2147469126 1 eq_refl) (SHW 2147469127 1 eq_refl) (SHW 2147469128 4 eq_refl)
           (SHW 2147469132 1 eq_refl) (SHW 2147469132 4 eq_refl) (SHW 2147469133 1 eq_refl) (SHW 2147469134 1 eq_refl) (SHW 2147469135 1 eq_refl) (SHW 2147469180 1 eq_refl)
           (SHW 2147469180 4 eq_refl) (SHW 2147469181 1 eq_refl) (SHW 2147469182 1 eq_refl) (SHW 2147469183 1 eq_refl) (SHW 2147469184 4 eq_refl) (SHW 2147469188 1 eq_refl)
           (SHW 2147469188 4 eq_refl) (SHW 2147469189 1 eq_refl) (SHW 2147469190 1 eq_refl) (SHW 2147469191 1 eq_refl) (SHW 2147469192 1 eq_refl) (SHW 2147469192 4 eq_refl)
           (SHW 2147469193 1 eq_refl) (SHW 2147469194 1 eq_refl) (SHW 2147469195 1 eq_refl) (SHW 2147469196 4 eq_refl) (SHW 2147469200 1 eq_refl) (SHW 2147469200 4 eq_refl)
           (SHW 2147469201 1 eq_refl) (SHW 2147469202 1 eq_refl) (SHW 2147469203 1 eq_refl) (SHW 2147615866 1 eq_refl) (SHW 2147615866 4 eq_refl) (SHW 2147615867 1 eq_refl)
           (SHW 2147615868 1 eq_refl) (SHW 2147615869 1 eq_refl) (SHW 2147615870 4 eq_refl) (SHW 2147615874 4 eq_refl) (SHW 2147615878 4 eq_refl) (SHW 2147615882 4 eq_refl)
           (SHW 2147615886 4 eq_refl) (SHW 2147615890 4 eq_refl) (SHW 2147615890 8 eq_refl) (SHW 2147615898 8 eq_refl) (SHW 2147615906 8 eq_refl) (SHW 2147615914 8 eq_refl)
           (SHW 2147615922 8 eq_refl) (SHW 2147615930 8 eq_refl) (SHW 2147615938 8 eq_refl) (SHW 2147615946 8 eq_refl) (SHW 2147615954 8 eq_refl) (SHW 2147615962 8 eq_refl)
           (SHW 2147615970 8 eq_refl) (SHW 2147615978 8 eq_refl) (SHW 2147615986 8 eq_refl) (SHW 2147615994 8 eq_refl) (SHW 2147616002 8 eq_refl) (SHW 2147616010 8 eq_refl)
           (SHW 2147616018 8 eq_refl) (SHW 2147616026 8 eq_refl) (SHW 2147616034 8 eq_refl) (SHW 2147616038 4 eq_refl) (SHW 2147616042 4 eq_refl) (SHW 2147616042 8 eq_refl)
           (SHW 2147616046 4 eq_refl) (SHW 2147616050 4 eq_refl) (SHW 2147616054 4 eq_refl) (SHW 2147616058 4 eq_refl) (SHW 2147616062 1 eq_refl) (SHW 2147616062 4 eq_refl)
           (SHW 2147616063 1 eq_refl) (SHW 2147616064 1 eq_refl) (SHW 2147616065 1 eq_refl) TIDC HTr (XCC 0%nat 6923248 4 0 eq_refl)
           (XCC1 1%nat 6923283 0 eq_refl eq_refl) (XCC 2%nat 6922720 8 6922728 eq_refl) (XCC 3%nat 6922712 4 2 eq_refl) (XCC 22%nat 6922744 8 1174352 eq_refl) (XCC 23%nat 6923000 8 692440 eq_refl) (XCC 6%nat 6922708 4 0 eq_refl)
           (XCC1 24%nat 6784852 0 eq_refl eq_refl) (XCC 4%nat 6922736 8 1174352 eq_refl) (XCC 5%nat 6922992 8 624400 eq_refl) (STC1 10%nat 1933216 0 eq_refl eq_refl) (XCC 7%nat 6922728 8 0 eq_refl) (STC1 3%nat 1321616 0 eq_refl eq_refl)
           (STC 0%nat 1308376 8 1308376 eq_refl) (STC 2%nat 1321536 8 1 eq_refl) (STC 4%nat 1325328 4 1 eq_refl) (STC 5%nat 1325488 8 0 eq_refl) (STC1 8%nat 1338840 1 eq_refl eq_refl) (STC 7%nat 1335544 8 2147450880 eq_refl)
           (DSC 1319888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144096)) ltac:(img_rd) eq_refl) (DSC 1319904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1333596 1 eq_refl eq_refl) (DSC 1319904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1932448 8 18446744073709551615 eq_refl) (STC 1%nat 1308888 8 1245236 eq_refl)
           (DSC 1319944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1319952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144352)) ltac:(img_rd) eq_refl) (DSC 1319968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1319968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl)
           (DSC 1320032 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1320032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1320072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144448)) ltac:(img_rd) eq_refl) (DSC 1320096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1320136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144480)) ltac:(img_rd) eq_refl) (DSC 1320160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144576)) ltac:(img_rd) eq_refl)
           (DSC 1320224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl) (DSC 1320288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
           (DSC 1320328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144832)) ltac:(img_rd) eq_refl) (DSC 1320352 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144864)) ltac:(img_rd) eq_refl)
           (DSC 1320416 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144960)) ltac:(img_rd) eq_refl) (DSC 1320480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
           (DSC 1320520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145088)) ltac:(img_rd) eq_refl) (DSC 1320544 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145216)) ltac:(img_rd) eq_refl)
           (DSC 1320608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145312)) ltac:(img_rd) eq_refl) (DSC 1320672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1320712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145408)) ltac:(img_rd) eq_refl) (DSC 1320736 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145504)) ltac:(img_rd) eq_refl)
           (DSC 1320800 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1320864 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1320864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1320904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145696)) ltac:(img_rd) eq_refl) (DSC 1320928 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145792)) ltac:(img_rd) eq_refl)
           (DSC 1320992 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145824)) ltac:(img_rd) eq_refl) (DSC 1321056 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1321096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145856)) ltac:(img_rd) eq_refl) (DSC 1321120 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145888)) ltac:(img_rd) eq_refl)
           (DSC 1321184 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145920)) ltac:(img_rd) eq_refl) (DSC 1321248 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1321288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145952)) ltac:(img_rd) eq_refl) (DSC 1321312 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146400)) ltac:(img_rd) eq_refl)
           (DSC 1321376 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl) (DSC 1321440 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1321480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6924680 8 0 eq_refl) (XCC 9%nat 1319832 8 1319600 eq_refl) (XCC 10%nat 1319740 4 4294967295 eq_refl) (XCC 11%nat 1319640 8 0 eq_refl) (XCC 12%nat 1319656 8 0 eq_refl)
           (XCC 13%nat 1319608 8 0 eq_refl) (XCC 14%nat 1319616 8 0 eq_refl) (XCC 15%nat 1319592 8 1319360 eq_refl) SOlock SOwpos SOwbase
           SOrpos SOrend (XCC 16%nat 1319352 8 1319120 eq_refl) (XCC 17%nat 1319260 4 4294967295 eq_refl) (XCC 18%nat 1319160 8 0 eq_refl) (XCC 19%nat 1319176 8 0 eq_refl)
           (XCC 20%nat 1319128 8 0 eq_refl) (XCC 21%nat 1319136 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11eba4) M R1 (Z_to_bv 64 0x11e8b4) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x11e8b4) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpX.KS_dpX; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.

  (* [comment removed for export] *)
  Definition stdoutPA (MV : word -> option byte) : Prop :=
    rdn ASEGS MV (Z_to_bv 64 1319500) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
    /\ rdn ASEGS MV (Z_to_bv 64 1319400) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1319416) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1319368) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1319376) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_e : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preE LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6791552 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutPA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x11eba4) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
Proof.
    intros LB LK cr A M model R S st tid (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G2 G4 G10 SOP.
    pose proof Hsp as Hsp'. destruct SOP as (SOlock & SOwpos & SOwbase & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpXe.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468892 <=? a) && (a + n <=? 2147469204) || (2147615866 <=? a) && (a + n <=? 2147616066)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_E i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_E i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_E i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x1423d0 <=? a) && (a + Z.of_nat n <=? 0x142a10) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXe.dpXe_conc fx R MV V HS64 HT64
           G2 G4 HSr HSa CWR CDF
           IMGc (WSG 1321536 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1321616 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1325488 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6922704 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6922712 4%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6922720 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6923248 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468892 1 eq_refl) (SHW 2147468893 1 eq_refl) (SHW 2147468894 1 eq_refl) (SHW 2147468895 1 eq_refl)
           (SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl) (SHW 2147468929 1 eq_refl)
           (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl)
           (SHW 2147468936 1 eq_refl) (SHW 2147468937 1 eq_refl) (SHW 2147468938 1 eq_refl) (SHW 2147468939 1 eq_refl) (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl)
           (SHW 2147468941 1 eq_refl) (SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl)
           (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl) (SHW 2147468952 1 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468953 1 eq_refl)
           (SHW 2147468954 1 eq_refl) (SHW 2147468955 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468964 1 eq_refl) (SHW 2147468964 4 eq_refl)
           (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468968 4 eq_refl) (SHW 2147468969 1 eq_refl)
           (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468976 4 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl)
           (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 1 eq_refl) (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl)
           (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl)
           (SHW 2147468992 4 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl)
           (SHW 2147469000 1 eq_refl) (SHW 2147469000 4 eq_refl) (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl) (SHW 2147469004 4 eq_refl)
           (SHW 2147469008 4 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469013 1 eq_refl) (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl)
           (SHW 2147469016 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl) (SHW 2147469019 1 eq_refl) (SHW 2147469020 4 eq_refl)
           (SHW 2147469024 4 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl) (SHW 2147469031 1 eq_refl)
           (SHW 2147469032 1 eq_refl) (SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 4 eq_refl)
           (SHW 2147469040 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469041 1 eq_refl) (SHW 2147469042 1 eq_refl) (SHW 2147469043 1 eq_refl) (SHW 2147469044 1 eq_refl)
           (SHW 2147469044 4 eq_refl) (SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469052 1 eq_refl)
           (SHW 2147469052 4 eq_refl) (SHW 2147469053 1 eq_refl) (SHW 2147469054 1 eq_refl) (SHW 2147469055 1 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl)
           (SHW 2147469057 1 eq_refl) (SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469064 1 eq_refl) (SHW 2147469064 4 eq_refl)
           (SHW 2147469065 1 eq_refl) (SHW 2147469066 1 eq_refl) (SHW 2147469067 1 eq_refl) (SHW 2147469068 1 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469069 1 eq_refl)
           (SHW 2147469070 1 eq_refl) (SHW 2147469071 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469080 4 eq_refl)
           (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl)
           (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl) (SHW 2147469092 1 eq_refl)
           (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147469104 1 eq_refl) (SHW 2147469105 1 eq_refl) (SHW 2147469106 1 eq_refl)
           (SHW 2147469107 1 eq_refl) (SHW 2147469108 1 eq_refl) (SHW 2147469109 1 eq_refl) (SHW 2147469110 1 eq_refl) (SHW 2147469111 1 eq_refl) (SHW 2147469112 1 eq_refl)
           (SHW 2147469113 1 eq_refl) (SHW 2147469114 1 eq_refl) (SHW 2147469115 1 eq_refl) (SHW 2147469116 1 eq_refl) (SHW 2147469117 1 eq_refl) (SHW 2147469118 1 eq_refl)
           (SHW 2147469119 1 eq_refl) (SHW 2147469120 1 eq_refl) (SHW 2147469121 1 eq_refl) (SHW 2147469122 1 eq_refl) (SHW 2147469123 1 eq_refl) (SHW 2147469124 1 eq_refl)
           (SHW 2147469124 4 eq_refl) (SHW 2147469125 1 eq_refl) (SHW 2147469126 1 eq_refl) (SHW 2147469127 1 eq_refl) (SHW 2147469128 4 eq_refl) (SHW 2147469132 1 eq_refl)
           (SHW 2147469132 4 eq_refl) (SHW 2147469133 1 eq_refl) (SHW 2147469134 1 eq_refl) (SHW 2147469135 1 eq_refl) (SHW 2147469180 1 eq_refl) (SHW 2147469180 4 eq_refl)
           (SHW 2147469181 1 eq_refl) (SHW 2147469182 1 eq_refl) (SHW 2147469183 1 eq_refl) (SHW 2147469184 4 eq_refl) (SHW 2147469188 1 eq_refl) (SHW 2147469188 4 eq_refl)
           (SHW 2147469189 1 eq_refl) (SHW 2147469190 1 eq_refl) (SHW 2147469191 1 eq_refl) (SHW 2147469192 1 eq_refl) (SHW 2147469192 4 eq_refl) (SHW 2147469193 1 eq_refl)
           (SHW 2147469194 1 eq_refl) (SHW 2147469195 1 eq_refl) (SHW 2147469196 4 eq_refl) (SHW 2147469200 1 eq_refl) (SHW 2147469200 4 eq_refl) (SHW 2147469201 1 eq_refl)
           (SHW 2147469202 1 eq_refl) (SHW 2147469203 1 eq_refl) (SHW 2147615866 1 eq_refl) (SHW 2147615866 4 eq_refl) (SHW 2147615867 1 eq_refl) (SHW 2147615868 1 eq_refl)
           (SHW 2147615869 1 eq_refl) (SHW 2147615870 4 eq_refl) (SHW 2147615874 4 eq_refl) (SHW 2147615878 4 eq_refl) (SHW 2147615882 4 eq_refl) (SHW 2147615886 4 eq_refl)
           (SHW 2147615890 4 eq_refl) (SHW 2147615890 8 eq_refl) (SHW 2147615898 8 eq_refl) (SHW 2147615906 8 eq_refl) (SHW 2147615914 8 eq_refl) (SHW 2147615922 8 eq_refl)
           (SHW 2147615930 8 eq_refl) (SHW 2147615938 8 eq_refl) (SHW 2147615946 8 eq_refl) (SHW 2147615954 8 eq_refl) (SHW 2147615962 8 eq_refl) (SHW 2147615970 8 eq_refl)
           (SHW 2147615978 8 eq_refl) (SHW 2147615986 8 eq_refl) (SHW 2147615994 8 eq_refl) (SHW 2147616002 8 eq_refl) (SHW 2147616010 8 eq_refl) (SHW 2147616018 8 eq_refl)
           (SHW 2147616026 8 eq_refl) (SHW 2147616034 8 eq_refl) (SHW 2147616038 4 eq_refl) (SHW 2147616042 4 eq_refl) (SHW 2147616042 8 eq_refl) (SHW 2147616046 4 eq_refl)
           (SHW 2147616050 4 eq_refl) (SHW 2147616054 4 eq_refl) (SHW 2147616058 4 eq_refl) (SHW 2147616062 1 eq_refl) (SHW 2147616062 4 eq_refl) (SHW 2147616063 1 eq_refl)
           (SHW 2147616064 1 eq_refl) (SHW 2147616065 1 eq_refl) TIDC HTr (XCC 0%nat 6923248 4 0 eq_refl) (XCC1 1%nat 6923283 0 eq_refl eq_refl)
           (XCC 2%nat 6922720 8 6922728 eq_refl) (XCC 3%nat 6922712 4 1 eq_refl) (XCC 4%nat 6922736 8 1174352 eq_refl) (XCC 5%nat 6922992 8 624400 eq_refl) (XCC 6%nat 6922708 4 0 eq_refl) (STC1 10%nat 1933216 0 eq_refl eq_refl)
           (XCC 7%nat 6922728 8 0 eq_refl) (STC1 3%nat 1321616 0 eq_refl eq_refl) (STC 0%nat 1308376 8 1308376 eq_refl) (STC 2%nat 1321536 8 1 eq_refl) (STC 4%nat 1325328 4 1 eq_refl) (STC 5%nat 1325488 8 0 eq_refl)
           (STC1 8%nat 1338840 1 eq_refl eq_refl) (STC 7%nat 1335544 8 2147450880 eq_refl) (DSC 1319888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144096)) ltac:(img_rd) eq_refl) (DSC 1319904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1333596 1 eq_refl eq_refl) (DSC 1319904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (STC 9%nat 1932448 8 18446744073709551615 eq_refl) (STC 1%nat 1308888 8 1245236 eq_refl) (DSC 1319944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1319952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144352)) ltac:(img_rd) eq_refl) (DSC 1319968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1319968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1320008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1320032 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1320032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1320072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144448)) ltac:(img_rd) eq_refl)
           (DSC 1320096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144480)) ltac:(img_rd) eq_refl) (DSC 1320160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1320200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144576)) ltac:(img_rd) eq_refl) (DSC 1320224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl)
           (DSC 1320288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144832)) ltac:(img_rd) eq_refl) (DSC 1320352 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1320392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144864)) ltac:(img_rd) eq_refl) (DSC 1320416 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144960)) ltac:(img_rd) eq_refl)
           (DSC 1320480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145088)) ltac:(img_rd) eq_refl) (DSC 1320544 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
           (DSC 1320584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145216)) ltac:(img_rd) eq_refl) (DSC 1320608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145312)) ltac:(img_rd) eq_refl)
           (DSC 1320672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145408)) ltac:(img_rd) eq_refl) (DSC 1320736 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1320776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145504)) ltac:(img_rd) eq_refl) (DSC 1320800 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl)
           (DSC 1320864 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1320864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1320904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145696)) ltac:(img_rd) eq_refl) (DSC 1320928 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1320968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145792)) ltac:(img_rd) eq_refl) (DSC 1320992 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145824)) ltac:(img_rd) eq_refl)
           (DSC 1321056 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145856)) ltac:(img_rd) eq_refl) (DSC 1321120 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1321160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145888)) ltac:(img_rd) eq_refl) (DSC 1321184 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145920)) ltac:(img_rd) eq_refl)
           (DSC 1321248 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145952)) ltac:(img_rd) eq_refl) (DSC 1321312 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1321352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146400)) ltac:(img_rd) eq_refl) (DSC 1321376 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl)
           (DSC 1321440 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6924680 8 0 eq_refl) (XCC 9%nat 1319832 8 1319600 eq_refl) (XCC 10%nat 1319740 4 4294967295 eq_refl)
           (XCC 11%nat 1319640 8 0 eq_refl) (XCC 12%nat 1319656 8 0 eq_refl) (XCC 13%nat 1319608 8 0 eq_refl) (XCC 14%nat 1319616 8 0 eq_refl) (XCC 15%nat 1319592 8 1319360 eq_refl) SOlock
           SOwpos SOwbase SOrpos SOrend (XCC 16%nat 1319352 8 1319120 eq_refl) (XCC 17%nat 1319260 4 4294967295 eq_refl)
           (XCC 18%nat 1319160 8 0 eq_refl) (XCC 19%nat 1319176 8 0 eq_refl) (XCC 20%nat 1319128 8 0 eq_refl) (XCC 21%nat 1319136 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11eba4) M R1 (Z_to_bv 64 0x11e8b4) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x11e8b4) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXe.KS_dpXe; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.


  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_2 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1172448 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6791552 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6922688) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x11eba4) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX2_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468892 <=? a) && (a + n <=? 2147469204) || (2147615866 <=? a) && (a + n <=? 2147616066)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x1423d0 <=? a) && (a + Z.of_nat n <=? 0x142a10) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpX2_pre.dpX2_pre_conc fx R MV V HS64 Hcan
           HT64 G1 G2 G4 HSr HSa
           CWR CDF IMGc (WSG 1321536 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1321616 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1325488 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6922704 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6922712 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6922720 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6923248 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468892 1 eq_refl) (SHW 2147468893 1 eq_refl)
           (SHW 2147468894 1 eq_refl) (SHW 2147468895 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl)
           (SHW 2147468928 1 eq_refl) (SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468933 1 eq_refl)
           (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 1 eq_refl) (SHW 2147468937 1 eq_refl) (SHW 2147468938 1 eq_refl) (SHW 2147468939 1 eq_refl)
           (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl) (SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl) (SHW 2147468944 4 eq_refl)
           (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl) (SHW 2147468952 1 eq_refl)
           (SHW 2147468952 4 eq_refl) (SHW 2147468953 1 eq_refl) (SHW 2147468954 1 eq_refl) (SHW 2147468955 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468960 4 eq_refl)
           (SHW 2147468964 1 eq_refl) (SHW 2147468964 4 eq_refl) (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl)
           (SHW 2147468968 4 eq_refl) (SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468976 4 eq_refl)
           (SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 1 eq_refl)
           (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl)
           (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 4 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147468997 1 eq_refl)
           (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl) (SHW 2147469000 1 eq_refl) (SHW 2147469000 4 eq_refl) (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl)
           (SHW 2147469003 1 eq_refl) (SHW 2147469004 4 eq_refl) (SHW 2147469008 4 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469013 1 eq_refl)
           (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl)
           (SHW 2147469019 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469029 1 eq_refl)
           (SHW 2147469030 1 eq_refl) (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl)
           (SHW 2147469035 1 eq_refl) (SHW 2147469036 4 eq_refl) (SHW 2147469040 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469041 1 eq_refl) (SHW 2147469042 1 eq_refl)
           (SHW 2147469043 1 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl) (SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl)
           (SHW 2147469048 4 eq_refl) (SHW 2147469052 1 eq_refl) (SHW 2147469052 4 eq_refl) (SHW 2147469053 1 eq_refl) (SHW 2147469054 1 eq_refl) (SHW 2147469055 1 eq_refl)
           (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl) (SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 4 eq_refl)
           (SHW 2147469064 1 eq_refl) (SHW 2147469064 4 eq_refl) (SHW 2147469065 1 eq_refl) (SHW 2147469066 1 eq_refl) (SHW 2147469067 1 eq_refl) (SHW 2147469068 1 eq_refl)
           (SHW 2147469068 4 eq_refl) (SHW 2147469069 1 eq_refl) (SHW 2147469070 1 eq_refl) (SHW 2147469071 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469076 4 eq_refl)
           (SHW 2147469080 1 eq_refl) (SHW 2147469080 4 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl)
           (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl)
           (SHW 2147469091 1 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147469104 1 eq_refl)
           (SHW 2147469105 1 eq_refl) (SHW 2147469106 1 eq_refl) (SHW 2147469107 1 eq_refl) (SHW 2147469108 1 eq_refl) (SHW 2147469109 1 eq_refl) (SHW 2147469110 1 eq_refl)
           (SHW 2147469111 1 eq_refl) (SHW 2147469112 1 eq_refl) (SHW 2147469113 1 eq_refl) (SHW 2147469114 1 eq_refl) (SHW 2147469115 1 eq_refl) (SHW 2147469116 1 eq_refl)
           (SHW 2147469117 1 eq_refl) (SHW 2147469118 1 eq_refl) (SHW 2147469119 1 eq_refl) (SHW 2147469120 1 eq_refl) (SHW 2147469121 1 eq_refl) (SHW 2147469122 1 eq_refl)
           (SHW 2147469123 1 eq_refl) (SHW 2147469124 1 eq_refl) (SHW 2147469124 4 eq_refl) (SHW 2147469125 1 eq_refl) (SHW 2147469126 1 eq_refl) (SHW 2147469127 1 eq_refl)
           (SHW 2147469128 4 eq_refl) (SHW 2147469132 1 eq_refl) (SHW 2147469132 4 eq_refl) (SHW 2147469133 1 eq_refl) (SHW 2147469134 1 eq_refl) (SHW 2147469135 1 eq_refl)
           (SHW 2147469180 1 eq_refl) (SHW 2147469180 4 eq_refl) (SHW 2147469181 1 eq_refl) (SHW 2147469182 1 eq_refl) (SHW 2147469183 1 eq_refl) (SHW 2147469184 4 eq_refl)
           (SHW 2147469188 1 eq_refl) (SHW 2147469188 4 eq_refl) (SHW 2147469189 1 eq_refl) (SHW 2147469190 1 eq_refl) (SHW 2147469191 1 eq_refl) (SHW 2147469192 1 eq_refl)
           (SHW 2147469192 4 eq_refl) (SHW 2147469193 1 eq_refl) (SHW 2147469194 1 eq_refl) (SHW 2147469195 1 eq_refl) (SHW 2147469196 4 eq_refl) (SHW 2147469200 1 eq_refl)
           (SHW 2147469200 4 eq_refl) (SHW 2147469201 1 eq_refl) (SHW 2147469202 1 eq_refl) (SHW 2147469203 1 eq_refl) (SHW 2147615866 1 eq_refl) (SHW 2147615866 4 eq_refl)
           (SHW 2147615867 1 eq_refl) (SHW 2147615868 1 eq_refl) (SHW 2147615869 1 eq_refl) (SHW 2147615870 4 eq_refl) (SHW 2147615874 4 eq_refl) (SHW 2147615878 4 eq_refl)
           (SHW 2147615882 4 eq_refl) (SHW 2147615886 4 eq_refl) (SHW 2147615890 4 eq_refl) (SHW 2147615890 8 eq_refl) (SHW 2147615898 8 eq_refl) (SHW 2147615906 8 eq_refl)
           (SHW 2147615914 8 eq_refl) (SHW 2147615922 8 eq_refl) (SHW 2147615930 8 eq_refl) (SHW 2147615938 8 eq_refl) (SHW 2147615946 8 eq_refl) (SHW 2147615954 8 eq_refl)
           (SHW 2147615962 8 eq_refl) (SHW 2147615970 8 eq_refl) (SHW 2147615978 8 eq_refl) (SHW 2147615986 8 eq_refl) (SHW 2147615994 8 eq_refl) (SHW 2147616002 8 eq_refl)
           (SHW 2147616010 8 eq_refl) (SHW 2147616018 8 eq_refl) (SHW 2147616026 8 eq_refl) (SHW 2147616034 8 eq_refl) (SHW 2147616038 4 eq_refl) (SHW 2147616042 4 eq_refl)
           (SHW 2147616042 8 eq_refl) (SHW 2147616046 4 eq_refl) (SHW 2147616050 4 eq_refl) (SHW 2147616054 4 eq_refl) (SHW 2147616058 4 eq_refl) (SHW 2147616062 1 eq_refl)
           (SHW 2147616062 4 eq_refl) (SHW 2147616063 1 eq_refl) (SHW 2147616064 1 eq_refl) (SHW 2147616065 1 eq_refl) TIDC HTr
           (XCC 0%nat 6923248 4 0 eq_refl) (XCC1 1%nat 6923283 0 eq_refl eq_refl) (XCC 2%nat 6922720 8 6922728 eq_refl) (XCC 3%nat 6922712 4 2 eq_refl) (XCC 22%nat 6922744 8 1174352 eq_refl) (XCC 23%nat 6923000 8 692440 eq_refl)
           (XCC 6%nat 6922708 4 0 eq_refl) (XCC1 24%nat 6784852 0 eq_refl eq_refl) (XCC 4%nat 6922736 8 1174352 eq_refl) (XCC 5%nat 6922992 8 624400 eq_refl) (STC1 10%nat 1933216 0 eq_refl eq_refl) (XCC 7%nat 6922728 8 0 eq_refl)
           (STC1 3%nat 1321616 0 eq_refl eq_refl) (STC 0%nat 1308376 8 1308376 eq_refl) (STC 2%nat 1321536 8 1 eq_refl) (STC 4%nat 1325328 4 1 eq_refl) (STC 5%nat 1325488 8 0 eq_refl) (STC1 8%nat 1338840 1 eq_refl eq_refl)
           (STC 7%nat 1335544 8 2147450880 eq_refl) (DSC 1319888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144096)) ltac:(img_rd) eq_refl) (DSC 1319904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1333596 1 eq_refl eq_refl) (DSC 1319904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1932448 8 18446744073709551615 eq_refl)
           (STC 1%nat 1308888 8 1245236 eq_refl) (DSC 1319944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1319952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144352)) ltac:(img_rd) eq_refl) (DSC 1319968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1319968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1320032 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1320032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1320072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144448)) ltac:(img_rd) eq_refl) (DSC 1320096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1320096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144480)) ltac:(img_rd) eq_refl) (DSC 1320160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144576)) ltac:(img_rd) eq_refl) (DSC 1320224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl) (DSC 1320288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1320288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144832)) ltac:(img_rd) eq_refl) (DSC 1320352 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144864)) ltac:(img_rd) eq_refl) (DSC 1320416 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144960)) ltac:(img_rd) eq_refl) (DSC 1320480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1320480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145088)) ltac:(img_rd) eq_refl) (DSC 1320544 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145216)) ltac:(img_rd) eq_refl) (DSC 1320608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145312)) ltac:(img_rd) eq_refl) (DSC 1320672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1320672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145408)) ltac:(img_rd) eq_refl) (DSC 1320736 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145504)) ltac:(img_rd) eq_refl) (DSC 1320800 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1320864 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
           (DSC 1320864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1320904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145696)) ltac:(img_rd) eq_refl) (DSC 1320928 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145792)) ltac:(img_rd) eq_refl) (DSC 1320992 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145824)) ltac:(img_rd) eq_refl) (DSC 1321056 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1321056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145856)) ltac:(img_rd) eq_refl) (DSC 1321120 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1321168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145888)) ltac:(img_rd) eq_refl) (DSC 1321184 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145920)) ltac:(img_rd) eq_refl) (DSC 1321248 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1321248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145952)) ltac:(img_rd) eq_refl) (DSC 1321312 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1321360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146400)) ltac:(img_rd) eq_refl) (DSC 1321376 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl) (DSC 1321440 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1321440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6924680 8 0 eq_refl) (XCC 9%nat 1319832 8 1319600 eq_refl) (XCC 10%nat 1319740 4 4294967295 eq_refl) (XCC 11%nat 1319640 8 0 eq_refl)
           (XCC 12%nat 1319656 8 0 eq_refl) (XCC 13%nat 1319608 8 0 eq_refl) (XCC 14%nat 1319616 8 0 eq_refl) (XCC 15%nat 1319592 8 1319360 eq_refl) SOlock SOwpos
           SOwbase SOwrite CANc SOfd) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1321488 \/ 1325496 <= i < 6922704 \/ 6922728 <= i < 6923248 \/ 6923252 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11eba4) M R1 (Z_to_bv 64 0x126588) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1321488) || ((1325496 <=? a) && (a + Z.of_nat n <=? 6922704)) || ((6923252 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6924704) (Z.to_nat (2 * 1)) = Some (zero_lines 1%nat)).
    { apply (LITX 6924704 (Z.to_nat (2 * 1))); [|reflexivity]. change (Z.to_nat (2 * 1)) with (2 * 1%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1319360 /\ (1319360 + 124 <= q \/ q + 32 + 16 <= 1319360 + 120) /\ 1319360 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 1%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1319360 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 1%nat)%nat true R1 M1 model1 q 2 6924704 (2 * 1) 0 0 (zero_lines 1%nat) []).
    { cbn. lia. }
    { exact (sbm_lazy_eq _ _ SBM1). }
    { exact MI1. }
    { rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
    { rewrite (sbm_fds' _ _ SBM1). exact FD1. }
    { rewrite (sbm_rdrA _ _ SBM1). exact (di_rdr _ _ _ _ _ _ _ _ _ _ D). }
    { unfold wv_regs. repeat split; assumption. }
    { rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
      split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
      split; [intros X; discriminate X|]. intros _.
      split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
      split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
    { lia. }
    { rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }

    intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
    set (MV3 := mrestrict (ahid A model) M3) in *.
    assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1321488) || ((1325496 <=? a) && (a + Z.of_nat n <=? 6922704)) || ((6923252 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
    assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
      apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (WIN3 : forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
    assert (FW3 : forall a n, 1319360 <= a -> a + n <= 1319360 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1306624 -> MV3 (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
    set (VD := fun n : nat => match n with
               | 2%nat => S - 144 | 40%nat => canz
               | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
               | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
               | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
    assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1319360) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6922688) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
    assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDa : AS0DRVP_dpXd_2.aligned (VD 2%nat) 16).
    { cbn [VD]. unfold AS0DRVP_dpXd_2.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
    destruct (AS0DRVP_dpXd_2.dpXd_2_conc fx1 R3 MV3 VD HD64 (u64_range _)
           (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           Dg2 Dg8 Dg9 Dg10 Dg18 Dg19
           Dg20 Dg21 Dg22 HDr HDa DWR
           DDF IMG3 (fun d k Hd Hk => FW3 1319392 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1319400 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1319416 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1319448 8%nat _ SObuf eq_refl)
           (LIT3 1319456 8%nat _ SObufsz eq_refl) (LIT3 6922688 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
           (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1319368 8%nat _ SOrpos eq_refl)
           (LIT3 1319376 8%nat _ SOrend eq_refl) (LIT3 1319352 8%nat _ (XCC 16%nat 1319352 8 1319120 eq_refl) eq_refl) (LIT3 1319260 4%nat _ (XCC 17%nat 1319260 4 4294967295 eq_refl) eq_refl) (LIT3 1319160 8%nat _ (XCC 18%nat 1319160 8 0 eq_refl) eq_refl) (LIT3 1319176 8%nat _ (XCC 19%nat 1319176 8 0 eq_refl) eq_refl) (LIT3 1319128 8%nat _ (XCC 20%nat 1319128 8 0 eq_refl) eq_refl)
           (LIT3 1319136 8%nat _ (XCC 21%nat 1319136 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x126594) M3 R4 (Z_to_bv 64 0x11e8b4) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x11e8b4) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.


  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_3 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1172448 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6791552 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6922688) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x11eba4) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX3_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468892 <=? a) && (a + n <=? 2147469204) || (2147615866 <=? a) && (a + n <=? 2147616066)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x1423d0 <=? a) && (a + Z.of_nat n <=? 0x142a10) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpX3_pre.dpX3_pre_conc fx R MV V HS64 Hcan
           HT64 G1 G2 G4 HSr HSa
           CWR CDF IMGc (WSG 1321536 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1321616 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1325488 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6922704 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6922712 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6922720 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6923248 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468892 1 eq_refl) (SHW 2147468893 1 eq_refl)
           (SHW 2147468894 1 eq_refl) (SHW 2147468895 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl)
           (SHW 2147468928 1 eq_refl) (SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468933 1 eq_refl)
           (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 1 eq_refl) (SHW 2147468937 1 eq_refl) (SHW 2147468938 1 eq_refl) (SHW 2147468939 1 eq_refl)
           (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl) (SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl) (SHW 2147468944 4 eq_refl)
           (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl) (SHW 2147468952 1 eq_refl)
           (SHW 2147468952 4 eq_refl) (SHW 2147468953 1 eq_refl) (SHW 2147468954 1 eq_refl) (SHW 2147468955 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468960 4 eq_refl)
           (SHW 2147468964 1 eq_refl) (SHW 2147468964 4 eq_refl) (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl)
           (SHW 2147468968 4 eq_refl) (SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468976 4 eq_refl)
           (SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 1 eq_refl)
           (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl)
           (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 4 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147468997 1 eq_refl)
           (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl) (SHW 2147469000 1 eq_refl) (SHW 2147469000 4 eq_refl) (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl)
           (SHW 2147469003 1 eq_refl) (SHW 2147469004 4 eq_refl) (SHW 2147469008 4 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469013 1 eq_refl)
           (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl)
           (SHW 2147469019 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469029 1 eq_refl)
           (SHW 2147469030 1 eq_refl) (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl)
           (SHW 2147469035 1 eq_refl) (SHW 2147469036 4 eq_refl) (SHW 2147469040 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469041 1 eq_refl) (SHW 2147469042 1 eq_refl)
           (SHW 2147469043 1 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl) (SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl)
           (SHW 2147469048 4 eq_refl) (SHW 2147469052 1 eq_refl) (SHW 2147469052 4 eq_refl) (SHW 2147469053 1 eq_refl) (SHW 2147469054 1 eq_refl) (SHW 2147469055 1 eq_refl)
           (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl) (SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 4 eq_refl)
           (SHW 2147469064 1 eq_refl) (SHW 2147469064 4 eq_refl) (SHW 2147469065 1 eq_refl) (SHW 2147469066 1 eq_refl) (SHW 2147469067 1 eq_refl) (SHW 2147469068 1 eq_refl)
           (SHW 2147469068 4 eq_refl) (SHW 2147469069 1 eq_refl) (SHW 2147469070 1 eq_refl) (SHW 2147469071 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469076 4 eq_refl)
           (SHW 2147469080 1 eq_refl) (SHW 2147469080 4 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl)
           (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl)
           (SHW 2147469091 1 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147469104 1 eq_refl)
           (SHW 2147469105 1 eq_refl) (SHW 2147469106 1 eq_refl) (SHW 2147469107 1 eq_refl) (SHW 2147469108 1 eq_refl) (SHW 2147469109 1 eq_refl) (SHW 2147469110 1 eq_refl)
           (SHW 2147469111 1 eq_refl) (SHW 2147469112 1 eq_refl) (SHW 2147469113 1 eq_refl) (SHW 2147469114 1 eq_refl) (SHW 2147469115 1 eq_refl) (SHW 2147469116 1 eq_refl)
           (SHW 2147469117 1 eq_refl) (SHW 2147469118 1 eq_refl) (SHW 2147469119 1 eq_refl) (SHW 2147469120 1 eq_refl) (SHW 2147469121 1 eq_refl) (SHW 2147469122 1 eq_refl)
           (SHW 2147469123 1 eq_refl) (SHW 2147469124 1 eq_refl) (SHW 2147469124 4 eq_refl) (SHW 2147469125 1 eq_refl) (SHW 2147469126 1 eq_refl) (SHW 2147469127 1 eq_refl)
           (SHW 2147469128 4 eq_refl) (SHW 2147469132 1 eq_refl) (SHW 2147469132 4 eq_refl) (SHW 2147469133 1 eq_refl) (SHW 2147469134 1 eq_refl) (SHW 2147469135 1 eq_refl)
           (SHW 2147469180 1 eq_refl) (SHW 2147469180 4 eq_refl) (SHW 2147469181 1 eq_refl) (SHW 2147469182 1 eq_refl) (SHW 2147469183 1 eq_refl) (SHW 2147469184 4 eq_refl)
           (SHW 2147469188 1 eq_refl) (SHW 2147469188 4 eq_refl) (SHW 2147469189 1 eq_refl) (SHW 2147469190 1 eq_refl) (SHW 2147469191 1 eq_refl) (SHW 2147469192 1 eq_refl)
           (SHW 2147469192 4 eq_refl) (SHW 2147469193 1 eq_refl) (SHW 2147469194 1 eq_refl) (SHW 2147469195 1 eq_refl) (SHW 2147469196 4 eq_refl) (SHW 2147469200 1 eq_refl)
           (SHW 2147469200 4 eq_refl) (SHW 2147469201 1 eq_refl) (SHW 2147469202 1 eq_refl) (SHW 2147469203 1 eq_refl) (SHW 2147615866 1 eq_refl) (SHW 2147615866 4 eq_refl)
           (SHW 2147615867 1 eq_refl) (SHW 2147615868 1 eq_refl) (SHW 2147615869 1 eq_refl) (SHW 2147615870 4 eq_refl) (SHW 2147615874 4 eq_refl) (SHW 2147615878 4 eq_refl)
           (SHW 2147615882 4 eq_refl) (SHW 2147615886 4 eq_refl) (SHW 2147615890 4 eq_refl) (SHW 2147615890 8 eq_refl) (SHW 2147615898 8 eq_refl) (SHW 2147615906 8 eq_refl)
           (SHW 2147615914 8 eq_refl) (SHW 2147615922 8 eq_refl) (SHW 2147615930 8 eq_refl) (SHW 2147615938 8 eq_refl) (SHW 2147615946 8 eq_refl) (SHW 2147615954 8 eq_refl)
           (SHW 2147615962 8 eq_refl) (SHW 2147615970 8 eq_refl) (SHW 2147615978 8 eq_refl) (SHW 2147615986 8 eq_refl) (SHW 2147615994 8 eq_refl) (SHW 2147616002 8 eq_refl)
           (SHW 2147616010 8 eq_refl) (SHW 2147616018 8 eq_refl) (SHW 2147616026 8 eq_refl) (SHW 2147616034 8 eq_refl) (SHW 2147616038 4 eq_refl) (SHW 2147616042 4 eq_refl)
           (SHW 2147616042 8 eq_refl) (SHW 2147616046 4 eq_refl) (SHW 2147616050 4 eq_refl) (SHW 2147616054 4 eq_refl) (SHW 2147616058 4 eq_refl) (SHW 2147616062 1 eq_refl)
           (SHW 2147616062 4 eq_refl) (SHW 2147616063 1 eq_refl) (SHW 2147616064 1 eq_refl) (SHW 2147616065 1 eq_refl) TIDC HTr
           (XCC 0%nat 6923248 4 0 eq_refl) (XCC1 1%nat 6923283 0 eq_refl eq_refl) (XCC 2%nat 6922720 8 6922728 eq_refl) (XCC 3%nat 6922712 4 2 eq_refl) (XCC 22%nat 6922744 8 1174352 eq_refl) (XCC 23%nat 6923000 8 692440 eq_refl)
           (XCC 6%nat 6922708 4 0 eq_refl) (XCC1 24%nat 6784852 0 eq_refl eq_refl) (XCC 4%nat 6922736 8 1174352 eq_refl) (XCC 5%nat 6922992 8 624400 eq_refl) (STC1 10%nat 1933216 0 eq_refl eq_refl) (XCC 7%nat 6922728 8 0 eq_refl)
           (STC1 3%nat 1321616 0 eq_refl eq_refl) (STC 0%nat 1308376 8 1308376 eq_refl) (STC 2%nat 1321536 8 1 eq_refl) (STC 4%nat 1325328 4 1 eq_refl) (STC 5%nat 1325488 8 0 eq_refl) (STC1 8%nat 1338840 1 eq_refl eq_refl)
           (STC 7%nat 1335544 8 2147450880 eq_refl) (DSC 1319888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144096)) ltac:(img_rd) eq_refl) (DSC 1319904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1333596 1 eq_refl eq_refl) (DSC 1319904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1932448 8 18446744073709551615 eq_refl)
           (STC 1%nat 1308888 8 1245236 eq_refl) (DSC 1319944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1319952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144352)) ltac:(img_rd) eq_refl) (DSC 1319968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1319968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1320032 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1320032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1320072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144448)) ltac:(img_rd) eq_refl) (DSC 1320096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1320096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144480)) ltac:(img_rd) eq_refl) (DSC 1320160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144576)) ltac:(img_rd) eq_refl) (DSC 1320224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl) (DSC 1320288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1320288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144832)) ltac:(img_rd) eq_refl) (DSC 1320352 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144864)) ltac:(img_rd) eq_refl) (DSC 1320416 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144960)) ltac:(img_rd) eq_refl) (DSC 1320480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1320480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145088)) ltac:(img_rd) eq_refl) (DSC 1320544 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145216)) ltac:(img_rd) eq_refl) (DSC 1320608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145312)) ltac:(img_rd) eq_refl) (DSC 1320672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1320672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145408)) ltac:(img_rd) eq_refl) (DSC 1320736 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145504)) ltac:(img_rd) eq_refl) (DSC 1320800 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1320864 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
           (DSC 1320864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1320904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145696)) ltac:(img_rd) eq_refl) (DSC 1320928 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145792)) ltac:(img_rd) eq_refl) (DSC 1320992 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145824)) ltac:(img_rd) eq_refl) (DSC 1321056 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1321056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145856)) ltac:(img_rd) eq_refl) (DSC 1321120 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1321168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145888)) ltac:(img_rd) eq_refl) (DSC 1321184 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145920)) ltac:(img_rd) eq_refl) (DSC 1321248 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1321248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145952)) ltac:(img_rd) eq_refl) (DSC 1321312 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1321360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146400)) ltac:(img_rd) eq_refl) (DSC 1321376 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl) (DSC 1321440 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1321440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6924680 8 0 eq_refl) (XCC 9%nat 1319832 8 1319600 eq_refl) (XCC 10%nat 1319740 4 4294967295 eq_refl) (XCC 11%nat 1319640 8 0 eq_refl)
           (XCC 12%nat 1319656 8 0 eq_refl) (XCC 13%nat 1319608 8 0 eq_refl) (XCC 14%nat 1319616 8 0 eq_refl) (XCC 15%nat 1319592 8 1319360 eq_refl) SOlock SOwpos
           SOwbase SOwrite CANc SOfd) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1321488 \/ 1325496 <= i < 6922704 \/ 6922728 <= i < 6923248 \/ 6923252 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11eba4) M R1 (Z_to_bv 64 0x126588) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1321488) || ((1325496 <=? a) && (a + Z.of_nat n <=? 6922704)) || ((6923252 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6924704) (Z.to_nat (2 * 2)) = Some (zero_lines 2%nat)).
    { apply (LITX 6924704 (Z.to_nat (2 * 2))); [|reflexivity]. change (Z.to_nat (2 * 2)) with (2 * 2%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1319360 /\ (1319360 + 124 <= q \/ q + 32 + 16 <= 1319360 + 120) /\ 1319360 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 2%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1319360 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 2%nat)%nat true R1 M1 model1 q 2 6924704 (2 * 2) 0 0 (zero_lines 2%nat) []).
    { cbn. lia. }
    { exact (sbm_lazy_eq _ _ SBM1). }
    { exact MI1. }
    { rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
    { rewrite (sbm_fds' _ _ SBM1). exact FD1. }
    { rewrite (sbm_rdrA _ _ SBM1). exact (di_rdr _ _ _ _ _ _ _ _ _ _ D). }
    { unfold wv_regs. repeat split; assumption. }
    { rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
      split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
      split; [intros X; discriminate X|]. intros _.
      split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
      split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
    { lia. }
    { rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }

    intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
    set (MV3 := mrestrict (ahid A model) M3) in *.
    assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1321488) || ((1325496 <=? a) && (a + Z.of_nat n <=? 6922704)) || ((6923252 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
    assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
      apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (WIN3 : forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
    assert (FW3 : forall a n, 1319360 <= a -> a + n <= 1319360 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1306624 -> MV3 (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
    set (VD := fun n : nat => match n with
               | 2%nat => S - 144 | 40%nat => canz
               | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
               | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
               | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
    assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1319360) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6922688) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
    assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDa : AS0DRVP_dpXd_3.aligned (VD 2%nat) 16).
    { cbn [VD]. unfold AS0DRVP_dpXd_3.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
    destruct (AS0DRVP_dpXd_3.dpXd_3_conc fx1 R3 MV3 VD HD64 (u64_range _)
           (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           Dg2 Dg8 Dg9 Dg10 Dg18 Dg19
           Dg20 Dg21 Dg22 HDr HDa DWR
           DDF IMG3 (fun d k Hd Hk => FW3 1319392 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1319400 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1319416 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1319448 8%nat _ SObuf eq_refl)
           (LIT3 1319456 8%nat _ SObufsz eq_refl) (LIT3 6922688 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
           (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1319368 8%nat _ SOrpos eq_refl)
           (LIT3 1319376 8%nat _ SOrend eq_refl) (LIT3 1319352 8%nat _ (XCC 16%nat 1319352 8 1319120 eq_refl) eq_refl) (LIT3 1319260 4%nat _ (XCC 17%nat 1319260 4 4294967295 eq_refl) eq_refl) (LIT3 1319160 8%nat _ (XCC 18%nat 1319160 8 0 eq_refl) eq_refl) (LIT3 1319176 8%nat _ (XCC 19%nat 1319176 8 0 eq_refl) eq_refl) (LIT3 1319128 8%nat _ (XCC 20%nat 1319128 8 0 eq_refl) eq_refl)
           (LIT3 1319136 8%nat _ (XCC 21%nat 1319136 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x126594) M3 R4 (Z_to_bv 64 0x11e8b4) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x11e8b4) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.


  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_4 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1172448 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6791552 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6922688) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x11eba4) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX4_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468892 <=? a) && (a + n <=? 2147469204) || (2147615866 <=? a) && (a + n <=? 2147616066)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x1423d0 <=? a) && (a + Z.of_nat n <=? 0x142a10) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpX4_pre.dpX4_pre_conc fx R MV V HS64 Hcan
           HT64 G1 G2 G4 HSr HSa
           CWR CDF IMGc (WSG 1321536 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1321616 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1325488 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6922704 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6922712 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6922720 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6923248 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468892 1 eq_refl) (SHW 2147468893 1 eq_refl)
           (SHW 2147468894 1 eq_refl) (SHW 2147468895 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl)
           (SHW 2147468928 1 eq_refl) (SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468933 1 eq_refl)
           (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 1 eq_refl) (SHW 2147468937 1 eq_refl) (SHW 2147468938 1 eq_refl) (SHW 2147468939 1 eq_refl)
           (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl) (SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl) (SHW 2147468944 4 eq_refl)
           (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl) (SHW 2147468952 1 eq_refl)
           (SHW 2147468952 4 eq_refl) (SHW 2147468953 1 eq_refl) (SHW 2147468954 1 eq_refl) (SHW 2147468955 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468960 4 eq_refl)
           (SHW 2147468964 1 eq_refl) (SHW 2147468964 4 eq_refl) (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl)
           (SHW 2147468968 4 eq_refl) (SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468976 4 eq_refl)
           (SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 1 eq_refl)
           (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl)
           (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 4 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147468997 1 eq_refl)
           (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl) (SHW 2147469000 1 eq_refl) (SHW 2147469000 4 eq_refl) (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl)
           (SHW 2147469003 1 eq_refl) (SHW 2147469004 4 eq_refl) (SHW 2147469008 4 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469013 1 eq_refl)
           (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl)
           (SHW 2147469019 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469029 1 eq_refl)
           (SHW 2147469030 1 eq_refl) (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl)
           (SHW 2147469035 1 eq_refl) (SHW 2147469036 4 eq_refl) (SHW 2147469040 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469041 1 eq_refl) (SHW 2147469042 1 eq_refl)
           (SHW 2147469043 1 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl) (SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl)
           (SHW 2147469048 4 eq_refl) (SHW 2147469052 1 eq_refl) (SHW 2147469052 4 eq_refl) (SHW 2147469053 1 eq_refl) (SHW 2147469054 1 eq_refl) (SHW 2147469055 1 eq_refl)
           (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl) (SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 4 eq_refl)
           (SHW 2147469064 1 eq_refl) (SHW 2147469064 4 eq_refl) (SHW 2147469065 1 eq_refl) (SHW 2147469066 1 eq_refl) (SHW 2147469067 1 eq_refl) (SHW 2147469068 1 eq_refl)
           (SHW 2147469068 4 eq_refl) (SHW 2147469069 1 eq_refl) (SHW 2147469070 1 eq_refl) (SHW 2147469071 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469076 4 eq_refl)
           (SHW 2147469080 1 eq_refl) (SHW 2147469080 4 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl)
           (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl)
           (SHW 2147469091 1 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147469104 1 eq_refl)
           (SHW 2147469105 1 eq_refl) (SHW 2147469106 1 eq_refl) (SHW 2147469107 1 eq_refl) (SHW 2147469108 1 eq_refl) (SHW 2147469109 1 eq_refl) (SHW 2147469110 1 eq_refl)
           (SHW 2147469111 1 eq_refl) (SHW 2147469112 1 eq_refl) (SHW 2147469113 1 eq_refl) (SHW 2147469114 1 eq_refl) (SHW 2147469115 1 eq_refl) (SHW 2147469116 1 eq_refl)
           (SHW 2147469117 1 eq_refl) (SHW 2147469118 1 eq_refl) (SHW 2147469119 1 eq_refl) (SHW 2147469120 1 eq_refl) (SHW 2147469121 1 eq_refl) (SHW 2147469122 1 eq_refl)
           (SHW 2147469123 1 eq_refl) (SHW 2147469124 1 eq_refl) (SHW 2147469124 4 eq_refl) (SHW 2147469125 1 eq_refl) (SHW 2147469126 1 eq_refl) (SHW 2147469127 1 eq_refl)
           (SHW 2147469128 4 eq_refl) (SHW 2147469132 1 eq_refl) (SHW 2147469132 4 eq_refl) (SHW 2147469133 1 eq_refl) (SHW 2147469134 1 eq_refl) (SHW 2147469135 1 eq_refl)
           (SHW 2147469180 1 eq_refl) (SHW 2147469180 4 eq_refl) (SHW 2147469181 1 eq_refl) (SHW 2147469182 1 eq_refl) (SHW 2147469183 1 eq_refl) (SHW 2147469184 4 eq_refl)
           (SHW 2147469188 1 eq_refl) (SHW 2147469188 4 eq_refl) (SHW 2147469189 1 eq_refl) (SHW 2147469190 1 eq_refl) (SHW 2147469191 1 eq_refl) (SHW 2147469192 1 eq_refl)
           (SHW 2147469192 4 eq_refl) (SHW 2147469193 1 eq_refl) (SHW 2147469194 1 eq_refl) (SHW 2147469195 1 eq_refl) (SHW 2147469196 4 eq_refl) (SHW 2147469200 1 eq_refl)
           (SHW 2147469200 4 eq_refl) (SHW 2147469201 1 eq_refl) (SHW 2147469202 1 eq_refl) (SHW 2147469203 1 eq_refl) (SHW 2147615866 1 eq_refl) (SHW 2147615866 4 eq_refl)
           (SHW 2147615867 1 eq_refl) (SHW 2147615868 1 eq_refl) (SHW 2147615869 1 eq_refl) (SHW 2147615870 4 eq_refl) (SHW 2147615874 4 eq_refl) (SHW 2147615878 4 eq_refl)
           (SHW 2147615882 4 eq_refl) (SHW 2147615886 4 eq_refl) (SHW 2147615890 4 eq_refl) (SHW 2147615890 8 eq_refl) (SHW 2147615898 8 eq_refl) (SHW 2147615906 8 eq_refl)
           (SHW 2147615914 8 eq_refl) (SHW 2147615922 8 eq_refl) (SHW 2147615930 8 eq_refl) (SHW 2147615938 8 eq_refl) (SHW 2147615946 8 eq_refl) (SHW 2147615954 8 eq_refl)
           (SHW 2147615962 8 eq_refl) (SHW 2147615970 8 eq_refl) (SHW 2147615978 8 eq_refl) (SHW 2147615986 8 eq_refl) (SHW 2147615994 8 eq_refl) (SHW 2147616002 8 eq_refl)
           (SHW 2147616010 8 eq_refl) (SHW 2147616018 8 eq_refl) (SHW 2147616026 8 eq_refl) (SHW 2147616034 8 eq_refl) (SHW 2147616038 4 eq_refl) (SHW 2147616042 4 eq_refl)
           (SHW 2147616042 8 eq_refl) (SHW 2147616046 4 eq_refl) (SHW 2147616050 4 eq_refl) (SHW 2147616054 4 eq_refl) (SHW 2147616058 4 eq_refl) (SHW 2147616062 1 eq_refl)
           (SHW 2147616062 4 eq_refl) (SHW 2147616063 1 eq_refl) (SHW 2147616064 1 eq_refl) (SHW 2147616065 1 eq_refl) TIDC HTr
           (XCC 0%nat 6923248 4 0 eq_refl) (XCC1 1%nat 6923283 0 eq_refl eq_refl) (XCC 2%nat 6922720 8 6922728 eq_refl) (XCC 3%nat 6922712 4 2 eq_refl) (XCC 22%nat 6922744 8 1174352 eq_refl) (XCC 23%nat 6923000 8 692440 eq_refl)
           (XCC 6%nat 6922708 4 0 eq_refl) (XCC1 24%nat 6784852 0 eq_refl eq_refl) (XCC 4%nat 6922736 8 1174352 eq_refl) (XCC 5%nat 6922992 8 624400 eq_refl) (STC1 10%nat 1933216 0 eq_refl eq_refl) (XCC 7%nat 6922728 8 0 eq_refl)
           (STC1 3%nat 1321616 0 eq_refl eq_refl) (STC 0%nat 1308376 8 1308376 eq_refl) (STC 2%nat 1321536 8 1 eq_refl) (STC 4%nat 1325328 4 1 eq_refl) (STC 5%nat 1325488 8 0 eq_refl) (STC1 8%nat 1338840 1 eq_refl eq_refl)
           (STC 7%nat 1335544 8 2147450880 eq_refl) (DSC 1319888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144096)) ltac:(img_rd) eq_refl) (DSC 1319904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1333596 1 eq_refl eq_refl) (DSC 1319904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1932448 8 18446744073709551615 eq_refl)
           (STC 1%nat 1308888 8 1245236 eq_refl) (DSC 1319944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1319952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144352)) ltac:(img_rd) eq_refl) (DSC 1319968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1319968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1320032 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1320032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1320072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144448)) ltac:(img_rd) eq_refl) (DSC 1320096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1320096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144480)) ltac:(img_rd) eq_refl) (DSC 1320160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144576)) ltac:(img_rd) eq_refl) (DSC 1320224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl) (DSC 1320288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1320288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144832)) ltac:(img_rd) eq_refl) (DSC 1320352 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144864)) ltac:(img_rd) eq_refl) (DSC 1320416 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144960)) ltac:(img_rd) eq_refl) (DSC 1320480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1320480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145088)) ltac:(img_rd) eq_refl) (DSC 1320544 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145216)) ltac:(img_rd) eq_refl) (DSC 1320608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145312)) ltac:(img_rd) eq_refl) (DSC 1320672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1320672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145408)) ltac:(img_rd) eq_refl) (DSC 1320736 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145504)) ltac:(img_rd) eq_refl) (DSC 1320800 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1320864 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
           (DSC 1320864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1320904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145696)) ltac:(img_rd) eq_refl) (DSC 1320928 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1320976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145792)) ltac:(img_rd) eq_refl) (DSC 1320992 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145824)) ltac:(img_rd) eq_refl) (DSC 1321056 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1321056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145856)) ltac:(img_rd) eq_refl) (DSC 1321120 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1321168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145888)) ltac:(img_rd) eq_refl) (DSC 1321184 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145920)) ltac:(img_rd) eq_refl) (DSC 1321248 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1321248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145952)) ltac:(img_rd) eq_refl) (DSC 1321312 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1321360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146400)) ltac:(img_rd) eq_refl) (DSC 1321376 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl) (DSC 1321440 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1321440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6924680 8 0 eq_refl) (XCC 9%nat 1319832 8 1319600 eq_refl) (XCC 10%nat 1319740 4 4294967295 eq_refl) (XCC 11%nat 1319640 8 0 eq_refl)
           (XCC 12%nat 1319656 8 0 eq_refl) (XCC 13%nat 1319608 8 0 eq_refl) (XCC 14%nat 1319616 8 0 eq_refl) (XCC 15%nat 1319592 8 1319360 eq_refl) SOlock SOwpos
           SOwbase SOwrite CANc SOfd) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1321488 \/ 1325496 <= i < 6922704 \/ 6922728 <= i < 6923248 \/ 6923252 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11eba4) M R1 (Z_to_bv 64 0x126588) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1321488) || ((1325496 <=? a) && (a + Z.of_nat n <=? 6922704)) || ((6923252 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6924704) (Z.to_nat (2 * 3)) = Some (zero_lines 3%nat)).
    { apply (LITX 6924704 (Z.to_nat (2 * 3))); [|reflexivity]. change (Z.to_nat (2 * 3)) with (2 * 3%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). destruct (BC 2 ltac:(lia)) as (B2a & B2b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. apply rdn_cons1; [lia | exact B2a|]. apply rdn_cons1; [lia | exact B2b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1319360 /\ (1319360 + 124 <= q \/ q + 32 + 16 <= 1319360 + 120) /\ 1319360 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 3%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1319360 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 3%nat)%nat true R1 M1 model1 q 2 6924704 (2 * 3) 0 0 (zero_lines 3%nat) []).
    { cbn. lia. }
    { exact (sbm_lazy_eq _ _ SBM1). }
    { exact MI1. }
    { rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
    { rewrite (sbm_fds' _ _ SBM1). exact FD1. }
    { rewrite (sbm_rdrA _ _ SBM1). exact (di_rdr _ _ _ _ _ _ _ _ _ _ D). }
    { unfold wv_regs. repeat split; assumption. }
    { rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
      split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
      split; [intros X; discriminate X|]. intros _.
      split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
      split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
    { lia. }
    { rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }

    intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
    set (MV3 := mrestrict (ahid A model) M3) in *.
    assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1321488) || ((1325496 <=? a) && (a + Z.of_nat n <=? 6922704)) || ((6923252 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
    assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
      apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (WIN3 : forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
    assert (FW3 : forall a n, 1319360 <= a -> a + n <= 1319360 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1306624 -> MV3 (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
    set (VD := fun n : nat => match n with
               | 2%nat => S - 144 | 40%nat => canz
               | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
               | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
               | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
    assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1319360) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6922688) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
    assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDa : AS0DRVP_dpXd_4.aligned (VD 2%nat) 16).
    { cbn [VD]. unfold AS0DRVP_dpXd_4.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
    destruct (AS0DRVP_dpXd_4.dpXd_4_conc fx1 R3 MV3 VD HD64 (u64_range _)
           (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           Dg2 Dg8 Dg9 Dg10 Dg18 Dg19
           Dg20 Dg21 Dg22 HDr HDa DWR
           DDF IMG3 (fun d k Hd Hk => FW3 1319392 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1319400 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1319416 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1319448 8%nat _ SObuf eq_refl)
           (LIT3 1319456 8%nat _ SObufsz eq_refl) (LIT3 6922688 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
           (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1319368 8%nat _ SOrpos eq_refl)
           (LIT3 1319376 8%nat _ SOrend eq_refl) (LIT3 1319352 8%nat _ (XCC 16%nat 1319352 8 1319120 eq_refl) eq_refl) (LIT3 1319260 4%nat _ (XCC 17%nat 1319260 4 4294967295 eq_refl) eq_refl) (LIT3 1319160 8%nat _ (XCC 18%nat 1319160 8 0 eq_refl) eq_refl) (LIT3 1319176 8%nat _ (XCC 19%nat 1319176 8 0 eq_refl) eq_refl) (LIT3 1319128 8%nat _ (XCC 20%nat 1319128 8 0 eq_refl) eq_refl)
           (LIT3 1319136 8%nat _ (XCC 21%nat 1319136 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x126594) M3 R4 (Z_to_bv 64 0x11e8b4) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x11e8b4) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

End Exit.
End FPX_1.
