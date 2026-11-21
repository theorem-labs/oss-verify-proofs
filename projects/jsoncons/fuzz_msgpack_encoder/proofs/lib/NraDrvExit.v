(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed rdn_cons1, msteps_vis_fx, ex_cell_vis and 8 more. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0248. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.ShapeLaws OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvPiece OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DiagLoopK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvStdio OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0248.NraDrvPrintfK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0248.NraDrvPrintf1.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Na0DrvP_dpX Na0DrvP_dpX2_pre Na0DrvP_dpX3_pre Na0DrvP_dpX4_pre. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Na0DrvP_dpXe. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DrvP_dpX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DrvP_dpX2_pre OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DrvP_dpX3_pre OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DrvP_dpX4_pre OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232.Na0DrvP_dpXd_2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232.Na0DrvP_dpXd_3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232.Na0DrvP_dpXd_4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DrvP_dpXe OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0ExitCells.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_NraDrvExit () := "C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses;subrelationC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes3nat02I46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07I46Stdlib9micromega7EnvRing5PExpr00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00K46Stdlib9micromega7EnvRing5PExpr01I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z2ltI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00C47Corelib9RelationsDRelation_Definitions8relationC47Corelib4Init3Nat3mulI46Stdlib;setoid_ring<Ring_polynom5PExpr00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega7EnvRing5PExpr05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes6option02I46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega:ZMicromega=Zeval_formulaC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC47Corelib7Classes9Morphisms@subrelation_reflC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Logic2or00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr06C47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms6ProperC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib;setoid_ring<Ring_polynom5PExpr05C56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic3notK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib7Mh_00634Spec:zero_linesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK47Corelib4Init5Logic2or01C47Corelib4Init5Logic8f_equal2C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic2or02I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA5lzinvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c49OSSVerify5KrLib:NraDrvExit5exitAC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit8exit_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK7stdoutAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0248=NraDrvPrintf18stdoutXAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan@Na0DrvP_dpX2_pre@AS0DRVP_dpX2_pre7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_01199Na0DrvLib@store_ok_definedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propc49OSSVerify5KrLib:NraDrvExit<wsg_writableC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit;sh_writableC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List<nth_error_Inc49OSSVerify5KrLib:NraDrvExit;ex_cell_visC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_00356ArtMem:art_bytes1C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit<cells_at_nthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio8img_cellC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib4asan@Na0DrvP_dpX2_pre@AS0DRVP_dpX2_pre=dpX2_pre_concC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_lzinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms;ProperProxyC47Corelib4Init9Datatypes3orbC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool<orb_true_iffC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC59OSSVerify5KrLib7Mh_0119;Na0DrvStdio6rdn_trC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addc49OSSVerify5KrLib:NraDrvExit9rdn_cons1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK6wv_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0248=NraDrvPrintf15nl_ptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00639ShapeLaws>t_exit_has_nilC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib7Mh_0116:As0DrvKitA;sbm_lazy_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA=sbm_halted_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK8sbm_fds'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7wv_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK6wv_iovC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom3Pol00C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z8max_specC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_2>AS0DRVP_dpXd_27alignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic8eq_transC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_2>AS0DRVP_dpXd_2;dpXd_2_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctKsame_but_materialized_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA9lzinv_sbmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKArz_exit_at_lit_lzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib7sbm_fdsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c49OSSVerify5KrLib:NraDrvExit=msteps_vis_fxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7wv_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7wv_loopC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega6VarMap4findC46Stdlib9micromega5Tauto7eval_bfC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00C47Corelib7Program6Basics4implK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init5Logic4True01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool02C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio8EX_CELLSC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit8XC_CELLSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK5SOBUFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan@Na0DrvP_dpX2_pre@AS0DRVP_dpX2_pre;KS_dpX2_preC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C47Corelib7Classes?RelationClasses=iff_ReflexiveI4ELinuxProcessSemantics?LinuxProcessSem5State5event00I46Stdlib;setoid_ring<Ring_polynom3Mon00I47Corelib7Numbers7BinNums8positive00C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7WV_KEEPC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_2>AS0DRVP_dpXd_29KS_dpXd_2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit;fetch_exitAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX?is_ecall_ECALLWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan@Na0DrvP_dpX3_pre@AS0DRVP_dpX3_pre7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan@Na0DrvP_dpX3_pre@AS0DRVP_dpX3_pre=dpX3_pre_concC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_3>AS0DRVP_dpXd_37alignedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_3>AS0DRVP_dpXd_3;dpXd_3_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan@Na0DrvP_dpX3_pre@AS0DRVP_dpX3_pre;KS_dpX3_preC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_3>AS0DRVP_dpXd_39KS_dpXd_3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan@Na0DrvP_dpX4_pre@AS0DRVP_dpX4_pre7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan@Na0DrvP_dpX4_pre@AS0DRVP_dpX4_pre=dpX4_pre_concC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_4>AS0DRVP_dpXd_47alignedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_4>AS0DRVP_dpXd_4;dpXd_4_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan@Na0DrvP_dpX4_pre@AS0DRVP_dpX4_pre;KS_dpX4_preC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_4>AS0DRVP_dpXd_49KS_dpXd_4C1?~~~~~~~~~~~~~~~".
Ltac2 kr_t_NraDrvExit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c49OSSVerify5KrLib:NraDrvExit8cells_atC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6to_natC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List<nth_error_InC47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01C46Stdlib6ZArith4Zdiv9Zplus_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedC59OSSVerify5KrLib7Mh_00387SeqExec7rdn_appC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC59OSSVerify5KrLib7Mh_01059SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib7Mh_0116:As0DrvKitA5lzinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct6hcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitAEmrestrict_munrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0036=AsanAcctShapeGsrz_msteps_restricted_TC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I47Corelib4Init9Datatypes4bool00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs8asegs_wxC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib6di_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089<HeapIfaceAMx<aiob_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:asc_got_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:asc_got_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7cell_isC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9asc_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib8dla_segsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio7vis_lowC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4woffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct<range_avoidsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct@rdn_mrestrict_eqC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz06I47Corelib4Init5Logic5False00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio8EX_CELLSC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib7Classes9Morphisms5flip2C59OSSVerify5KrLib7Mh_0057<Na0ExitCells=atexit_cellsAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057<Na0ExitCells7ax_cellC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057<Na0ExitCells8AX_CELLSC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9MorphismsDiff_impl_subrelationC59OSSVerify5KrLib7Mh_0057<Na0ExitCells;ax_cells_inC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegI59OSSVerify5KrLib7Mh_0057<Na0ExitCells3axv00C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC59OSSVerify5KrLib7Mh_0057<Na0ExitCells4AXLOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057<Na0ExitCells4AXHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057<Na0ExitCells4SSLOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057<Na0ExitCells4SSHIC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic2or01C59OSSVerify5KrLib7Mh_0089:IcptIfaceABaic_shadow_definedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC59OSSVerify5KrLib7Mh_00368AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool>negb_false_iffC59OSSVerify5KrLib7Mh_0089:IcptIfaceA;aic_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA;icl_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA<aicl_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:shadow_blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_invC47Corelib4Init5Logic5proj2C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC35stdpp7tactics<f_equal_helpK47Corelib4Init5Logic2or02C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_img_hiC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib7Mh_0089:IcptIfaceA:icl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA;aicl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA>aic_img_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4BoolAandb_false_intro2C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC47Corelib7Classes?RelationClasses=iff_ReflexiveC59OSSVerify5KrLib7Mh_0089:IcptIfaceA8LOWSH_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA8LOWSH_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA9HIGHSH_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA9HIGHSH_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_windowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit8exit_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK7stdoutAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0248=NraDrvPrintf18stdoutXAC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit5exitAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan;Na0DrvP_dpX;AS0DRVP_dpX7alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib@store_ok_definedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propc49OSSVerify5KrLib:NraDrvExit<wsg_writableC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit;sh_writableC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit;ex_cell_visC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_00356ArtMem:art_bytes1C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit<cells_at_nthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio8img_cellC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8f_equal2C69OSSVerify5KrLib4asan;Na0DrvP_dpX;AS0DRVP_dpX8dpX_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_lzinvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib7Mh_0116:As0DrvKitA=sbm_halted_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKArz_exit_at_lit_lzC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC59OSSVerify5KrLib7Mh_01199Na0DrvLib7sbm_fdsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit=msteps_vis_fxC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit8XC_CELLSC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK5SOBUFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan;Na0DrvP_dpX;AS0DRVP_dpX6KS_dpXC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit;fetch_exitAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX?is_ecall_ECALLWC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c49OSSVerify5KrLib:NraDrvExit9exit_preEC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit8stdoutPAC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit5exitEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan<Na0DrvP_dpXe<AS0DRVP_dpXe7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan<Na0DrvP_dpXe<AS0DRVP_dpXe9dpXe_concC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:NraDrvExit:XC_CELLS_EC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan<Na0DrvP_dpXe<AS0DRVP_dpXe7KS_dpXeC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XC_CELLS : list (Z * Z * Z) :=
  [(7028080, 4, 0); (7028115, 1, 0); (7027552, 8, 7027560); (7027544, 4, 2); (7027568, 8, 1277044); (7027824, 8, 648332); (7027540, 4, 0); (7027560, 8, 0); (7029512, 8, 0); (1423464, 8, 1423232); (1423372, 4, 4294967295); (1423272, 8, 0); (1423288, 8, 0); (1423240, 8, 0); (1423248, 8, 0); (1423224, 8, 1422992); (1422984, 8, 1422752); (1422892, 4, 4294967295); (1422792, 8, 0); (1422808, 8, 0); (1422760, 8, 0); (1422768, 8, 0); (7027576, 8, 1277044); (7027832, 8, 716372); (6889684, 1, 0)].
(* [comment removed for export] *)
Definition XC_CELLS_E : list (Z * Z * Z) :=
  [(7028080, 4, 0); (7028115, 1, 0); (7027552, 8, 7027560); (7027544, 4, 1); (7027568, 8, 1277044); (7027824, 8, 648332); (7027540, 4, 0); (7027560, 8, 0); (7029512, 8, 0); (1423464, 8, 1423232); (1423372, 4, 4294967295); (1423272, 8, 0); (1423288, 8, 0); (1423240, 8, 0); (1423248, 8, 0); (1423224, 8, 1422992); (1422984, 8, 1422752); (1422892, 4, 4294967295); (1422792, 8, 0); (1422808, 8, 0); (1422760, 8, 0); (1422768, 8, 0)].

Definition cells_at (MV : word -> option byte) (l : list (Z * Z * Z)) : Prop :=
  Forall (fun c => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (Z.to_nat (snd (fst c))) = Some (word_to_le_bytes (Z.to_nat (snd (fst c))) (Z_to_bv 64 (snd c)))) l.
Lemma cells_at_nth : forall MV l (i : nat) a n v, cells_at MV l -> nth_error l i = Some (a, n, v) ->
  rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
Proof.
ltac2:(KReplay.run1 (kr_t_NraDrvExit ()) [] "h01ch11xh22HCh32Hnh42MVh51ah61ih71lh81nh91vp;1p;2p;3p;4p;5p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9P0g003<R1p4p710p8P0g003]R2p4p710p8P0P2p4p7210p8p1004:p4p70p1004jp4p710p8p1005Hp4p70p10066p4p710p8g006Rj10Tg0077j1>Tg007Uj16Tg0088j14Tg008Zj2;Tg009:j1:Tg009Zj2CTg00:Rj3?Tg00;0j42Tg00;Pj27Tg00<2j31TP2j35Tg00<Lj29Tg00=2j3=Tg00=Oj1ETg00=oj43Tg00>`j2DTP1j3<Tg00?hj38Tg00@?j3BTg00@aj5@Tg00ABj6ATg00A]#0#0#0R1#0#0#0#>R2#6%>1#6R1#4[g00BBR0/;0R3/;0R4#:g00B`f5R5f4R6'C%44A?456P3P0P0P0f3R7f2R8C2f1R9C2,7431%:1R1#4R:g00C?R;f8R<f0R=9530R>9500,92R?A=00>#ER>C3A=30=,92,D>,71R131X04R2f6R@5<4A84=<P;f;P?P>C3=1:1X04P9O1[^14[f7R<984=P;f:P?P>C3=1:1X04P9O1[^14P;f9P?P>C3=1:1X04=<4<[AB42@P9P3P0P0P0P6P7C2P8C2R8P4P@P5P8P=D@EAW3W2X90X80X50W6W7W4o"). Qed.

(* [comment removed for export] *)
Definition exitA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6896216) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x15b8a0 <= i < 0x15c3a0 -> MV (Z_to_bv 64 i) = None).

Definition exitE (tid : Z) (MV : word -> option byte) : Prop :=   (* [comment removed for export] *)
  cells_at MV XC_CELLS_E
  /\ rdn ASEGS MV (Z_to_bv 64 6896216) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x15b8a0 <= i < 0x15c3a0 -> MV (Z_to_bv 64 i) = None).


Lemma rdn_cons1 : forall (MV : word -> option byte) a b (n : nat) bs, 0 <= a ->
  rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [b] -> rdn ASEGS MV (Z_to_bv 64 (a + 1)) n = Some bs -> rdn ASEGS MV (Z_to_bv 64 a) (Datatypes.S n) = Some (b :: bs).
Proof.
  intros MV a b n bs Ha H1 H2. change (Datatypes.S n) with (1 + n)%nat. change (b :: bs) with ([b] ++ bs). apply (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec.rdn_app ASEGS MV 1%nat n _ _ _ H1).
  replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1)); [exact H2|].
  apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Ltac img_rd := vm_compute; apply f_equal; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity.

Lemma fetch_exitA : fetch_word ASEGS (Z_to_bv 64 0x1379d8) = Some ECALLW.
Proof.
ltac2:(KReplay.run1 (kr_t_NraDrvExit ()) [] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9P0p1003<p4p710p8P0p1003]R1p4p710p8P0P1p4p7210p8p1004:p4p70p1004jp4p710p8p1005Hp4p70p10066p4p710p8g006Rj11Tg0077j14Tg007Uj17Tg0088j1>Tg00FOj16Tg00QOj2;Tg00RBj3:Tg00;Pj25Tg00LGj28Tg00Rej13Tg00<Lj29Tg00SJj2=Tg00<2j3<Tf0R1#1#1p=2%31#3p=0g00A]R1#1#2#2R0#4R2#7R3#>R4%01#2#0#6R51;255:2,53'8g00C?%10#4%21#0#1#0#0#2#3#0#1#0#1#2#6'9'=g00TL,535<4do"). Qed.

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
  apply (KONT _ model1 MI1 SBM). apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA.mrestrict_munrestrict. intros a Ha. exact (HC a Ha).
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
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x6b6000).
    { unfold EX_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
    rewrite (u64_lit a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.
  #[using="scfg L C IL HIok Hsp DL"] Lemma ax_cells_vis : forall LB LK cr A M (model : Model) (ax : axv), dinvA LB LK cr A M model -> atexit_cellsA M ax ->
    atexit_cellsA (mrestrict (ahid A model) M) ax.
Proof.
ltac2:(KReplay.run1 (kr_t_NraDrvExit ()) ["FPX_1"; "Exit"] "h01xh12Hah24__p1h34__p2h44__x1h54__x2h64__x3h71Hh82H4h93Hk0h:7__arithh;4__ffh<4__p3h=4__p4h>6__sat5h?6__sat6h@6__sat7hA8__varmaphB5__withC4__x4hD4__x5hE4cstrhF5lemmahG2z4hH1AhI2B3hJ2BBhK1DhL2H0hM2HchN2HkhO2LBhP2LKhQ1MhR6__sat8hS6__sat9hT2axhU1chV2crhW1khX5modelhY1ohZ1yh[1zp&0p;2p;1p;:p;3p;7p;4p;Cp;6p;<p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0g01d:R1p4p710p9P0g003<R2p4p710p8P0g003]R3p4p710p8P0P3p4p7210p8p1004:p4p70g004jR0p4p710p8p1005Hp4p70p10066p4p710p8g008Zj2{Tg009:j1XTg006Rj10Tg0077j1zTg007Uj1vTg0088j1oTg00nQm:0@Tg01d\j2jTg018lj2Hj3fTg00\Fj2ITg01ecj1Wj2CTg01fdj1cTP2j3ZTg00?hj3|Tg01gfR2j2yTg01h?k20KTP1k70JTg00@?j3pTg01h]k30FTg01iNk30ETg00Fmj2:Tg01N>j2DTg00FOj17Tg00Q4R1j24Tg00<Lj2OTg00=OR4j1_Tg00=oj4lTg00=2j3wTg00>`k200Tg00;Pj2~Tg00<2j3BTg01:gR5j2hTg00J8R6j1gTg01O5j2YTg015QR7j29Tg00LGj2dTg01D<k40OTg01<@k10NTg01<ek20MTg00Rej1>Tg01=Gj2uTg01=oj2tTg01>Lj3rTg00GJj2qTg01jSk20HTg00Kgk20GTg00E0j1FTg01Dcj2mTg01ELj2VTg00EOk10DTg01F8k10?Tg01?0j2^Tg01FVj4RTg01?Nk10>Tg01?lk10=Tg01@Wj2MTg01S5j4QTg01A:j2iTg00[dk10<Tg01ULj3[Tg01A]k209Tg01B?k208Tg01Bkk30:Tg01CJk407Tg00DTj2<Tg01G4mC06Tg01I\k305Tg01J?k20ATP0j6nTg01K<k204Tg01L6k30BTg01M8k60CTP3j3kTg01ORm<03Tg01P]m<02Tg01W>k301Tg00Eoj3sTg01RQk60ITg01S`j7`Tg01TDj7xTg01Thk70LTg01Uoj8}Tf0R3#0#0p=Ef1R0g00BBR8;k3p=6Ak883p=GAw883p=5f3R9f2R:'<1<03'4p=8g00OYR;/<3p=11<03,4:p=]g00iiR<g01bn7B3p=eP8g00B`R=P8P8P4f4R4P6P9g01XDP:P0P3N<03p>0QP=P8P5P6P7g01Y1f5R7P4P9P:P0P3N<02p>0P1<:0/43p=a%>3#>p=21m83p=LB01803p=?g01bBR6As6037s:p=PP0g01YSR5g01Z2R>P>g01ZRR?P3J0Ip=KP9P5P>P>P?P:P0P5P>P>P?P3g01[YR@F`Fxp=@P:P5P>P>P?P0P3K0Lp=bP:P5P>P>P?P8P0g01\9RAP3CQP@F`p=;P8P0g01\`P3CQp=\P0P5P>P>P?P3P@F`p>0;P:P5P>P>P?P0P3Fxp=U%>3#0p=3%03#>p=A%03#0#0#0p=N1i83p=JP8P0PAP3CQp=S%03#0#0#0#0#0#0#0p=TP9P5P>P>P?P:P0P3G}p==1{88R5#XRAg01]G#Xg01^Eg00A]R@#0RB#0RC#0RD#0RE#ERF#zRG#v%zD#vRH#o[g00k@g01kDp,2arRIp,2HIRJp,3sp0RKp,2M0RLf6RMP7P4P9P:P0N:0@1j901{58RN1H79/I4RO#WRP%c:RQ3Z%c9RR9|N3RSf7RT/H7/IM/C0[^0N'yp-0RUP220K30XZUX0Ug01lC1HM4/I7#W=ZNR%c49|N3R2f8RV/HM/IT/C0[^0NP3K0JWFApNPQ%W4RP=ZNQ1CM0\S^0NRS'y%W7=ZNR1CT0\2^0N<0F3WFApNPQP3O2PSB0E703g01m9RS1650RP#GRQ%5PRP,:QRRg01n7RWC8g01o5RXPQPRg0203RRC8'D%1P%7DRD7]P'4P1PS165:R1#GRP%51R1,:PRQPWC8PXPPPQPRC8'D%11?]1Df:R1/HVf9RQ'I/C9P3PS1654RS#GRP%5S,:PRSPWC8PXPPPSPRC8'D1657#5RR#1?]RDPTPMP7O2f<RR/CM%XHRH#oRSg00C?RPf=RX165TRW#G,OGRY%5W#_RWCl165V#5#_RZAw58V,OG+00,~H9BS3XYSP3PPf>RS/HRRH/IXR[PYPWClPPPHPWPXPY1h3ZP8165QRZ#GRPfAR\f?R]%g:R^,:3,OG3f#eX[8p,4scfgp,1LPIp,1Cp,2ILPJp,4HIokPKp,2DLPLfCRLfBP\f@RJP]PS%g0R],:PPR%5ZRZ#_RI,h01Y;Z,9]R_P0P]1d8]PI1Y;3X08RIPZO1P3X08PIPZPZ1d8ZI0QJ0PP3H0ORZP_&0N:RI%1^R^f;R`,65#5Ra-0M;Rb19;a1Y;aRc=B8a'4AB8c;9aa;'DRa165R#5,Y;RcP8%7BRd%>BRe#>#2#7Rf'uRg19;dRh%1f1tdfRi,9;[[Rj%1dRkg01afRlArdf0UW1Rf%1i\l^1kRm1qGKRK%7ERE+0HRn%1K%1E20GKE#1[[REg00P7Ro#F#FRp#FRq#FRr#FRs#FRt#F#LRu%LsRs%Lr%Lp1m8oRo'?Rp'?Rr'?'?g01cNRv'VRw%Lt%Lq/?o'?/VvRo1?sp,?u/VvRu&0D6Rp9Pou7Po9Pow3P%X6R6P8P8&0?8RoP:1^87CRP0P81^84P9PoCRCR&0>8Rw&0=8RuPu1KuTPuP8%>@Rs#0,M8Rqg01[2Rt1M8eReCQC@Pu1KuVPuP8PqPt1i8;RtCQC@5bu&0<>R>Pu1M8BRB9;utP>Pu1\Bq-0;uP>PuA;ute1KuQ5UuP>PuPu%3@#3#2#E#2#3#2#A#A#N#7Rq#J1M8@RV5;uRxPuA[8VeRe%3@#3#2#E#2#2#A#A#2#N#7Ry#JRz'SC@Pu%3@#3#A#E#3#E#A#N#3#E#7R{#JR|=;uVR}Pu1Se|C@5buP>Pu%>s#2#2#2#2#2#2#3#E#N#T#T#T#7Re#JR~1M8s5;u1Ku15UuP>PuA[8VBRs9;utPu%3@#3#2#A#3#N#T#7R@#J,\sC@C=C=C=C=C=C=209u?R?P3P:g00n1Rs,d<2083:=B<sdB0:8;0H07Rsb;bAbBX48X58X68XC8XD8X2UX3UX<UX=UAB849,47AB84;,4M'D%1:R<199M%1M/41PqP41:4TR1PyC8P{P4P1P{C8'DAaeTX1:MTR1#1191@'4[[[[[[^48^58^68^C8^D8^2U^3U^<U^=UP31<KiRi165\R\#5R1/<D1<1;19;1P4P1PK%gQ%G\P7PMPTP`PRp,3HspRRO?b:b>b?b@bGb8bEb9NC061OGPR`,qGR\PZP_PIP^PbPaPcP8PgPjPfPm%7FRF,ud%1F1tdFRm,9;[\hArdF0VlX1k%1m\l^1kPnPE1VrvRv?PvpP6P8P81^89P:PoCRP0PoCRPwPu1M8CRC9;ut1Ku75UuP>PuPuPxPuA[8VCRC/SzC@PuP}Pu1SC|C@5buP>PuA;u~B1KuM5UuP>PuA;utVPu%Jd>058G,\VC@C=C=C=P?Psb;bAbBX48X58X68X2UX3U14<9PqP01:09RqPyC8P{P0PqP{C8'DAae9M%19199m'4[[[^48^58^68^2U^3UP3Pi165LRL#5R5/<DP5PK%GLPXPSPRO8b:b>b?b@bRbSbGb8bEb9-0APEn1:\],OG9fJS#ee204`09fJS#eeWNXW=B0BHYWeJ0CEn1C[Teb7WIWJP0P3O2n2001000000121000000bLXM2XUNb7O21jO:eW7WKWTWXWQXHAWVWPWOo"). Qed.

  (* [comment removed for export] *)
  #[using="scfg L IL ICok ILY Hsp DL"] Lemma sh_writable : forall LB LK cr A M (model : Model) a n, dinvA LB LK cr A M model ->
    ((2147469128 <=? a) && (a + n <=? 2147470932) || (2147623588 <=? a) && (a + n <=? 2147623604) || (2147628820 <=? a) && (a + n <=? 2147629172)) = true ->
    L5Defs.L5.writable ASEGS (mrestrict (ahid A model) M) a n.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_NraDrvExit ()) ["FPX_1"; "Exit"] "h02Hbh14__x1h27__arithh34__ffh46__sat1h56__sat2h68__varmaph75__with85lemmah95heq_xh:4__p1h;6__sat3h<4__x2h=4__x3h>4__x4h?6__sat4h@1HhA4__x5hB4__p2hC4__p3hD1ghE1zhF2H0hG2H1hH2H2hI2H3hJ2H4hK6__sat5hL1rhM3H10hN3H11hO3H12hP3H13hQ3H14hR3H15hS2H5hT2H6hU2H7hV2H8hW2H9hX2SAhY4__x6hZ1bh[1qh\2q0h]2q1h^2r0h_2r1h`1xha2Hahb2Hxhc1Ahd1Ghe1lhf1Bhg1Dhh3DEFhi2HHhj2Hihk2LBhl2LKhm1Mhn3VISho2_Hhp1ahq2a0hr2crhs1iht5modelhu1np%0p%1p%2p%3p&0p&1p;2p;1p;:p;;p;8p;3p;4p;6p;7p;@p;>p;5p;Dp;=p-1R0g0211R1p4p710p9P0p1000Sp4p710p9P0p1001?R2p4p710p9P0P2p4p7210p9P0P2p4p73110p9P0g021XR2p4p710p9P0g022GR3p4p710p9P0g003<R4p4p710p8P0g003]R5p4p710p8P0P5p4p7210p8p1004:p4p70g004jR0p4p710p8p1005Hp4p70g0066R6p4p710p8g008Zk21sTg009:k10sTg006Rj10Tg0077k11;Tg007Uk118Tg0088k11cTg00nQm:1RTg00Rej13Tg00Fmj27Tg023Bj2\Tg00oNm;1GTg00EOk10bTg010Kk10UTg011Ik81CTg018lk20wk30}Tg00\Fk21Bk31QTg023_j29Tg024<j2nTg01N>S00j21Tg01gfR7j2BTg01h]R8k30vTg024Zk20PTP1k40OTg025:k21rTg025gk81:Tg026Zk31kTg00Q4S01j25Tg027PR1k60ETg028Ak20DTP2k71dm=1]Tg00DTj22Tg028bR2k60<Tg029Tj2]Tg00FOj1?Tg01=Gk20~Tg01=ok210Tg01>Lk311Tg00GJj2lTg01jSk21LTg00Kgj2DTg00E0j1eTg01Dck20{Tg01?0k20JTg01F8k11FTg01?Nk11ETg01?lk11DTg01A:k20zTg00[dk10yTg01@Wk20xTg01A]k21ATg00LGk20STg01B?k21@Tg01Bkk31?Tg01CJk41>Tg015Qj2<Tg02:4k30uTg02:Nm@1=Tg00<Lj2Ak11bTg00<2j34Tg02;Xk109Tg02<1j1ZTg00X6k11<Tg02<ik21qTg02=fk20tTg02>ik10]Tg02?Gk11oTg02?im>1nTg02@lk11lTP4k30;Tg00Eoj3oTg02Aok21jTP6k60ZTg02C3k30pTg02D5k30GTg02E;k51iTg02EZk319Tg02F5j2^Tg02Ffj2CTg02GCk20oTg02G`j2TTg02HAj2QTg02Hhj2WTg02IOj2STg02J5j2YTg02J[k20KTg01H4k11fTg01HRk21eTg01I3k30lTg02KGk217Tg02L0k30kTg02LYk30qTg02M<k30RTg02N@k204Tg02N]k80iTg01I\k31aTg01J?k20BTg00?hk312Tg00@?k31`Tg02O:k30hTg02OTk50cTg00ABk61_Tg02P1k11^Tg02Q2k51[Tg02R3k11ZTg02S4k51YTg02T5k21XTg02TVk60fTg02U7k11WTg02V9k21UTP0k60dTg02W<mD1TTg02XBk30eTg02YAk31VTg02Yfk31PTg02Zdk71\Tg02[ok41NTP3m;0aTg01W>k30=Tg01ELk216Tg01FVk41MTg01S5j4|Tg01S`j7uTg01TDk70YTg01ULk31KTg01Thk71gTg01RQk61hTg01Uok80ATP5k31JTg00=2k31ITg00;0k40NTg02\bk61HTg02]Fk31mTf0R5#0#0p=L%35#3#3#3p>0I%35#3p=I%35#0#3#0p=t%05#3p=P%05#0#0#?p=`%05#0#3#0p>0r%05#?p=bf3R3f2R0'9f1R6/95'np=f%05#0#0#0#0#0#0#0p=}%05#0#0#3p=a%05#3#0#3p>0V%35#0p={%35#0#0#0p>0|%05#0#0#0p>0^g00iiR4g00n1R9745p=:g00OYR:/201<65'5p=Kp-0R;P;P7P7P5P7g01h?R<P8L1:p>1p1n65=449p=wP;P7P6P5H1Np=8P5P6Q00P1P0g01[YR8P3f4R=f5R>f6R?f7R@f8RAf9RBN=1]p=M1106/15p=XA4469A4459'5p=_1965=449p=>A4469/55p>0mP;P?P7P>Q00P1P=P3P0P6P5N;0ap>0C1506/15p>05P;P@P7P?Q00P>P=P3P0P6P5N;0ap>0@P;P?P7P>Q01P2P=P3P0P6P5N;0ap>0?12301265'5p=H1565,10p>0>1<:5p>0H12:5p=6g00BBR200{5p=mB0=265:0=20g01cNRC+16p=yg01bBRDAoD657o0p>03P2P0P6P5H1Mp=O20x25p>0:P?g01YSREg01Z2RFPFg01ZRRGP>PEPFPFPGP2P=g01\9RHP3C|P8FuP0PEPFPFPGP2P6g01\`RIP5C|P8FuK0Yp=j20z25p==P0PEPFPFPGP2P6PHP5C|P8Fup=@B1K265p=cP2P6PHP5C|p>02P3PEPFPFPGP0P6PEPFPFPGP5P8FuK0Yp=iP0PEPFPFPGP6P5K1gp=R%05#0#0p>0TP6PEPFPFPGP5J1hp>01P0PEPFPFPGP6P5K0Yp>08P3PEPFPFPGP0P6P5L0Ap=vP?PEPFPFPGP>P=P3PEPFPFPGP0P6P5L0AL0Ap=V1<65,50p=g1206/55p>0`12301<65'5p=[20S25p>00A4265p=;P2P6PIP5C|p>0Q%35#3#3#0p>0_P0PEPFPFPGP2P6PIP5C|P8Fup=~P>PEPFPFPGP=P3P0PEPFPFPGP6P5K0YL0Ap=sg01bnS029445p>0\B1J225p>0FB1I225p>07B0p>=3B0G065'5p=zP2P2P6P5H0Np>0MP2P2%36#0#0#0#0#0#?%?5H0Np=rP2P2%36#0#0#0#0#0#?P5H0Np=NP2P2%06#0#0#0#0#0#?%?5H0Np=pP2P2%06#0#0#0#0#0#?P5H0Np=k%05#3#0p>0[%05#3#0#0p>0LAo0659o=3p=F20t65=449p=qA425:p=G20406/759423p=J1<06125:'5p=UB0=265p>0XB0=265016Cp>0nAoD65p>0gP0PEPFPFPGP2P6g01[2RCP5C|P8Fup>15P6PEPFPFPGP5J1Hp>14B1m265p>06P>PEPFPFPGP=P3P0PEPFPFPGP2P6PCP5C|P8FuL0Ap=d20406/75p>0jg02]iRC,C5004Cp=hB0=265:0=20p>13P2P=P3P0P6P5J0dp=xB0h065:0h=3p=EB0G065,53p>1S1265,50p>0WP=PEPFPFPGP3P0P6PEPFPFPGP5P8FuL0Ap>1O21s22RE$0sS03g01]GRC$0sg01^EQ03g00A]RI#0RH#0RJ#0RK#0S04#LS05$1;RL$18RM&1;K$18RN$1cS06[g00k@p,2arS07p,2HIS08p,3sp0S09p,2M0ROP@P?P>P=P3P0N:1R%3IRP#3S0:#3S0;$0I$0I$0IRQ#3#LRR#0#I#t#P#`RSP01706RT%3R#I$0r#t#bRRCf%LI#}#a#a#a$0V$0r#bRUP0PT%LI#}#a#a#a$0V#t#bRVCf'\%LI#}#a#a#{#I$0|#t#bRWP0PT%LI#}#a#a#I$0^#I#t#bRTCf'\#:Q07Q08Q09POPBPAP@P?P>P=P6N;1GQ08PB&0bCS0<PAP@P?P>&0U=L1Cg00C?20w@>01B?S0=P=P3AK55=17?6P219S@S0>17@?RC/9RS0?'nS0@19U@S0A19CVS0B'nS0C'\ROPWP@PCPTCfRC'\#:%:O%:CS0D'1RX'B19SAS0E17A@RY/9RS0F'nRZ19UAS0G19YVS0H'nR['\R\19WAS0I19YTS0J'nRY'\#:%:\R\%:YS0K'1<0v5W820POCP=O2PX%:Z%:[S0L'1RX,B\P;^f;R\^c;RCP;P;\;P7P;P;P7P7H0OROH0ORYP;P\P7P;P;P7P<H0OS0MH0OR<P;P\P7P721r;7R]POQ0M&1p]L1:R]19SBR^17BAR_/9RR`'nRa19UBS0N19_VS0O'nRb'\#:%:aRa%:bRb'1P519WBS0P19_TS0Q'wS0RQ0Rg02^a:1k;7R7Q0R'8M:MW820PZ[P5O2Q0K,1X%:^S0S%:`S0T'5S0U,BaPCPYP<P]f:Ra,9SRX17aBS0V/9RR['wRZ19UaR_Q0V/9VRc'wRd'1%:XS0W%:[S0X'5S0Y/1dPZQ0YP5PdPd187dJ0E19WaS0ZQ0V/9TS0['wRZPZ187ZM:MW820D^`P5O2Q0UQ0R7Xb1__cS0\,BdPCPYP<P]f;Rd,9S17daS0]/>RS0^+0mRb19UdR`Q0]/9VR^'wR['1%:`S0_%:^S0`'5S0a,1bR^P\POPb187bP[Q0aP5K0C19WdR[Q0]/9TRb'wR`P`187`M:MW820D_cP5O2Q0YQ0\'1S0b/1Z1_[bS0c,B`P\Q0MP\\;PYQ00P1P<P8P]K1dS0df<R8,>SR1178dS0e/>RR`1>U8S0fQ0e/>VS0g'5S0h405RZ187Z19W8RZQ0e/9TRc'w1_ZcS0iP5L0@W820D[bP5O2Q0c,1^12S8S0j,B1PCPYP<P]f=R1,>SR^1718S0k/>RRb'5R[19U1Q0k/>VS0l+0mRc'112S1RZ/5bR_/1cP[P_P^PZP5PbPb187bJ0<PcPc187cJ0E1>W1S0mQ0k/>TS0n'5S0oQ0oQ0o,87S0pM:MW81]S8P5O2Q0j/5`Q0hQ0i3XQ0k/2RR`,BbPCPYP<P]f>Rb,2SR^17b1S0q/>RR_'5R[1>UbRXQ0q/>VRe'5Rf'1Q0q/2RRg,5^S0r/1fP[Q0rP\POP^187^P_PgP5K0?PfPf187fJ0E1>WbS0sQ0q/>TS0t'5S0uQ0uQ0u,87M:MW8Q0k/]RP5O215Z`S0vQ0o7Xc12UbS0w,BXPCPYP<P]PSf?RX17XbS0xPRCHRc1>UXR`Q0x/>VRZ'5Rf'112UXRg/5ZR_,1cP\POPc187cPfP_P`PgP5PZPZ187ZJ0<K0C19WXQ0x/>TS0y+0mR`P`187`M:MW81]UbP5O2Q0rQ0w/5eQ0u3XQ0x/2VRe,BZPCPYP<P]PSf@RZ17ZXR_PRCHRf12UZR^1>_VR['5Rh'112_VRi,5^Rj,1fRkP\POPf187fPhPjP\POP^187^P[PiP5K0?K0C1>WZRi1>_TR_'5R[P[187[M:MW8Q0x/]VP5O2B0>cgeS0z/1`12WZR`,BiP\Q0MQ0dfARi,2S17iZRe/2RPUPiPePVCH405Rg187g1>WiRc1>eTR['512WiR^/5[PcP^P5P[P[187[J0<L0@W81]WZP5O2B0>k`_12eTR`,B[P\Q0MQ0dfBR[,2S17[iR_/2RPUP[P_PVCH405Rk187k12W[Rk1>_TRc'512_TR_,5kP\POPk187kPcP_P5K0?L0@W81]eTP5O2B0>g^`%?HR`%3HR^#3Rg#3S0{#3#?Re+0~R_&0H`S0|%6e210`eRc$0H[[Rk%6`S0}g01afS0~B11`e6UWaReQ0}Q0~%6c[]aRjQ09,lLRhQ04#?Rf+1LS10%6h%6f1DhfRl#6S11[[S12g00P7Rm#eRn#eRo#eS13#eRp#eRq#eRr#eS14#mRs%mqS15%mnRn3yRq%mrS16%mpRp;ynRrQ1520{2mS175ysRmQ16Q177ypQ16%moS187ypRoQ15Q185ys&0bDRs603o803o803m803m803r803q&0sDRD20J20S1920J2=S1:&1F2Rq7O37O6&1E2Rr&1D2RmPmPm20z2:Ro&0:HS1;PmQ1;&0:^RHFj&0yFRFPmPm%=SS1<20x2IRt5@mS1=Pm1ctHRH%=RS1>+02CiPm%=US1?=@mtS1@Pm%=VS1A-02HCi5RmPm%=WS1B=@mtS1CPm%=TRu-02HCi5RmPFPm&0TQ$0^#}RQ#0$0^#}#`S1D#=&0:P5@mS1E201m?S1F608mPFPmPmQ1<Q1;,ctRHPmPHQ1>FjPmPmQ1?PHPmPHQ1AFjPmPmQ1BPHPmPHPuFj5Rm5RmCvFV21AmGRGP5P020S4921@50#:dB1?2:6H1>R9b3b6b7X12X<2X=2X>2X:;%66S1G?g63PSP6176=RvPRCHPUP6PvPVCHPWP6PvPTCH3XQ1D@0`=?173=Rv,2S1<vR12Uv1<vVPWPvPvPTC[405405[[[^12^<2^=2^>2^:;P512hcS1HfERcPhPifFS1IPZP=p,3HspS1JO8b2b4b5b;b0b0b0b0b0b0b0b0b0b0b012S5S1K?g5RS1L12U5S1M?g5VS1N12W5S1O?g5TS1P'1'1RvePvp,1LS1QQ07p,2ILS1Rp,4scfgS1SQ08p,4ICokS1TPbQ0<P1P8PdPa&0UBP=P6g02_QP6P6g02`QC[Rwg02aQP6P6g02bRC[17A3Rx$001;6xRxePxP_PkPePjQ10Q12PsPD20J26S1UPrPmPmQ1=PmQ1>-0QtCiS1VPmQ1@PmQ1A-0QtCiS1WPmQ1CPm20QtuCiS1X5Rm5RmPFPm%?QRQ#=S1Y=@mt%3KS1Z#IRx#3Ry#3$0I$0_$0_#}#`Rz#=9~mtEsPGP9b3b6b7X12PQP6P6PzC[\v^12P5P?P>O2b2b4b5b;b9Pwe40uN@1=Q06Pa1AL6O1&0yNS1[34$091AL0S1\#ZRN&1<a+1q20t8N$0]Q01&0]5$0\%:6RN[%:5&0]6$0\[Rw&0]0$0\\N&1o5P5n2001000000120000000XZ4Pw^Z4P51AL3S1]#Z-0t1Q1QQ07Q1RQ1SQ08Q1TPZQ0<PXPbP1P8&0UdP?N>1nP1&0F5Rw&075RNPbPwPNEzXDEQ1R$1lRv60;EQ03PvQ03PXPwPNPZPwPNEzXDE>0;E5WeP5%PxRx#0Rv#PRz$0T#`R{Q0:#?R|+0MS1^PE%0PR}#3R~#P,rzS1_PE%Iv%?~Rv'NS1`PE%3xRx#0Rz#0%3JS1a#3S1b#3S1c'pS1dPE%3z%?}Rz'NS1ePE%{x%0^Rx#3RJ'pS1fPE&0TyRy#0/NzS1gPE%3yRy/kzS1hPE%0JS1i$0I#LS1j#b,NyS1kPEQ1a#0S1l#3S1m#P#I#LQ1j'rS1jPEQ1b#0Ry#PS1b#0S1n$0[S1o%?gS1p'kS1qPEQ1o%0I$0V#b'NS1oPEQ1n#3S1n#0S1r#0/NzS1sPEQ1r#3S1rQ1p'kS1pPEQ1r%?^S1t'NS1rPEQ1n#{R^Q1t'kS1tPE1N^zS1nPEQ1b#3R^#0#P%?IS1b'NS1uPE%3^#IQ1Z'rS1ZPE%3yR^#0S1v#0S1w#0S1x#0Rz#0Q0{'rS0{PE%3z/NvS1yPEQ1x#3Rz#0/pyS1xPE%3zQ1i#?S1i'NS1zPEQ1w#3Rz#P%3J#?S1w'kS1{PE%{zQ0:#0S1|#3Rz#3'rS1}PEQ1v#3S1v#0RJ#0Ry#0%bz'kS1~PE%3yQ1w'NS1wPE%IJ/p^S20PEQ1v#3RJ#PQ1l'pS1lPE%3JRJ#0%0gRg'pS1vPE%3JQ04#3'pS04PE%3^R^#0RJ#0Ry#L%3g'rS21PE%3yRy#0Q0;#0#b'kS0;PE%3yQ1i'NS1iPE%3JRJ#PQ1m'pS1mPE%{J%0}#I'rS22PE%3^R^$0T/kvS23PE%3^R^#PR}/pPS24PE1r}xS25PE%{^R^/kvS26PEQ1|,r^S1|PEQ1c#LS1c#LR^#L%3~R~#b'NS27PE%{^%3~#`'kS28%0I#t$0r#t$0L#`R~%0g#bS29+0MRg&0bES2:5oEDFDFDFDFDFDFDFDFDFDFDFDFDFDFDFDFDFDFDFDFDFR^5oERvQ1Rp,3ILYS2;+1jJ0ZPbPwPNPXPwPNEzXDE>0;EvQ00PSP>P>PRC[12U>1<>VPWP>P>PTC[4051AL?#Z,qZP=PSP?P?PRC[Q1^$0FR}Q1^$07RP60pZB0Gi}PRPPEPiPwPNP[PwPNEzXDEQ1^P^P0I1i419PPP5PS17XaRP$001;APRPePP%?KRK,^{%6{%6KS2<1C{KRP#6[[P_PkPePj17{|Q1b+0oR^/^K%6^Q2<1C^KR}#6[[Q10Q121T{K%GKRJ$09S2=P{PKPP1D{KRyCJ[1Q{K&0HKRzAKyyK[1W{K1<K:S2>AUKyy[1S{K%GP\J1Y{K1;y{\JPPP2PyP21T^KQ2=P^PKP}1D^KRyCJ[1Q^KAKyyK\z1W^KQ2>AUKyy[1S^K%G}\J1Y^K1;y^\JP}P2PyP21ThfS2?%GfRy$09PhPf1ChfS2@PlCJ[S2A1QhfS2B&0HfS2CQ11?glf[S111WhfS2D1<f:AUfll[S2E1ShfS2FQ2@#G\yS2G1YhfS2H1;lh\yS2IQ2@P2PlP2Q01fUS2J#6Q2JfYS2K'<17ZQS2LPSPS17BQS2MCHfTfWS2N#6S2OfXS2Pf\S2Q'<S2RQ1500XpS2SQ1700nn+0KQ13#m&1fI-1e2S13Q1860l22172KQ1760k2S183y00gsS2T+0gPD20J2>S2U?O>q9Oq0Q1:?O>q?O3q7O6S2VPrPmPm%=KRy9~moS2WPFPm201m@&0:xS2X=~myEsS2YPFPmPmB15myo-14mS2ZPFPm%={S2[%=|'cQ1b#=S2\60q2Q1;-06yQ2X'cS2]EdPFPmPmQ2WPFPmQ1a$0:S1a9@moS2W201mAS2^EsS2_PFPmPmQ2ZPFPmQ2[206ytQ1a'cS2`EdPFPmQ1E201mB608mS2aPFPmQ1Y,ctS2bQ1<5@mQ1<Q1;Q1Y'cS1Y5@mEsFVFVPGP9b3b6b7X12X<2X=2X>2XA2X:;XB;XC;Ag?>K\zS2cg01WgS2d\JS2eB0jK3?S2f,;^[%6?S2g/5B\zS2hQ2eB0jK=@S2i,;{[Q1D@0`?dS2j17>QS2kPSPS17?QS2lCH[[[[[^12^<2^=2^>2^A2^:;^B;^C;P5Q1HfCS2m/<K%68P8Q2mPhP1fDR^PiP[fHS2nfIRyQ1JO=S2ob2WRWQP6P5O2n2001000000121000000b_b]bPbObNbMbWb^b\bVbUbTbSbJbLb[bIbHbGbFb@b4b5b;b?bKb917PQPSPS17}QCHeB0R{|SeO21ALSS2p#ZS2q,q[PS%h5,ALS2r1ALaS2s,lL#h,AL54MXE2PB%hSS2t,ALQ2r54MXE2P2PM&1bLS2uQ2uQ2t%hBS2vPM\2Q2u+0SS2w17ZdR|$001;B|S2xeS2yQ2xP_PkPePjQ05#L$0^S2z#?R|,^S%6SS2{%6|S2|1CS|S2}#6[[1^1|%61S2~Q2|1CX|#6[[Q10Q121TS|%G|R}$09S30PSP|Q2}1DS|RPCJ[1QS|&0H|RxAKPP|[1WS|1<|:S31AU|PP[1SS|Q2}#G\}1YS|1;PS\}Q2}P2PPP2Q1I/T|Q30fGRPP|1CP|1DP|CJ[1QP|Q2n/D|S2}Q2};K|\xQ2n/W|Q311Dy|S2}Q2}5U|[1Sy|fJS32/C|#G\}Q32/Y|fKS33/D|S34Q33';\}Q33/C|P2fLS35/D|P2Q2?Q2AQ2BQ11Q2DQ2EQ2FQ2GQ2HQ2IQ2@P2PlP2Q01fVS36#6Q36fZS37'<204Z|204B|';S38Q2JQ2P#6S2PQ2Kf]S2J'<Q2S2172|S39>0k2nS3:Q39Q1760k2S39Q14#e#eS14#eS17#e#mQ13Q14#mS1460l200Xp413+0n-0Kn+0KQ16Q13>0l2p+0XQ3:Q39Q17#mQ14Q15+0X413+0n-0Kn+0K<03sS3:PD20J2??O?q9Oq0Q2U?O?qQ1:7O37O6S1:PrPmPm%=|Rn9~moS2UPFPmQ2X9@moQ2X=~mnEsS39PFPmPmB15mno-14mS14PFPmQ0:$0:S0:Q1;-06nQ2X'cEdS2XPFPmPmQ2UPFPmQ2WQ1a=~mnEsS2WPFPmPmQ14PFPmQ1<206ntQ1a'cS1aEdPFPmPmPmQ1<Q0:PmQ0:Q1>FjPFPmQ1EQ2^608mPFPm206tnQ1;006nEdS1;CvFVFVPGP9b3b6b7X12X<2X=2X>2XA2XY2X:;Q2g?g?|\xS2gQ2d\}S2^P>P|P3P@CJ[S1EAK@@|\xS2UQ2^B0j|=AS17,;S[PSP@P@PRC[Q1D@0`@d204?|204@|';[S16[[[[[^12^<2^=2^>2^A2^Y2^:;P5Q1HP8Q2mQ2KPhP1P^PiP[Q2nPyfRS13Q1JO=b2WRWQP6P5O2n2001000000121000000b_b]bPbObNbMbWb^b\bVbUbTbSbJbLb[bIbHbGbFb@b4b5b;b?bKb9Q2tQ2v';eL0i1ALBS2v,lLQ2yQ2xP_PkPePjQ05#?S05-0~`S2tQ0|Q05#6Q05-10`Rn$0H[[S0|Q0}Q0~Q05>11`6UWaS05Q0}Q0~%6n[]aS0}PsPDQ1UPrPmQ1VPFPmA@motS1VPm%=`>1a2LS0~-0QtCiS2SCvPGP9b3b6b7X12Q1LQ1G?g6nS3;[^12P5PXPAO2b2b4b5b;b?b9-0BBDxQ2p,lLQ2yQ2xP_PkPePjQ2tQ0|Q05Q0}PsPDPqPrPmPmPoQ1<PmQ1<Q0~FjPGP9b3b6b7Q2{?gSnP5b2b4b5b;b?b9-0BSDxQ2qQ2v#Z54MRtePtPMQ2q1qc5XZMP6Q2s#ZP5J0Zb@bXbXWbP5O112U?1<?VPWP?P?PTC[405Q00PUP@P@PVC[S00PWP@P@PTC[S2s1ALA#Z,q[P5PUPAPAPVC[&0FgR@&07gRt60p[Q2m@0G@tS2qQ2mPwPNP^PwPNEzXDERt>0;EvB12E5vR@Q1IPwPNPPPwPNEzXDEP6O1[^`E[PcPwPNQ1IPwPNEzXDEP6O1\@^`EP^PwPNPcPwPNEzXDE>0;Ev[B1`EtvP=PgQ1D/2hS1DQ1HQ1^=4EgS1^Q1_=4EgS1_Q1`=4EgS1`Q1d=4EgS1dQ1e=4EgS1eQ1f=4EgS1fQ1g=4EgS1gQ1h=4EgS1hQ1k=4EgS1kQ1j=4EgS1jQ1q=4EgS1qQ1o=4EgS1oQ1s=4EgS1sQ1p=4EgS1pQ1r=4EgS1rQ1t=4EgS1tQ1n=4EgS1nQ1u=4EgS1uQ1Z=4EgS1ZQ0{=4EgS0{Q1y=4EgS1yQ1x=4EgS1xQ1z=4EgS1zQ1{=4EgS1{Q1}=4EgS1}Q1~=4EgS1~Q1w=4EgS1wQ20=4EgS20Q1l=4EgS1lQ1v=4EgS1vQ04=4EgS04Q21=4EgS21Q0;=4EgS0;Q1i=4EgS1iQ1m=4EgS1mQ22=4EgS22Q23=4EgS23Q24=4EgS24Q25=4EgS25Q26=4EgS26Q1|=4EgS1|Q27=4EgS27Q28=4EgS28A4EggS2vQ2d'1Rt'1S2{'1S1<'1S2p'1S1L'1S3<'1S3='1S3>'1S3?'1S3@'1S3A'1S3B'1S3C'1S3D'1S3E'1S3F'1S3G'1S3H'1S3I'1S3J'1S3K'1S3L'1S3M'1S3N'1S3O'1S3P'1S3Q'1S3R'1S3S'1S3T'1S3U'1S3V'1S3W'1S3X'1S3Y'1S3Z'1S3['1S3\'1S3]'1S3^'1S3_'1S3`'1S3a'1R@Q1DQ1HQ2~1<1iP@Q2~1<b[12U1R`1<1VP@1<bVQ1^Q3aQ1_Q3`Q1`Q3_Q1dQ3^Q1eQ3]Q1fQ3\Q1gQ3[Q1hQ3ZQ1kQ3YQ1jQ3XQ1qQ3WQ1oQ3VQ1sQ3UQ1pQ3TQ1rQ3SQ1tQ3RQ1nQ3QQ1uQ3PQ1ZQ3OQ0{Q3NQ1yQ3MQ1xQ3LQ1zQ3KQ1{Q3JQ1}Q3IQ1~Q3HQ1wQ3GQ20Q3FQ1lQ3EQ1vQ3DQ04Q3CQ21Q3BQ0;Q3AQ1iQ3@Q1mQ3?Q22Q3>Q23Q3=Q24Q3<Q25Q1LQ26Q2pQ1|Q1<Q27Q2{Q28Q2vQ2d20SEg40u80htDEDEDEDEDEDEDEDEDEDEDEDEDEDEDEDEDEDEDEDEDEWJXI`P=I0cWHWGP8I0cWFW@Q1JI0cB12EgveJ1_419Q2qP5PU17i8Rv$001;avRvePv1^~K%6~Q2<1C~KRv#6[[P_PkPePjQ29,7~Q1b+0oRg/^K%6gQ2<1CgKRt#6[[Q10Q121T~KQ2=P~PKPv1D~KR@CJ[1Q~KAK@@K\z1W~KQ2>AUK@@[1S~K%Gv\J1Y~K1;@~\JPvP2P@P21TgKQ2=PgPKPt1DgKR@CJ[1QgKAK@@K\z1WgKQ2>AUK@@[1SgK%Gt\J1YgK1;@g\JPtP2P@P2Q2?Q2AQ2BQ11Q2DQ2EQ2FQ2GQ2HQ2IQ2@P2PlP2Q01Q2OQ2Nf[R@'<Q2LPUPUQ2MCHQ36Q2K#6Q37f^S2K'<Q15Q187ypQ2T+0gS2TPDQ2VPrPmQ2YPFPmPmQ2ZPFPm%=~S18Q29#='cQ2\60q2Q2]EdPFPmQ2_PFPmPmQ2ZPFPmQ18Q2`EdPFPmQ2aPFPmQ2bQ1?5@mQ1?Q1Y5@mEsFVFVPGP9b3b6b7X12X<2X=2X>2XA2X:;XB;XC;Q2cQ2eQ2f,;g[Q2hQ2eQ2i,;~[Q2jQ2kPUPUQ2lCH[[[[[^12^<2^=2^>2^A2^:;^B;^C;Q2ob2WRWQP6P5O2n2001000000121000000b_b]bPbObNbMbWb^b\bVbUbTbSbJbLb[bIbHbGbFb@b4b5b;b?bKb917vQPUPU17tQCHeQ29>0R~UeO21ALUS29#ZS15,q^PUQ2r1AL8S2O,lL#h,AL54MXE2Pd%hURt,ALQ2r54MXE2P2PMQ2uQ2uPt%hdS2qQ2w17[1Rv$001;dvRveS1DPvP_PkPePj1^U|%6US2~Q2|1CU|Rg#6[[1^X|%6XQ2|1Ci|#6[[Q10Q121TU|Q30PUP|Pg1DU|RpCJ[1QU|AKpp|\x1WU|Q31AU|pp[1SU|%Gg\}1YU|1;pU\}PgP2PpP2Q2n/T|Q30PyP|1Cy|Q2}CJ[1Qy|Q32/D|Rp?Kp|\xQ32/W|Q31Q34Q345U|[Q33/S|Q35/C|#G\}Q35/Y|fMRp/D|S34/;p\}1Cp|S32P2fNS2}/D|S28P2Q2?Q2AQ2BQ11Q2DQ2EQ2FQ2GQ2HQ2IQ2@P2PlP2Q01Q2PQ2RQ38Q2NQ37#6f_S2N,<@S2RQ3:PDQ1:PrPmQ39PFPmQ2XPFPmQ2WPFPmPmQ14PFPmQ1?Q1aEdPFPmPmPmQ1?Q0:PmQ0:Q1AFjPFQ1;CvFVFVPGP9b3b6b7X12X<2X=2X>2XA2XY2X:;Q2gQ1EQ2UQ2^Q17,;U[Q00Q16[[[[[^12^<2^=2^>2^A2^Y2^:;P5Q1HP8Q2mP@PhP1P^PiP[Q2nPyQ13Q1JO=b2WRWQP6P5O2n2001000000121000000b_b]bPbObNbMbWb^b\bVbUbTbSbJbLb[bIbHbGbFb@b4b5b;b?bKb9Q2q,;teL0i1ALdRt,lLQ1DPvP_PkPePjQ2tQ0|Q05Q0}PsPDQ1UPrPmQ1WPFQ2SCvPGP9b3b6b7X12Q1NQ3;[^12P5PiPAO2b2b4b5b;b?b9-0BdDxQ29,lLQ1DPvP_PkPePjQ2tQ0|Q05Q0}PsPDPqPrPmPmPoQ1?PmQ1?Q0~FjPGP9b3b6b7Q2~?gUnP5b2b4b5b;b?b9-0BUDxQ15%ZtS2~54MRtePtPMQ151qP5XZMP6Q2O#ZP5J0Zb@bXbXWbP5O1PWPAPAPTC[Q1QQ07Q1RQ1SQ08Q1TQ1IQ0<PcP^Q2mP[&0UiP8&0[I$0_#a#I$0L#`RAPfQ2z#0#`Rt125AXE2Q2yQ2xP_PkPePjPsPDPqPr%=t%=ARv5@mPGP9b3b6b712tAP5b2b4b5b9Q1Q$1^Q1QQ07Q1RQ09p,2DLS2zI1[Dx%3I$0V#{#I#L#}#`S0<17AfRt/25XE2Q2yQ2xP_PkPePjPsPDPqPr%=fS1T,cvRgQ0<#=5@mPGP9b3b6b7Q0<,2tP5b2b4b5b9Q1Q$1ZQ1QQ07Q1RQ09Q2zI1YDxQ2yQ2xP_PkPePjPsPDPqPrQ1T9~moPGP9b3b6b7Q2CP5b2b4b5b9Q03Q1c#3#P$0L#`S1c-0M{S2C&0[I$0|#t#I$0L#`S1T-0M~S2z&0[I#I#P#I#a$0L#`S0900MARIQ2:5oES075oES1Q5oEQ0312tw12NA'1XLERN>0;E5WePEPNQ2CQ1QQ2yQ2xP_PkPePjPsPDPqPrQ2[9@mgQ1c#==@mv5RmPGP9b3b6b712t{Q1c/2A'1P5b2b4b5b9Q2C$0F,2tQ2C$07/2A'1ePEPNQ2zQ07Q2yQ2xP_PkPePjPsPDPqPrQ189@mgQ1T#==@mv5RmPGP9b3b6b712t~Q1T/2A'1P5b2b4b5b9Q2z$0F,2tQ2z$07/2A'1ePEPNPIQ2:Q2yQ2xP_PkPePjPsPDPqPrQ09#=9@mgA@mvv5RmPGP9b3b6b7Q09,2t12AA'1P5b2b4b5b9&0FI,2t&07I/2A'1e21XENJ0fJ0fJ0fQ1R$1WQ1RQ2;+1UJ0dND1TB0RAf5RNB0e^6:[^`2Q2mPAPfH1SQ01B0ec6:\N^`2B0G^AfQ2~,qcP5B0eP6:\N^`2B0GPAfP5PT17cZRP$001;bPRPePP1^AK%6AQ2<1CAKRP#6[[P_PkPePjQ1b-0otRt/^K%6tQ2<1CtKRN#6[[Q10Q121TAKQ2=PAPKPP1DAKR:CJ[1QAKAK::K\z1WAKQ2>AUK::[1SAK%GP\J1YAK1;:A\JPPP2P:P21TtKQ2=PtPKPN1DtKR:CJ[1QtKAK::K\z1WtKQ2>AUK::[1StK%GN\J1YtK1;:t\JPNP2P:P2Q2?Q2AQ2BQ11Q2DQ2EQ2FQ2GQ2HQ2IQ2@P2PlP2Q01%6@Q2RQ2LPTPTQ2MCHQ37Q2J#6Q2Kfb'<Q2TPDQ2VPrPmQ2YPFPmPmQ2ZPFPmQ2\:0q2gQ2]EdPFPmQ2_PFPmPmQ2ZPFPmPvQ2`EdPFPmQ2aPFPmQ2b=@muQ1Y9@muEsFVFVPGP9b3b6b7X12X<2X=2X>2XA2X:;XB;XC;Q2cQ2eQ2f,;t[Q2hQ2eQ2i,;A[Q2jQ2kPTPTQ2lCH[[[[[^12^<2^=2^>2^A2^:;^B;^C;Q2ob2WRWQP6P5O2n2001000000121000000b_b]bPbObNbMbWb^b\bVbUbTbSbJbLb[bIbHbGbFb@b4b5b;b?bKb917PQPTPT17NQCHeB0RAfTeO2Q2n1ALTRA#ZRf'qPTQ2r1ALZRZ,lL#h,AL54MXE2PX%hTRN,ALQ2r54MXE2P2PMQ2uQ2uPN%hXRQQ2wQ1I/7iRP$001;XPRPeRtPPP_PkPePj1^[|%6[Q2|1C^|#6[[1^T|%6TRvQ2|1CT|Rg#6[[Q10Q121TT|Q30PTP|Pg1DT|R:CJ[1QT|AK::|\x1WT|Q31AU|::[1ST|%Gg\}1YT|1;:T\}PgP2P:P2Q35/T|Q30PpP|Q32Q34CJ[1Qp|Q28Q28;K|\xQ2}/W|Q31fORx/D|Rp=U|p[1Sx|fPRx/C|#G\}1Yx|fQRx/D|/;x\}1Cx|P2Q13/D|P2Q2?Q2AQ2BQ11Q2DQ2EQ2FQ2GQ2HQ2IQ2@P2PlP2Q01Q2Q#6Q2Qf`'<Q38P@Q2K#6Q2Nfc'<Q3:PDQ1:PrPmQ39PFPmQ2XPFPmQ2WPFPmPmQ14PFPmPuQ1aEdPFPmPmPmQ1BQ0:PmQ0:PuFjPFQ1;CvFVFVPGP9b3b6b7X12X<2X=2X>2XA2XY2X:;Q2gQ1EQ2UQ2^Q17,;T[Q2sQ16[[[[[^12^<2^=2^>2^A2^Y2^:;P5Q1HP8Q2mQ2NPhP1P^PiP[Q2nPyQ36Q1JO=b2WRWQP6P5O2n2001000000121000000b_b]bPbObNbMbWb^b\bVbUbTbSbJbLb[bIbHbGbFb@b4b5b;b?bKb91;NQeL0i1ALXRQ,lLPtPPP_PkPePjQ2tQ0|Q05Q0}PsPDQ1UPrPmQ1XPFQ2SCvPGP9b3b6b7X12Q1PQ3;[^12P5PcP8O2b2b4b5b;b?b9-0BXDx1lLAPtPPP_PkPePjQ2tQ0|Q05Q0}PsPDPqPrPmPmPoPuPmPuQ0~FjPGP9b3b6b7AgvTnP5b2b4b5b;b?b9-0BTDx%ZQ94MfRQePQPMPfQ33/q5XZMP6%ZZP5J0Zb@bXWXWoP6P5O2n2001000000121000000bqWbP5O1n200100000021100011000W@P5O1n200100000021100011000bdbdO2b@41VQ1\:0}8a$0\RZePZP4Q02Q06P4Q06P5Q1[P11AL=O1n0100000020000Q1[34$09XZ4P6Q1]:0}1dP5J0dQ0620w1dQ1]81Q8Q1[34$09ebnbhbbb`WjXs2Q0=@1P=3ePSP=17=3R4PRCfPUP=P4PVCf'\RLPWP=P4PTCfR4'\#:%:L%:4'1RZ'BPSP>17>=RMPRCfRfPUP>PMPVCfRQ'\RvPWP>PMPTCfRM'\#:%:vRv%:MRM'1<0v5W820PL4P6O2R4PZ%:f%:Q'1RL,BvPCPYP<P]19S?Rv17?>Ro/9RRP'nRtPUP?PoPVCfRA'\#:%:tRt%:ARA'1P519W?19oT'wRoPo187oM:MW820PfQP5O2RQ11LMRL1_vPRM,BtPCPYP<P]Q0@#:RtQ0C#:Rf'1Q0>Q0?'_RN/1fPtPNP5PfPf187fJ0EQ0DQ0DQ0D,87M:MW820DvPP5O2RPAXMAoRMQ0AQ0B'_Ro,BfPCPYP<P]Q0EQ0F'_RfQ0L'1Q0GQ0H'_RA,1fRvP\POPf187fQ0LPAP5K0CQ0KQ0KQ0K,87M:MW8Q0AQ0B+0DP5O2RAQ0D9XNoRoQ0KQ0IQ0J'_RN'BP\Q0MQ0dQ0UQ0NQ0O'_Rf'1Rt187tQ0RQ0PQ0Q'_RtP5L0@W8Q0IQ0J+0DP5O2Ry11vNRNQ0S12SBRv'BPCPYP<P]Q0b12SaRaQ0X'5RiQ0\'1Q0YPiQ0WPaP5Q0XQ0XQ0X,87J0<Q0\Q0\Q0\,87J0EQ0ZQ0['_RiPi187iM:MW81]SBP5O2RBQ0T,5v?XftRtQ0XQ0V/2RRf'BPCPYP<P]12SdRvQ0^'5RhQ0a'1Q0]/2RR@,5vRlQ0a'1PhPlP\POPv187vQ0^P@P5K0?Q0aQ0aQ0a,87J0EQ0cQ0cQ0c,87M:MW8Q0V/]RP5O2R@15afQ0\;XiRiQ0_12UdRf'BPCPYP<P]Q0jQ0e<0WRRaQ0h'112U8R8Q0g'5Rv,1aP\POPa187aQ0hPvQ0fP8P5Q0gQ0gQ0g,87J0<K0CQ0iQ0iQ0i,87M:MW81]UdP5O2RdQ0`,5fQ0c5XlRlQ0gQ0e/2VRf'BPCPYP<P]Q0vQ0l,5`R]'1Q0vQ0k/2VR<,5`RY'1RCP\POQ0vQ0v,87P]PYP\POP`187`Q0lP<P5K0?K0CQ0oQ0oQ0pM:MW8Q0e/]VP5O2R<158fQ0i5XaRaQ0m12W1Rf'BP\Q0MQ0dQ0rQ0wQ0q/2V40>R81878Q0u12WbRbQ0t'5Q0sPbP5Q0tQ0tQ0t,87J0<L0@W81]W1P5O2R1Q0n:0>CfRfQ0tQ0q/2TRC'BP\Q0MQ0dQ0zQ0z,8712WXRXQ0y'5Q0x/2TR`,5XP\POPX187XQ0yP`P5K0?L0@W8Q0q/]TP5O2R`B0>8bCRCP_PkPePjQ10Q12PsPDQ1UPrPmQ1=201m3608mQ1@201m=Rb608m5RmQ1C201m>R>608m5RmPFQ1VCvPGP9b3b6b7X12X:;XB;XC;Q1K/56Q1M/50Q1O/533XQ1G[^12^:;^B;^C;P5Q2m/7[R[/2T12[V12[RQ2mP=O5b2b4b5b;b0b0b0b0b0b0b0b0b0b0b0P4PZPQPLPPPMPAPoPyPNPBPtP@PiPdPlP<PaP1PfP`PCP_PkPePjQ2tQ0|Q05Q0}Q10Q12PsPDQ19?O6qPrPmPmPbPmQ1>-02HCiPmP>PmQ1A-02HCi5RmPmQ1FPm202HuCi5RmPFPmQ0~-02HI1OPGP9b3b6b7X12X<2X:;XB;XC;1756R9>0W0RB0W39VB0W=9T3X1760/2n[^12^<2^:;^B;^C;P512Wc12Uc12ScP^PcP?O6b2b4b5b;b?bKb0b0b0b0b0b0b0b0b0b0b0K1\biW0WgXu2Xp2WtWmWcWrWlWko"). Qed.

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
    /\ (forall i, 65536 <= i < 1409024 -> MV (Z_to_bv 64 i) = None)
    /\ exitA tid MV.
  Definition exit_preE (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1409024 -> MV (Z_to_bv 64 i) = None)
    /\ exitE tid MV.

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_0 : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1275140 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6896384 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x137cc8) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
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
    assert (SHW : forall a n, ((2147469128 <=? a) && (a + n <=? 2147470932) || (2147623588 <=? a) && (a + n <=? 2147623604) || (2147628820 <=? a) && (a + n <=? 2147629172)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x15b8a0 <=? a) && (a + Z.of_nat n <=? 0x15c3a0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpX.dpX_conc fx R MV V
           HS64 HT64 G1 G2 G4 HSr HSa CWR CDF IMGc (WSG 1426368 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1426448 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 1430320 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027536 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027544 4%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 7027552 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7028080 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147469128 1 eq_refl) (SHW 2147469129 1 eq_refl)
           (SHW 2147469130 1 eq_refl) (SHW 2147469131 1 eq_refl) (SHW 2147469132 1 eq_refl) (SHW 2147469132 4 eq_refl) (SHW 2147469133 1 eq_refl) (SHW 2147469134 1 eq_refl)
           (SHW 2147469135 1 eq_refl) (SHW 2147469136 4 eq_refl) (SHW 2147469140 1 eq_refl) (SHW 2147469140 4 eq_refl) (SHW 2147469141 1 eq_refl) (SHW 2147469142 1 eq_refl)
           (SHW 2147469143 1 eq_refl) (SHW 2147469148 1 eq_refl) (SHW 2147469149 1 eq_refl) (SHW 2147469150 1 eq_refl) (SHW 2147469151 1 eq_refl) (SHW 2147469152 1 eq_refl)
           (SHW 2147469152 4 eq_refl) (SHW 2147469153 1 eq_refl) (SHW 2147469154 1 eq_refl) (SHW 2147469155 1 eq_refl) (SHW 2147469156 4 eq_refl) (SHW 2147469160 1 eq_refl)
           (SHW 2147469160 4 eq_refl) (SHW 2147469161 1 eq_refl) (SHW 2147469162 1 eq_refl) (SHW 2147469163 1 eq_refl) (SHW 2147469164 1 eq_refl) (SHW 2147469165 1 eq_refl)
           (SHW 2147469166 1 eq_refl) (SHW 2147469167 1 eq_refl) (SHW 2147469168 1 eq_refl) (SHW 2147469169 1 eq_refl) (SHW 2147469170 1 eq_refl) (SHW 2147469171 1 eq_refl)
           (SHW 2147469172 1 eq_refl) (SHW 2147469173 1 eq_refl) (SHW 2147469174 1 eq_refl) (SHW 2147469175 1 eq_refl) (SHW 2147469188 1 eq_refl) (SHW 2147469189 1 eq_refl)
           (SHW 2147469190 1 eq_refl) (SHW 2147469191 1 eq_refl) (SHW 2147469192 1 eq_refl) (SHW 2147469193 1 eq_refl) (SHW 2147469194 1 eq_refl) (SHW 2147469195 1 eq_refl)
           (SHW 2147469196 1 eq_refl) (SHW 2147469196 4 eq_refl) (SHW 2147469197 1 eq_refl) (SHW 2147469198 1 eq_refl) (SHW 2147469199 1 eq_refl) (SHW 2147469200 4 eq_refl)
           (SHW 2147469204 4 eq_refl) (SHW 2147469208 4 eq_refl) (SHW 2147469212 4 eq_refl) (SHW 2147469216 4 eq_refl) (SHW 2147469220 4 eq_refl) (SHW 2147469224 8 eq_refl)
           (SHW 2147469232 8 eq_refl) (SHW 2147469240 8 eq_refl) (SHW 2147469248 8 eq_refl) (SHW 2147469256 8 eq_refl) (SHW 2147469264 8 eq_refl) (SHW 2147469272 8 eq_refl)
           (SHW 2147469280 8 eq_refl) (SHW 2147469288 8 eq_refl) (SHW 2147469296 8 eq_refl) (SHW 2147469304 8 eq_refl) (SHW 2147469312 8 eq_refl) (SHW 2147469320 8 eq_refl)
           (SHW 2147469328 8 eq_refl) (SHW 2147469336 8 eq_refl) (SHW 2147469344 8 eq_refl) (SHW 2147469352 8 eq_refl) (SHW 2147469360 8 eq_refl) (SHW 2147469368 8 eq_refl)
           (SHW 2147469376 8 eq_refl) (SHW 2147469384 8 eq_refl) (SHW 2147469392 8 eq_refl) (SHW 2147469400 8 eq_refl) (SHW 2147469408 8 eq_refl) (SHW 2147469416 8 eq_refl)
           (SHW 2147469424 8 eq_refl) (SHW 2147469432 8 eq_refl) (SHW 2147469440 8 eq_refl) (SHW 2147469448 8 eq_refl) (SHW 2147469456 8 eq_refl) (SHW 2147469464 8 eq_refl)
           (SHW 2147469472 8 eq_refl) (SHW 2147469480 8 eq_refl) (SHW 2147469488 8 eq_refl) (SHW 2147469496 8 eq_refl) (SHW 2147469504 8 eq_refl) (SHW 2147469512 8 eq_refl)
           (SHW 2147469520 8 eq_refl) (SHW 2147469528 8 eq_refl) (SHW 2147469536 8 eq_refl) (SHW 2147469544 8 eq_refl) (SHW 2147469552 8 eq_refl) (SHW 2147469560 8 eq_refl)
           (SHW 2147469568 8 eq_refl) (SHW 2147469576 8 eq_refl) (SHW 2147469584 8 eq_refl) (SHW 2147469592 8 eq_refl) (SHW 2147469600 8 eq_refl) (SHW 2147469608 8 eq_refl)
           (SHW 2147469616 8 eq_refl) (SHW 2147469624 8 eq_refl) (SHW 2147469632 8 eq_refl) (SHW 2147469640 8 eq_refl) (SHW 2147469648 8 eq_refl) (SHW 2147469656 8 eq_refl)
           (SHW 2147469664 8 eq_refl) (SHW 2147469672 8 eq_refl) (SHW 2147469680 8 eq_refl) (SHW 2147469688 8 eq_refl) (SHW 2147469696 8 eq_refl) (SHW 2147469704 8 eq_refl)
           (SHW 2147469712 8 eq_refl) (SHW 2147469720 8 eq_refl) (SHW 2147469728 8 eq_refl) (SHW 2147469736 8 eq_refl) (SHW 2147469744 8 eq_refl) (SHW 2147469752 8 eq_refl)
           (SHW 2147469760 8 eq_refl) (SHW 2147469768 8 eq_refl) (SHW 2147469776 8 eq_refl) (SHW 2147469784 8 eq_refl) (SHW 2147469792 8 eq_refl) (SHW 2147469800 8 eq_refl)
           (SHW 2147469808 8 eq_refl) (SHW 2147469816 8 eq_refl) (SHW 2147469824 8 eq_refl) (SHW 2147469832 8 eq_refl) (SHW 2147469840 8 eq_refl) (SHW 2147469848 8 eq_refl)
           (SHW 2147469856 8 eq_refl) (SHW 2147469864 8 eq_refl) (SHW 2147469872 8 eq_refl) (SHW 2147469880 8 eq_refl) (SHW 2147469888 8 eq_refl) (SHW 2147469896 8 eq_refl)
           (SHW 2147469904 8 eq_refl) (SHW 2147469912 8 eq_refl) (SHW 2147469920 8 eq_refl) (SHW 2147469928 8 eq_refl) (SHW 2147469936 8 eq_refl) (SHW 2147469944 8 eq_refl)
           (SHW 2147469952 8 eq_refl) (SHW 2147469960 8 eq_refl) (SHW 2147469968 8 eq_refl) (SHW 2147469976 8 eq_refl) (SHW 2147469984 8 eq_refl) (SHW 2147469992 8 eq_refl)
           (SHW 2147470000 8 eq_refl) (SHW 2147470008 8 eq_refl) (SHW 2147470016 8 eq_refl) (SHW 2147470024 4 eq_refl) (SHW 2147470028 4 eq_refl) (SHW 2147470032 4 eq_refl)
           (SHW 2147470036 4 eq_refl) (SHW 2147470040 4 eq_refl) (SHW 2147470044 4 eq_refl) (SHW 2147470048 1 eq_refl) (SHW 2147470048 4 eq_refl) (SHW 2147470049 1 eq_refl)
           (SHW 2147470050 1 eq_refl) (SHW 2147470051 1 eq_refl) (SHW 2147470052 1 eq_refl) (SHW 2147470052 4 eq_refl) (SHW 2147470053 1 eq_refl) (SHW 2147470054 1 eq_refl)
           (SHW 2147470055 1 eq_refl) (SHW 2147470056 4 eq_refl) (SHW 2147470060 4 eq_refl) (SHW 2147470064 4 eq_refl) (SHW 2147470068 4 eq_refl) (SHW 2147470072 4 eq_refl)
           (SHW 2147470076 4 eq_refl) (SHW 2147470080 8 eq_refl) (SHW 2147470088 8 eq_refl) (SHW 2147470096 8 eq_refl) (SHW 2147470104 8 eq_refl) (SHW 2147470112 8 eq_refl)
           (SHW 2147470120 8 eq_refl) (SHW 2147470128 8 eq_refl) (SHW 2147470136 8 eq_refl) (SHW 2147470144 8 eq_refl) (SHW 2147470152 8 eq_refl) (SHW 2147470160 8 eq_refl)
           (SHW 2147470168 8 eq_refl) (SHW 2147470176 8 eq_refl) (SHW 2147470184 8 eq_refl) (SHW 2147470192 8 eq_refl) (SHW 2147470200 8 eq_refl) (SHW 2147470208 8 eq_refl)
           (SHW 2147470216 8 eq_refl) (SHW 2147470224 8 eq_refl) (SHW 2147470232 8 eq_refl) (SHW 2147470240 8 eq_refl) (SHW 2147470248 8 eq_refl) (SHW 2147470256 8 eq_refl)
           (SHW 2147470264 8 eq_refl) (SHW 2147470272 8 eq_refl) (SHW 2147470280 8 eq_refl) (SHW 2147470288 8 eq_refl) (SHW 2147470296 8 eq_refl) (SHW 2147470304 8 eq_refl)
           (SHW 2147470312 8 eq_refl) (SHW 2147470320 8 eq_refl) (SHW 2147470328 8 eq_refl) (SHW 2147470336 8 eq_refl) (SHW 2147470344 8 eq_refl) (SHW 2147470352 8 eq_refl)
           (SHW 2147470360 8 eq_refl) (SHW 2147470368 8 eq_refl) (SHW 2147470376 8 eq_refl) (SHW 2147470384 8 eq_refl) (SHW 2147470392 8 eq_refl) (SHW 2147470400 8 eq_refl)
           (SHW 2147470408 8 eq_refl) (SHW 2147470416 8 eq_refl) (SHW 2147470424 8 eq_refl) (SHW 2147470432 8 eq_refl) (SHW 2147470440 8 eq_refl) (SHW 2147470448 8 eq_refl)
           (SHW 2147470452 4 eq_refl) (SHW 2147470456 4 eq_refl) (SHW 2147470456 8 eq_refl) (SHW 2147470460 4 eq_refl) (SHW 2147470464 4 eq_refl) (SHW 2147470468 4 eq_refl)
           (SHW 2147470472 4 eq_refl) (SHW 2147470476 1 eq_refl) (SHW 2147470476 4 eq_refl) (SHW 2147470477 1 eq_refl) (SHW 2147470478 1 eq_refl) (SHW 2147470479 1 eq_refl)
           (SHW 2147470480 1 eq_refl) (SHW 2147470481 1 eq_refl) (SHW 2147470482 1 eq_refl) (SHW 2147470483 1 eq_refl) (SHW 2147470484 1 eq_refl) (SHW 2147470484 4 eq_refl)
           (SHW 2147470485 1 eq_refl) (SHW 2147470486 1 eq_refl) (SHW 2147470487 1 eq_refl) (SHW 2147470488 4 eq_refl) (SHW 2147470492 4 eq_refl) (SHW 2147470496 1 eq_refl)
           (SHW 2147470496 4 eq_refl) (SHW 2147470497 1 eq_refl) (SHW 2147470498 1 eq_refl) (SHW 2147470499 1 eq_refl) (SHW 2147470500 1 eq_refl) (SHW 2147470501 1 eq_refl)
           (SHW 2147470502 1 eq_refl) (SHW 2147470503 1 eq_refl) (SHW 2147470504 1 eq_refl) (SHW 2147470505 1 eq_refl) (SHW 2147470506 1 eq_refl) (SHW 2147470507 1 eq_refl)
           (SHW 2147470508 1 eq_refl) (SHW 2147470509 1 eq_refl) (SHW 2147470510 1 eq_refl) (SHW 2147470511 1 eq_refl) (SHW 2147470512 1 eq_refl) (SHW 2147470513 1 eq_refl)
           (SHW 2147470514 1 eq_refl) (SHW 2147470515 1 eq_refl) (SHW 2147470516 1 eq_refl) (SHW 2147470517 1 eq_refl) (SHW 2147470518 1 eq_refl) (SHW 2147470519 1 eq_refl)
           (SHW 2147470540 1 eq_refl) (SHW 2147470541 1 eq_refl) (SHW 2147470542 1 eq_refl) (SHW 2147470543 1 eq_refl) (SHW 2147470588 1 eq_refl) (SHW 2147470589 1 eq_refl)
           (SHW 2147470590 1 eq_refl) (SHW 2147470591 1 eq_refl) (SHW 2147470592 1 eq_refl) (SHW 2147470593 1 eq_refl) (SHW 2147470594 1 eq_refl) (SHW 2147470595 1 eq_refl)
           (SHW 2147470596 1 eq_refl) (SHW 2147470597 1 eq_refl) (SHW 2147470598 1 eq_refl) (SHW 2147470599 1 eq_refl) (SHW 2147470600 1 eq_refl) (SHW 2147470601 1 eq_refl)
           (SHW 2147470602 1 eq_refl) (SHW 2147470603 1 eq_refl) (SHW 2147470604 1 eq_refl) (SHW 2147470605 1 eq_refl) (SHW 2147470606 1 eq_refl) (SHW 2147470607 1 eq_refl)
           (SHW 2147470608 1 eq_refl) (SHW 2147470608 4 eq_refl) (SHW 2147470609 1 eq_refl) (SHW 2147470610 1 eq_refl) (SHW 2147470611 1 eq_refl) (SHW 2147470612 4 eq_refl)
           (SHW 2147470616 1 eq_refl) (SHW 2147470616 4 eq_refl) (SHW 2147470617 1 eq_refl) (SHW 2147470618 1 eq_refl) (SHW 2147470619 1 eq_refl) (SHW 2147470620 1 eq_refl)
           (SHW 2147470620 4 eq_refl) (SHW 2147470621 1 eq_refl) (SHW 2147470622 1 eq_refl) (SHW 2147470623 1 eq_refl) (SHW 2147470624 4 eq_refl) (SHW 2147470628 1 eq_refl)
           (SHW 2147470628 4 eq_refl) (SHW 2147470629 1 eq_refl) (SHW 2147470630 1 eq_refl) (SHW 2147470631 1 eq_refl) (SHW 2147470632 1 eq_refl) (SHW 2147470632 4 eq_refl)
           (SHW 2147470633 1 eq_refl) (SHW 2147470634 1 eq_refl) (SHW 2147470635 1 eq_refl) (SHW 2147470636 4 eq_refl) (SHW 2147470640 1 eq_refl) (SHW 2147470640 4 eq_refl)
           (SHW 2147470641 1 eq_refl) (SHW 2147470642 1 eq_refl) (SHW 2147470643 1 eq_refl) (SHW 2147470644 1 eq_refl) (SHW 2147470644 4 eq_refl) (SHW 2147470645 1 eq_refl)
           (SHW 2147470646 1 eq_refl) (SHW 2147470647 1 eq_refl) (SHW 2147470648 4 eq_refl) (SHW 2147470652 1 eq_refl) (SHW 2147470652 4 eq_refl) (SHW 2147470653 1 eq_refl)
           (SHW 2147470654 1 eq_refl) (SHW 2147470655 1 eq_refl) (SHW 2147470656 1 eq_refl) (SHW 2147470656 4 eq_refl) (SHW 2147470657 1 eq_refl) (SHW 2147470658 1 eq_refl)
           (SHW 2147470659 1 eq_refl) (SHW 2147470660 4 eq_refl) (SHW 2147470664 1 eq_refl) (SHW 2147470664 4 eq_refl) (SHW 2147470665 1 eq_refl) (SHW 2147470666 1 eq_refl)
           (SHW 2147470667 1 eq_refl) (SHW 2147470668 1 eq_refl) (SHW 2147470668 4 eq_refl) (SHW 2147470669 1 eq_refl) (SHW 2147470670 1 eq_refl) (SHW 2147470671 1 eq_refl)
           (SHW 2147470672 4 eq_refl) (SHW 2147470676 1 eq_refl) (SHW 2147470676 4 eq_refl) (SHW 2147470677 1 eq_refl) (SHW 2147470678 1 eq_refl) (SHW 2147470679 1 eq_refl)
           (SHW 2147470680 1 eq_refl) (SHW 2147470680 4 eq_refl) (SHW 2147470681 1 eq_refl) (SHW 2147470682 1 eq_refl) (SHW 2147470683 1 eq_refl) (SHW 2147470684 4 eq_refl)
           (SHW 2147470688 4 eq_refl) (SHW 2147470692 1 eq_refl) (SHW 2147470692 4 eq_refl) (SHW 2147470693 1 eq_refl) (SHW 2147470694 1 eq_refl) (SHW 2147470695 1 eq_refl)
           (SHW 2147470696 1 eq_refl) (SHW 2147470697 1 eq_refl) (SHW 2147470698 1 eq_refl) (SHW 2147470699 1 eq_refl) (SHW 2147470700 1 eq_refl) (SHW 2147470701 1 eq_refl)
           (SHW 2147470702 1 eq_refl) (SHW 2147470703 1 eq_refl) (SHW 2147470704 1 eq_refl) (SHW 2147470705 1 eq_refl) (SHW 2147470706 1 eq_refl) (SHW 2147470707 1 eq_refl)
           (SHW 2147470708 1 eq_refl) (SHW 2147470709 1 eq_refl) (SHW 2147470710 1 eq_refl) (SHW 2147470711 1 eq_refl) (SHW 2147470712 1 eq_refl) (SHW 2147470712 4 eq_refl)
           (SHW 2147470713 1 eq_refl) (SHW 2147470714 1 eq_refl) (SHW 2147470715 1 eq_refl) (SHW 2147470716 4 eq_refl) (SHW 2147470720 1 eq_refl) (SHW 2147470720 4 eq_refl)
           (SHW 2147470721 1 eq_refl) (SHW 2147470722 1 eq_refl) (SHW 2147470723 1 eq_refl) (SHW 2147470724 1 eq_refl) (SHW 2147470724 4 eq_refl) (SHW 2147470725 1 eq_refl)
           (SHW 2147470726 1 eq_refl) (SHW 2147470727 1 eq_refl) (SHW 2147470728 4 eq_refl) (SHW 2147470732 1 eq_refl) (SHW 2147470732 4 eq_refl) (SHW 2147470733 1 eq_refl)
           (SHW 2147470734 1 eq_refl) (SHW 2147470735 1 eq_refl) (SHW 2147470736 1 eq_refl) (SHW 2147470736 4 eq_refl) (SHW 2147470737 1 eq_refl) (SHW 2147470738 1 eq_refl)
           (SHW 2147470739 1 eq_refl) (SHW 2147470740 4 eq_refl) (SHW 2147470744 1 eq_refl) (SHW 2147470744 4 eq_refl) (SHW 2147470745 1 eq_refl) (SHW 2147470746 1 eq_refl)
           (SHW 2147470747 1 eq_refl) (SHW 2147470748 1 eq_refl) (SHW 2147470748 4 eq_refl) (SHW 2147470749 1 eq_refl) (SHW 2147470750 1 eq_refl) (SHW 2147470751 1 eq_refl)
           (SHW 2147470752 4 eq_refl) (SHW 2147470756 1 eq_refl) (SHW 2147470756 4 eq_refl) (SHW 2147470757 1 eq_refl) (SHW 2147470758 1 eq_refl) (SHW 2147470759 1 eq_refl)
           (SHW 2147470760 1 eq_refl) (SHW 2147470760 4 eq_refl) (SHW 2147470761 1 eq_refl) (SHW 2147470762 1 eq_refl) (SHW 2147470763 1 eq_refl) (SHW 2147470764 4 eq_refl)
           (SHW 2147470768 1 eq_refl) (SHW 2147470768 4 eq_refl) (SHW 2147470769 1 eq_refl) (SHW 2147470770 1 eq_refl) (SHW 2147470771 1 eq_refl) (SHW 2147470772 1 eq_refl)
           (SHW 2147470772 4 eq_refl) (SHW 2147470773 1 eq_refl) (SHW 2147470774 1 eq_refl) (SHW 2147470775 1 eq_refl) (SHW 2147470776 4 eq_refl) (SHW 2147470780 1 eq_refl)
           (SHW 2147470780 4 eq_refl) (SHW 2147470781 1 eq_refl) (SHW 2147470782 1 eq_refl) (SHW 2147470783 1 eq_refl) (SHW 2147470784 1 eq_refl) (SHW 2147470785 1 eq_refl)
           (SHW 2147470786 1 eq_refl) (SHW 2147470787 1 eq_refl) (SHW 2147470824 1 eq_refl) (SHW 2147470825 1 eq_refl) (SHW 2147470826 1 eq_refl) (SHW 2147470827 1 eq_refl)
           (SHW 2147470828 1 eq_refl) (SHW 2147470829 1 eq_refl) (SHW 2147470830 1 eq_refl) (SHW 2147470831 1 eq_refl) (SHW 2147470832 1 eq_refl) (SHW 2147470833 1 eq_refl)
           (SHW 2147470834 1 eq_refl) (SHW 2147470835 1 eq_refl) (SHW 2147470836 1 eq_refl) (SHW 2147470837 1 eq_refl) (SHW 2147470838 1 eq_refl) (SHW 2147470839 1 eq_refl)
           (SHW 2147470852 1 eq_refl) (SHW 2147470852 4 eq_refl) (SHW 2147470853 1 eq_refl) (SHW 2147470854 1 eq_refl) (SHW 2147470855 1 eq_refl) (SHW 2147470856 4 eq_refl)
           (SHW 2147470860 1 eq_refl) (SHW 2147470860 4 eq_refl) (SHW 2147470861 1 eq_refl) (SHW 2147470862 1 eq_refl) (SHW 2147470863 1 eq_refl) (SHW 2147470864 1 eq_refl)
           (SHW 2147470864 4 eq_refl) (SHW 2147470865 1 eq_refl) (SHW 2147470866 1 eq_refl) (SHW 2147470867 1 eq_refl) (SHW 2147470868 4 eq_refl) (SHW 2147470872 4 eq_refl)
           (SHW 2147470876 4 eq_refl) (SHW 2147470880 4 eq_refl) (SHW 2147470884 4 eq_refl) (SHW 2147470888 4 eq_refl) (SHW 2147470888 8 eq_refl) (SHW 2147470896 8 eq_refl)
           (SHW 2147470904 4 eq_refl) (SHW 2147470904 8 eq_refl) (SHW 2147470908 4 eq_refl) (SHW 2147470912 4 eq_refl) (SHW 2147470912 8 eq_refl) (SHW 2147470916 4 eq_refl)
           (SHW 2147470920 4 eq_refl) (SHW 2147470924 4 eq_refl) (SHW 2147470928 1 eq_refl) (SHW 2147470928 4 eq_refl) (SHW 2147470929 1 eq_refl) (SHW 2147470930 1 eq_refl)
           (SHW 2147470931 1 eq_refl) (SHW 2147623588 1 eq_refl) (SHW 2147623588 4 eq_refl) (SHW 2147623589 1 eq_refl) (SHW 2147623590 1 eq_refl) (SHW 2147623591 1 eq_refl)
           (SHW 2147623592 4 eq_refl) (SHW 2147623596 4 eq_refl) (SHW 2147623600 1 eq_refl) (SHW 2147623600 4 eq_refl) (SHW 2147623601 1 eq_refl) (SHW 2147623602 1 eq_refl)
           (SHW 2147623603 1 eq_refl) (SHW 2147628820 1 eq_refl) (SHW 2147628820 4 eq_refl) (SHW 2147628821 1 eq_refl) (SHW 2147628822 1 eq_refl) (SHW 2147628823 1 eq_refl)
           (SHW 2147628824 4 eq_refl) (SHW 2147628828 4 eq_refl) (SHW 2147628832 4 eq_refl) (SHW 2147628836 4 eq_refl) (SHW 2147628840 4 eq_refl) (SHW 2147628844 4 eq_refl)
           (SHW 2147628848 8 eq_refl) (SHW 2147628856 8 eq_refl) (SHW 2147628864 8 eq_refl) (SHW 2147628872 8 eq_refl) (SHW 2147628880 8 eq_refl) (SHW 2147628888 8 eq_refl)
           (SHW 2147628896 8 eq_refl) (SHW 2147628904 8 eq_refl) (SHW 2147628912 8 eq_refl) (SHW 2147628920 8 eq_refl) (SHW 2147628928 8 eq_refl) (SHW 2147628936 8 eq_refl)
           (SHW 2147628944 8 eq_refl) (SHW 2147628952 8 eq_refl) (SHW 2147628960 8 eq_refl) (SHW 2147628968 8 eq_refl) (SHW 2147628976 8 eq_refl) (SHW 2147628984 8 eq_refl)
           (SHW 2147628992 8 eq_refl) (SHW 2147629000 8 eq_refl) (SHW 2147629008 8 eq_refl) (SHW 2147629016 8 eq_refl) (SHW 2147629024 8 eq_refl) (SHW 2147629032 8 eq_refl)
           (SHW 2147629040 8 eq_refl) (SHW 2147629048 8 eq_refl) (SHW 2147629056 8 eq_refl) (SHW 2147629064 8 eq_refl) (SHW 2147629072 8 eq_refl) (SHW 2147629080 8 eq_refl)
           (SHW 2147629088 8 eq_refl) (SHW 2147629096 8 eq_refl) (SHW 2147629104 8 eq_refl) (SHW 2147629112 8 eq_refl) (SHW 2147629120 8 eq_refl) (SHW 2147629128 8 eq_refl)
           (SHW 2147629136 8 eq_refl) (SHW 2147629144 8 eq_refl) (SHW 2147629144 4 eq_refl) (SHW 2147629148 4 eq_refl) (SHW 2147629152 8 eq_refl) (SHW 2147629152 4 eq_refl)
           (SHW 2147629156 4 eq_refl) (SHW 2147629160 8 eq_refl) (SHW 2147629160 4 eq_refl) (SHW 2147629164 4 eq_refl) (SHW 2147629168 1 eq_refl) (SHW 2147629168 4 eq_refl)
           (SHW 2147629169 1 eq_refl) (SHW 2147629170 1 eq_refl) (SHW 2147629171 1 eq_refl) TIDC HTr (XCC 0%nat 7028080 4 0 eq_refl) (XCC1 1%nat 7028115 0 eq_refl eq_refl)
           (XCC 2%nat 7027552 8 7027560 eq_refl) (XCC 3%nat 7027544 4 2 eq_refl) (XCC 22%nat 7027576 8 1277044 eq_refl) (XCC 23%nat 7027832 8 716372 eq_refl) (XCC 6%nat 7027540 4 0 eq_refl)
           (XCC1 24%nat 6889684 0 eq_refl eq_refl) (XCC 4%nat 7027568 8 1277044 eq_refl) (XCC 5%nat 7027824 8 648332 eq_refl) (STC1 10%nat 2038048 0 eq_refl eq_refl)
           (XCC 7%nat 7027560 8 0 eq_refl) (STC1 3%nat 1426448 0 eq_refl eq_refl) (STC 0%nat 1412008 8 1412008 eq_refl) (STC 2%nat 1426368 8 1 eq_refl) (STC 4%nat 1430160 4 1 eq_refl)
           (STC 5%nat 1430320 8 0 eq_refl) (STC1 8%nat 1443672 1 eq_refl eq_refl) (STC 7%nat 1440376 8 2147450880 eq_refl)
           (DSC 1423520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145984)) ltac:(img_rd) eq_refl) (DSC 1423536 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1438428 1 eq_refl eq_refl)
           (DSC 1423536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 2037280 8 18446744073709551615 eq_refl) (STC 1%nat 1412520 8 1347948 eq_refl)
           (DSC 1423576 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146016)) ltac:(img_rd) eq_refl)
           (DSC 1423600 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1423640 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146144)) ltac:(img_rd) eq_refl)
           (DSC 1423664 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1423704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146176)) ltac:(img_rd) eq_refl)
           (DSC 1423728 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1423768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146272)) ltac:(img_rd) eq_refl)
           (DSC 1423792 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1423832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146304)) ltac:(img_rd) eq_refl)
           (DSC 1423856 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1423856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1423896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146464)) ltac:(img_rd) eq_refl)
           (DSC 1423920 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1423960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl)
           (DSC 1423984 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146528)) ltac:(img_rd) eq_refl)
           (DSC 1424048 1%nat [Z_to_bv 8 192] ltac:(img_rd) eq_refl) (DSC 1424048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 6848)) ltac:(img_rd) eq_refl)
           (DSC 1424088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 153376)) ltac:(img_rd) eq_refl)
           (DSC 1424112 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 3424)) ltac:(img_rd) eq_refl)
           (DSC 1424152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156800)) ltac:(img_rd) eq_refl)
           (DSC 1424176 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156832)) ltac:(img_rd) eq_refl)
           (DSC 1424240 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1424240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
           (DSC 1424280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156960)) ltac:(img_rd) eq_refl)
           (DSC 1424304 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156992)) ltac:(img_rd) eq_refl)
           (DSC 1424368 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157024)) ltac:(img_rd) eq_refl)
           (DSC 1424432 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157056)) ltac:(img_rd) eq_refl)
           (DSC 1424496 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157088)) ltac:(img_rd) eq_refl)
           (DSC 1424560 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157280)) ltac:(img_rd) eq_refl)
           (DSC 1424624 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157664)) ltac:(img_rd) eq_refl)
           (DSC 1424688 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1424728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157728)) ltac:(img_rd) eq_refl)
           (DSC 1424752 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1424792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157792)) ltac:(img_rd) eq_refl)
           (DSC 1424816 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157824)) ltac:(img_rd) eq_refl)
           (DSC 1424880 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1424920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157920)) ltac:(img_rd) eq_refl)
           (DSC 1424944 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1424984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158016)) ltac:(img_rd) eq_refl)
           (DSC 1425008 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158112)) ltac:(img_rd) eq_refl)
           (DSC 1425072 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158208)) ltac:(img_rd) eq_refl)
           (DSC 1425136 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158304)) ltac:(img_rd) eq_refl)
           (DSC 1425200 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158400)) ltac:(img_rd) eq_refl)
           (DSC 1425264 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1425264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
           (DSC 1425304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158528)) ltac:(img_rd) eq_refl)
           (DSC 1425328 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1425368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158592)) ltac:(img_rd) eq_refl)
           (DSC 1425392 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1425432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158656)) ltac:(img_rd) eq_refl)
           (DSC 1425456 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158752)) ltac:(img_rd) eq_refl)
           (DSC 1425520 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158848)) ltac:(img_rd) eq_refl)
           (DSC 1425584 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158944)) ltac:(img_rd) eq_refl)
           (DSC 1425648 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159040)) ltac:(img_rd) eq_refl)
           (DSC 1425712 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159136)) ltac:(img_rd) eq_refl)
           (DSC 1425776 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159232)) ltac:(img_rd) eq_refl)
           (DSC 1425840 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1425880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159552)) ltac:(img_rd) eq_refl)
           (DSC 1425904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1425944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159584)) ltac:(img_rd) eq_refl)
           (DSC 1425968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1426008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159616)) ltac:(img_rd) eq_refl)
           (DSC 1426032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1426072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159648)) ltac:(img_rd) eq_refl)
           (DSC 1426096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1426136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159776)) ltac:(img_rd) eq_refl)
           (DSC 1426160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1426160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1426200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159872)) ltac:(img_rd) eq_refl)
           (DSC 1426224 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 544)) ltac:(img_rd) eq_refl)
           (DSC 1426264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1426272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1381664)) ltac:(img_rd) eq_refl) (DSC 1426288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1426288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1426328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (XCC 8%nat 7029512 8 0 eq_refl) (XCC 9%nat 1423464 8 1423232 eq_refl) (XCC 10%nat 1423372 4 4294967295 eq_refl) (XCC 11%nat 1423272 8 0 eq_refl) (XCC 12%nat 1423288 8 0 eq_refl)
           (XCC 13%nat 1423240 8 0 eq_refl) (XCC 14%nat 1423248 8 0 eq_refl) (XCC 15%nat 1423224 8 1422992 eq_refl) SOlock SOwpos SOwbase SOrpos SOrend (XCC 16%nat 1422984 8 1422752 eq_refl)
           (XCC 17%nat 1422892 4 4294967295 eq_refl) (XCC 18%nat 1422792 8 0 eq_refl) (XCC 19%nat 1422808 8 0 eq_refl) (XCC 20%nat 1422760 8 0 eq_refl) (XCC 21%nat 1422768 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x137cc8) M R1 (Z_to_bv 64 0x1379d8) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x1379d8) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpX.KS_dpX; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.

  (* [comment removed for export] *)
  Definition stdoutPA (MV : word -> option byte) : Prop :=
    rdn ASEGS MV (Z_to_bv 64 1423132) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
    /\ rdn ASEGS MV (Z_to_bv 64 1423032) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1423048) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1423000) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1423008) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_e : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preE LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6896384 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutPA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x137cc8) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
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
    assert (SHW : forall a n, ((2147469128 <=? a) && (a + n <=? 2147470932) || (2147623588 <=? a) && (a + n <=? 2147623604) || (2147628820 <=? a) && (a + n <=? 2147629172)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_E i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_E i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_E i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x15b8a0 <=? a) && (a + Z.of_nat n <=? 0x15c3a0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXe.dpXe_conc fx R MV V
           HS64 HT64 G2 G4 HSr HSa CWR CDF IMGc (WSG 1426368 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1426448 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 1430320 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027536 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027544 4%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 7027552 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7028080 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147469128 1 eq_refl) (SHW 2147469129 1 eq_refl)
           (SHW 2147469130 1 eq_refl) (SHW 2147469131 1 eq_refl) (SHW 2147469132 1 eq_refl) (SHW 2147469132 4 eq_refl) (SHW 2147469133 1 eq_refl) (SHW 2147469134 1 eq_refl)
           (SHW 2147469135 1 eq_refl) (SHW 2147469136 4 eq_refl) (SHW 2147469140 1 eq_refl) (SHW 2147469140 4 eq_refl) (SHW 2147469141 1 eq_refl) (SHW 2147469142 1 eq_refl)
           (SHW 2147469143 1 eq_refl) (SHW 2147469148 1 eq_refl) (SHW 2147469149 1 eq_refl) (SHW 2147469150 1 eq_refl) (SHW 2147469151 1 eq_refl) (SHW 2147469152 1 eq_refl)
           (SHW 2147469152 4 eq_refl) (SHW 2147469153 1 eq_refl) (SHW 2147469154 1 eq_refl) (SHW 2147469155 1 eq_refl) (SHW 2147469156 4 eq_refl) (SHW 2147469160 1 eq_refl)
           (SHW 2147469160 4 eq_refl) (SHW 2147469161 1 eq_refl) (SHW 2147469162 1 eq_refl) (SHW 2147469163 1 eq_refl) (SHW 2147469164 1 eq_refl) (SHW 2147469165 1 eq_refl)
           (SHW 2147469166 1 eq_refl) (SHW 2147469167 1 eq_refl) (SHW 2147469168 1 eq_refl) (SHW 2147469169 1 eq_refl) (SHW 2147469170 1 eq_refl) (SHW 2147469171 1 eq_refl)
           (SHW 2147469172 1 eq_refl) (SHW 2147469173 1 eq_refl) (SHW 2147469174 1 eq_refl) (SHW 2147469175 1 eq_refl) (SHW 2147469188 1 eq_refl) (SHW 2147469189 1 eq_refl)
           (SHW 2147469190 1 eq_refl) (SHW 2147469191 1 eq_refl) (SHW 2147469192 1 eq_refl) (SHW 2147469193 1 eq_refl) (SHW 2147469194 1 eq_refl) (SHW 2147469195 1 eq_refl)
           (SHW 2147469196 1 eq_refl) (SHW 2147469196 4 eq_refl) (SHW 2147469197 1 eq_refl) (SHW 2147469198 1 eq_refl) (SHW 2147469199 1 eq_refl) (SHW 2147469200 4 eq_refl)
           (SHW 2147469204 4 eq_refl) (SHW 2147469208 4 eq_refl) (SHW 2147469212 4 eq_refl) (SHW 2147469216 4 eq_refl) (SHW 2147469220 4 eq_refl) (SHW 2147469224 8 eq_refl)
           (SHW 2147469232 8 eq_refl) (SHW 2147469240 8 eq_refl) (SHW 2147469248 8 eq_refl) (SHW 2147469256 8 eq_refl) (SHW 2147469264 8 eq_refl) (SHW 2147469272 8 eq_refl)
           (SHW 2147469280 8 eq_refl) (SHW 2147469288 8 eq_refl) (SHW 2147469296 8 eq_refl) (SHW 2147469304 8 eq_refl) (SHW 2147469312 8 eq_refl) (SHW 2147469320 8 eq_refl)
           (SHW 2147469328 8 eq_refl) (SHW 2147469336 8 eq_refl) (SHW 2147469344 8 eq_refl) (SHW 2147469352 8 eq_refl) (SHW 2147469360 8 eq_refl) (SHW 2147469368 8 eq_refl)
           (SHW 2147469376 8 eq_refl) (SHW 2147469384 8 eq_refl) (SHW 2147469392 8 eq_refl) (SHW 2147469400 8 eq_refl) (SHW 2147469408 8 eq_refl) (SHW 2147469416 8 eq_refl)
           (SHW 2147469424 8 eq_refl) (SHW 2147469432 8 eq_refl) (SHW 2147469440 8 eq_refl) (SHW 2147469448 8 eq_refl) (SHW 2147469456 8 eq_refl) (SHW 2147469464 8 eq_refl)
           (SHW 2147469472 8 eq_refl) (SHW 2147469480 8 eq_refl) (SHW 2147469488 8 eq_refl) (SHW 2147469496 8 eq_refl) (SHW 2147469504 8 eq_refl) (SHW 2147469512 8 eq_refl)
           (SHW 2147469520 8 eq_refl) (SHW 2147469528 8 eq_refl) (SHW 2147469536 8 eq_refl) (SHW 2147469544 8 eq_refl) (SHW 2147469552 8 eq_refl) (SHW 2147469560 8 eq_refl)
           (SHW 2147469568 8 eq_refl) (SHW 2147469576 8 eq_refl) (SHW 2147469584 8 eq_refl) (SHW 2147469592 8 eq_refl) (SHW 2147469600 8 eq_refl) (SHW 2147469608 8 eq_refl)
           (SHW 2147469616 8 eq_refl) (SHW 2147469624 8 eq_refl) (SHW 2147469632 8 eq_refl) (SHW 2147469640 8 eq_refl) (SHW 2147469648 8 eq_refl) (SHW 2147469656 8 eq_refl)
           (SHW 2147469664 8 eq_refl) (SHW 2147469672 8 eq_refl) (SHW 2147469680 8 eq_refl) (SHW 2147469688 8 eq_refl) (SHW 2147469696 8 eq_refl) (SHW 2147469704 8 eq_refl)
           (SHW 2147469712 8 eq_refl) (SHW 2147469720 8 eq_refl) (SHW 2147469728 8 eq_refl) (SHW 2147469736 8 eq_refl) (SHW 2147469744 8 eq_refl) (SHW 2147469752 8 eq_refl)
           (SHW 2147469760 8 eq_refl) (SHW 2147469768 8 eq_refl) (SHW 2147469776 8 eq_refl) (SHW 2147469784 8 eq_refl) (SHW 2147469792 8 eq_refl) (SHW 2147469800 8 eq_refl)
           (SHW 2147469808 8 eq_refl) (SHW 2147469816 8 eq_refl) (SHW 2147469824 8 eq_refl) (SHW 2147469832 8 eq_refl) (SHW 2147469840 8 eq_refl) (SHW 2147469848 8 eq_refl)
           (SHW 2147469856 8 eq_refl) (SHW 2147469864 8 eq_refl) (SHW 2147469872 8 eq_refl) (SHW 2147469880 8 eq_refl) (SHW 2147469888 8 eq_refl) (SHW 2147469896 8 eq_refl)
           (SHW 2147469904 8 eq_refl) (SHW 2147469912 8 eq_refl) (SHW 2147469920 8 eq_refl) (SHW 2147469928 8 eq_refl) (SHW 2147469936 8 eq_refl) (SHW 2147469944 8 eq_refl)
           (SHW 2147469952 8 eq_refl) (SHW 2147469960 8 eq_refl) (SHW 2147469968 8 eq_refl) (SHW 2147469976 8 eq_refl) (SHW 2147469984 8 eq_refl) (SHW 2147469992 8 eq_refl)
           (SHW 2147470000 8 eq_refl) (SHW 2147470008 8 eq_refl) (SHW 2147470016 8 eq_refl) (SHW 2147470024 4 eq_refl) (SHW 2147470028 4 eq_refl) (SHW 2147470032 4 eq_refl)
           (SHW 2147470036 4 eq_refl) (SHW 2147470040 4 eq_refl) (SHW 2147470044 4 eq_refl) (SHW 2147470048 1 eq_refl) (SHW 2147470048 4 eq_refl) (SHW 2147470049 1 eq_refl)
           (SHW 2147470050 1 eq_refl) (SHW 2147470051 1 eq_refl) (SHW 2147470052 1 eq_refl) (SHW 2147470052 4 eq_refl) (SHW 2147470053 1 eq_refl) (SHW 2147470054 1 eq_refl)
           (SHW 2147470055 1 eq_refl) (SHW 2147470056 4 eq_refl) (SHW 2147470060 4 eq_refl) (SHW 2147470064 4 eq_refl) (SHW 2147470068 4 eq_refl) (SHW 2147470072 4 eq_refl)
           (SHW 2147470076 4 eq_refl) (SHW 2147470080 8 eq_refl) (SHW 2147470088 8 eq_refl) (SHW 2147470096 8 eq_refl) (SHW 2147470104 8 eq_refl) (SHW 2147470112 8 eq_refl)
           (SHW 2147470120 8 eq_refl) (SHW 2147470128 8 eq_refl) (SHW 2147470136 8 eq_refl) (SHW 2147470144 8 eq_refl) (SHW 2147470152 8 eq_refl) (SHW 2147470160 8 eq_refl)
           (SHW 2147470168 8 eq_refl) (SHW 2147470176 8 eq_refl) (SHW 2147470184 8 eq_refl) (SHW 2147470192 8 eq_refl) (SHW 2147470200 8 eq_refl) (SHW 2147470208 8 eq_refl)
           (SHW 2147470216 8 eq_refl) (SHW 2147470224 8 eq_refl) (SHW 2147470232 8 eq_refl) (SHW 2147470240 8 eq_refl) (SHW 2147470248 8 eq_refl) (SHW 2147470256 8 eq_refl)
           (SHW 2147470264 8 eq_refl) (SHW 2147470272 8 eq_refl) (SHW 2147470280 8 eq_refl) (SHW 2147470288 8 eq_refl) (SHW 2147470296 8 eq_refl) (SHW 2147470304 8 eq_refl)
           (SHW 2147470312 8 eq_refl) (SHW 2147470320 8 eq_refl) (SHW 2147470328 8 eq_refl) (SHW 2147470336 8 eq_refl) (SHW 2147470344 8 eq_refl) (SHW 2147470352 8 eq_refl)
           (SHW 2147470360 8 eq_refl) (SHW 2147470368 8 eq_refl) (SHW 2147470376 8 eq_refl) (SHW 2147470384 8 eq_refl) (SHW 2147470392 8 eq_refl) (SHW 2147470400 8 eq_refl)
           (SHW 2147470408 8 eq_refl) (SHW 2147470416 8 eq_refl) (SHW 2147470424 8 eq_refl) (SHW 2147470432 8 eq_refl) (SHW 2147470440 8 eq_refl) (SHW 2147470448 8 eq_refl)
           (SHW 2147470452 4 eq_refl) (SHW 2147470456 4 eq_refl) (SHW 2147470456 8 eq_refl) (SHW 2147470460 4 eq_refl) (SHW 2147470464 4 eq_refl) (SHW 2147470468 4 eq_refl)
           (SHW 2147470472 4 eq_refl) (SHW 2147470476 1 eq_refl) (SHW 2147470476 4 eq_refl) (SHW 2147470477 1 eq_refl) (SHW 2147470478 1 eq_refl) (SHW 2147470479 1 eq_refl)
           (SHW 2147470480 1 eq_refl) (SHW 2147470481 1 eq_refl) (SHW 2147470482 1 eq_refl) (SHW 2147470483 1 eq_refl) (SHW 2147470484 1 eq_refl) (SHW 2147470484 4 eq_refl)
           (SHW 2147470485 1 eq_refl) (SHW 2147470486 1 eq_refl) (SHW 2147470487 1 eq_refl) (SHW 2147470488 4 eq_refl) (SHW 2147470492 4 eq_refl) (SHW 2147470496 1 eq_refl)
           (SHW 2147470496 4 eq_refl) (SHW 2147470497 1 eq_refl) (SHW 2147470498 1 eq_refl) (SHW 2147470499 1 eq_refl) (SHW 2147470500 1 eq_refl) (SHW 2147470501 1 eq_refl)
           (SHW 2147470502 1 eq_refl) (SHW 2147470503 1 eq_refl) (SHW 2147470504 1 eq_refl) (SHW 2147470505 1 eq_refl) (SHW 2147470506 1 eq_refl) (SHW 2147470507 1 eq_refl)
           (SHW 2147470508 1 eq_refl) (SHW 2147470509 1 eq_refl) (SHW 2147470510 1 eq_refl) (SHW 2147470511 1 eq_refl) (SHW 2147470512 1 eq_refl) (SHW 2147470513 1 eq_refl)
           (SHW 2147470514 1 eq_refl) (SHW 2147470515 1 eq_refl) (SHW 2147470516 1 eq_refl) (SHW 2147470517 1 eq_refl) (SHW 2147470518 1 eq_refl) (SHW 2147470519 1 eq_refl)
           (SHW 2147470540 1 eq_refl) (SHW 2147470541 1 eq_refl) (SHW 2147470542 1 eq_refl) (SHW 2147470543 1 eq_refl) (SHW 2147470588 1 eq_refl) (SHW 2147470589 1 eq_refl)
           (SHW 2147470590 1 eq_refl) (SHW 2147470591 1 eq_refl) (SHW 2147470592 1 eq_refl) (SHW 2147470593 1 eq_refl) (SHW 2147470594 1 eq_refl) (SHW 2147470595 1 eq_refl)
           (SHW 2147470596 1 eq_refl) (SHW 2147470597 1 eq_refl) (SHW 2147470598 1 eq_refl) (SHW 2147470599 1 eq_refl) (SHW 2147470600 1 eq_refl) (SHW 2147470601 1 eq_refl)
           (SHW 2147470602 1 eq_refl) (SHW 2147470603 1 eq_refl) (SHW 2147470604 1 eq_refl) (SHW 2147470605 1 eq_refl) (SHW 2147470606 1 eq_refl) (SHW 2147470607 1 eq_refl)
           (SHW 2147470608 1 eq_refl) (SHW 2147470608 4 eq_refl) (SHW 2147470609 1 eq_refl) (SHW 2147470610 1 eq_refl) (SHW 2147470611 1 eq_refl) (SHW 2147470612 4 eq_refl)
           (SHW 2147470616 1 eq_refl) (SHW 2147470616 4 eq_refl) (SHW 2147470617 1 eq_refl) (SHW 2147470618 1 eq_refl) (SHW 2147470619 1 eq_refl) (SHW 2147470620 1 eq_refl)
           (SHW 2147470620 4 eq_refl) (SHW 2147470621 1 eq_refl) (SHW 2147470622 1 eq_refl) (SHW 2147470623 1 eq_refl) (SHW 2147470624 4 eq_refl) (SHW 2147470628 1 eq_refl)
           (SHW 2147470628 4 eq_refl) (SHW 2147470629 1 eq_refl) (SHW 2147470630 1 eq_refl) (SHW 2147470631 1 eq_refl) (SHW 2147470632 1 eq_refl) (SHW 2147470632 4 eq_refl)
           (SHW 2147470633 1 eq_refl) (SHW 2147470634 1 eq_refl) (SHW 2147470635 1 eq_refl) (SHW 2147470636 4 eq_refl) (SHW 2147470640 1 eq_refl) (SHW 2147470640 4 eq_refl)
           (SHW 2147470641 1 eq_refl) (SHW 2147470642 1 eq_refl) (SHW 2147470643 1 eq_refl) (SHW 2147470644 1 eq_refl) (SHW 2147470644 4 eq_refl) (SHW 2147470645 1 eq_refl)
           (SHW 2147470646 1 eq_refl) (SHW 2147470647 1 eq_refl) (SHW 2147470648 4 eq_refl) (SHW 2147470652 1 eq_refl) (SHW 2147470652 4 eq_refl) (SHW 2147470653 1 eq_refl)
           (SHW 2147470654 1 eq_refl) (SHW 2147470655 1 eq_refl) (SHW 2147470656 1 eq_refl) (SHW 2147470656 4 eq_refl) (SHW 2147470657 1 eq_refl) (SHW 2147470658 1 eq_refl)
           (SHW 2147470659 1 eq_refl) (SHW 2147470660 4 eq_refl) (SHW 2147470664 1 eq_refl) (SHW 2147470664 4 eq_refl) (SHW 2147470665 1 eq_refl) (SHW 2147470666 1 eq_refl)
           (SHW 2147470667 1 eq_refl) (SHW 2147470668 1 eq_refl) (SHW 2147470668 4 eq_refl) (SHW 2147470669 1 eq_refl) (SHW 2147470670 1 eq_refl) (SHW 2147470671 1 eq_refl)
           (SHW 2147470672 4 eq_refl) (SHW 2147470676 1 eq_refl) (SHW 2147470676 4 eq_refl) (SHW 2147470677 1 eq_refl) (SHW 2147470678 1 eq_refl) (SHW 2147470679 1 eq_refl)
           (SHW 2147470680 1 eq_refl) (SHW 2147470680 4 eq_refl) (SHW 2147470681 1 eq_refl) (SHW 2147470682 1 eq_refl) (SHW 2147470683 1 eq_refl) (SHW 2147470684 4 eq_refl)
           (SHW 2147470688 4 eq_refl) (SHW 2147470692 1 eq_refl) (SHW 2147470692 4 eq_refl) (SHW 2147470693 1 eq_refl) (SHW 2147470694 1 eq_refl) (SHW 2147470695 1 eq_refl)
           (SHW 2147470696 1 eq_refl) (SHW 2147470697 1 eq_refl) (SHW 2147470698 1 eq_refl) (SHW 2147470699 1 eq_refl) (SHW 2147470700 1 eq_refl) (SHW 2147470701 1 eq_refl)
           (SHW 2147470702 1 eq_refl) (SHW 2147470703 1 eq_refl) (SHW 2147470704 1 eq_refl) (SHW 2147470705 1 eq_refl) (SHW 2147470706 1 eq_refl) (SHW 2147470707 1 eq_refl)
           (SHW 2147470708 1 eq_refl) (SHW 2147470709 1 eq_refl) (SHW 2147470710 1 eq_refl) (SHW 2147470711 1 eq_refl) (SHW 2147470712 1 eq_refl) (SHW 2147470712 4 eq_refl)
           (SHW 2147470713 1 eq_refl) (SHW 2147470714 1 eq_refl) (SHW 2147470715 1 eq_refl) (SHW 2147470716 4 eq_refl) (SHW 2147470720 1 eq_refl) (SHW 2147470720 4 eq_refl)
           (SHW 2147470721 1 eq_refl) (SHW 2147470722 1 eq_refl) (SHW 2147470723 1 eq_refl) (SHW 2147470724 1 eq_refl) (SHW 2147470724 4 eq_refl) (SHW 2147470725 1 eq_refl)
           (SHW 2147470726 1 eq_refl) (SHW 2147470727 1 eq_refl) (SHW 2147470728 4 eq_refl) (SHW 2147470732 1 eq_refl) (SHW 2147470732 4 eq_refl) (SHW 2147470733 1 eq_refl)
           (SHW 2147470734 1 eq_refl) (SHW 2147470735 1 eq_refl) (SHW 2147470736 1 eq_refl) (SHW 2147470736 4 eq_refl) (SHW 2147470737 1 eq_refl) (SHW 2147470738 1 eq_refl)
           (SHW 2147470739 1 eq_refl) (SHW 2147470740 4 eq_refl) (SHW 2147470744 1 eq_refl) (SHW 2147470744 4 eq_refl) (SHW 2147470745 1 eq_refl) (SHW 2147470746 1 eq_refl)
           (SHW 2147470747 1 eq_refl) (SHW 2147470748 1 eq_refl) (SHW 2147470748 4 eq_refl) (SHW 2147470749 1 eq_refl) (SHW 2147470750 1 eq_refl) (SHW 2147470751 1 eq_refl)
           (SHW 2147470752 4 eq_refl) (SHW 2147470756 1 eq_refl) (SHW 2147470756 4 eq_refl) (SHW 2147470757 1 eq_refl) (SHW 2147470758 1 eq_refl) (SHW 2147470759 1 eq_refl)
           (SHW 2147470760 1 eq_refl) (SHW 2147470760 4 eq_refl) (SHW 2147470761 1 eq_refl) (SHW 2147470762 1 eq_refl) (SHW 2147470763 1 eq_refl) (SHW 2147470764 4 eq_refl)
           (SHW 2147470768 1 eq_refl) (SHW 2147470768 4 eq_refl) (SHW 2147470769 1 eq_refl) (SHW 2147470770 1 eq_refl) (SHW 2147470771 1 eq_refl) (SHW 2147470772 1 eq_refl)
           (SHW 2147470772 4 eq_refl) (SHW 2147470773 1 eq_refl) (SHW 2147470774 1 eq_refl) (SHW 2147470775 1 eq_refl) (SHW 2147470776 4 eq_refl) (SHW 2147470780 1 eq_refl)
           (SHW 2147470780 4 eq_refl) (SHW 2147470781 1 eq_refl) (SHW 2147470782 1 eq_refl) (SHW 2147470783 1 eq_refl) (SHW 2147470784 1 eq_refl) (SHW 2147470785 1 eq_refl)
           (SHW 2147470786 1 eq_refl) (SHW 2147470787 1 eq_refl) (SHW 2147470824 1 eq_refl) (SHW 2147470825 1 eq_refl) (SHW 2147470826 1 eq_refl) (SHW 2147470827 1 eq_refl)
           (SHW 2147470828 1 eq_refl) (SHW 2147470829 1 eq_refl) (SHW 2147470830 1 eq_refl) (SHW 2147470831 1 eq_refl) (SHW 2147470832 1 eq_refl) (SHW 2147470833 1 eq_refl)
           (SHW 2147470834 1 eq_refl) (SHW 2147470835 1 eq_refl) (SHW 2147470836 1 eq_refl) (SHW 2147470837 1 eq_refl) (SHW 2147470838 1 eq_refl) (SHW 2147470839 1 eq_refl)
           (SHW 2147470852 1 eq_refl) (SHW 2147470852 4 eq_refl) (SHW 2147470853 1 eq_refl) (SHW 2147470854 1 eq_refl) (SHW 2147470855 1 eq_refl) (SHW 2147470856 4 eq_refl)
           (SHW 2147470860 1 eq_refl) (SHW 2147470860 4 eq_refl) (SHW 2147470861 1 eq_refl) (SHW 2147470862 1 eq_refl) (SHW 2147470863 1 eq_refl) (SHW 2147470864 1 eq_refl)
           (SHW 2147470864 4 eq_refl) (SHW 2147470865 1 eq_refl) (SHW 2147470866 1 eq_refl) (SHW 2147470867 1 eq_refl) (SHW 2147470868 4 eq_refl) (SHW 2147470872 4 eq_refl)
           (SHW 2147470876 4 eq_refl) (SHW 2147470880 4 eq_refl) (SHW 2147470884 4 eq_refl) (SHW 2147470888 4 eq_refl) (SHW 2147470888 8 eq_refl) (SHW 2147470896 8 eq_refl)
           (SHW 2147470904 4 eq_refl) (SHW 2147470904 8 eq_refl) (SHW 2147470908 4 eq_refl) (SHW 2147470912 4 eq_refl) (SHW 2147470912 8 eq_refl) (SHW 2147470916 4 eq_refl)
           (SHW 2147470920 4 eq_refl) (SHW 2147470924 4 eq_refl) (SHW 2147470928 1 eq_refl) (SHW 2147470928 4 eq_refl) (SHW 2147470929 1 eq_refl) (SHW 2147470930 1 eq_refl)
           (SHW 2147470931 1 eq_refl) (SHW 2147623588 1 eq_refl) (SHW 2147623588 4 eq_refl) (SHW 2147623589 1 eq_refl) (SHW 2147623590 1 eq_refl) (SHW 2147623591 1 eq_refl)
           (SHW 2147623592 4 eq_refl) (SHW 2147623596 4 eq_refl) (SHW 2147623600 1 eq_refl) (SHW 2147623600 4 eq_refl) (SHW 2147623601 1 eq_refl) (SHW 2147623602 1 eq_refl)
           (SHW 2147623603 1 eq_refl) (SHW 2147628820 1 eq_refl) (SHW 2147628820 4 eq_refl) (SHW 2147628821 1 eq_refl) (SHW 2147628822 1 eq_refl) (SHW 2147628823 1 eq_refl)
           (SHW 2147628824 4 eq_refl) (SHW 2147628828 4 eq_refl) (SHW 2147628832 4 eq_refl) (SHW 2147628836 4 eq_refl) (SHW 2147628840 4 eq_refl) (SHW 2147628844 4 eq_refl)
           (SHW 2147628848 8 eq_refl) (SHW 2147628856 8 eq_refl) (SHW 2147628864 8 eq_refl) (SHW 2147628872 8 eq_refl) (SHW 2147628880 8 eq_refl) (SHW 2147628888 8 eq_refl)
           (SHW 2147628896 8 eq_refl) (SHW 2147628904 8 eq_refl) (SHW 2147628912 8 eq_refl) (SHW 2147628920 8 eq_refl) (SHW 2147628928 8 eq_refl) (SHW 2147628936 8 eq_refl)
           (SHW 2147628944 8 eq_refl) (SHW 2147628952 8 eq_refl) (SHW 2147628960 8 eq_refl) (SHW 2147628968 8 eq_refl) (SHW 2147628976 8 eq_refl) (SHW 2147628984 8 eq_refl)
           (SHW 2147628992 8 eq_refl) (SHW 2147629000 8 eq_refl) (SHW 2147629008 8 eq_refl) (SHW 2147629016 8 eq_refl) (SHW 2147629024 8 eq_refl) (SHW 2147629032 8 eq_refl)
           (SHW 2147629040 8 eq_refl) (SHW 2147629048 8 eq_refl) (SHW 2147629056 8 eq_refl) (SHW 2147629064 8 eq_refl) (SHW 2147629072 8 eq_refl) (SHW 2147629080 8 eq_refl)
           (SHW 2147629088 8 eq_refl) (SHW 2147629096 8 eq_refl) (SHW 2147629104 8 eq_refl) (SHW 2147629112 8 eq_refl) (SHW 2147629120 8 eq_refl) (SHW 2147629128 8 eq_refl)
           (SHW 2147629136 8 eq_refl) (SHW 2147629144 8 eq_refl) (SHW 2147629144 4 eq_refl) (SHW 2147629148 4 eq_refl) (SHW 2147629152 8 eq_refl) (SHW 2147629152 4 eq_refl)
           (SHW 2147629156 4 eq_refl) (SHW 2147629160 8 eq_refl) (SHW 2147629160 4 eq_refl) (SHW 2147629164 4 eq_refl) (SHW 2147629168 1 eq_refl) (SHW 2147629168 4 eq_refl)
           (SHW 2147629169 1 eq_refl) (SHW 2147629170 1 eq_refl) (SHW 2147629171 1 eq_refl) TIDC HTr (XCC 0%nat 7028080 4 0 eq_refl) (XCC1 1%nat 7028115 0 eq_refl eq_refl)
           (XCC 2%nat 7027552 8 7027560 eq_refl) (XCC 3%nat 7027544 4 1 eq_refl) (XCC 4%nat 7027568 8 1277044 eq_refl) (XCC 5%nat 7027824 8 648332 eq_refl) (XCC 6%nat 7027540 4 0 eq_refl)
           (STC1 10%nat 2038048 0 eq_refl eq_refl) (XCC 7%nat 7027560 8 0 eq_refl) (STC1 3%nat 1426448 0 eq_refl eq_refl) (STC 0%nat 1412008 8 1412008 eq_refl)
           (STC 2%nat 1426368 8 1 eq_refl) (STC 4%nat 1430160 4 1 eq_refl) (STC 5%nat 1430320 8 0 eq_refl) (STC1 8%nat 1443672 1 eq_refl eq_refl) (STC 7%nat 1440376 8 2147450880 eq_refl)
           (DSC 1423520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145984)) ltac:(img_rd) eq_refl) (DSC 1423536 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1438428 1 eq_refl eq_refl)
           (DSC 1423536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 2037280 8 18446744073709551615 eq_refl) (STC 1%nat 1412520 8 1347948 eq_refl)
           (DSC 1423576 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146016)) ltac:(img_rd) eq_refl)
           (DSC 1423600 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1423640 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146144)) ltac:(img_rd) eq_refl)
           (DSC 1423664 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1423704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146176)) ltac:(img_rd) eq_refl)
           (DSC 1423728 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1423768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146272)) ltac:(img_rd) eq_refl)
           (DSC 1423792 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1423832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146304)) ltac:(img_rd) eq_refl)
           (DSC 1423856 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1423856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1423896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146464)) ltac:(img_rd) eq_refl)
           (DSC 1423920 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1423960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl)
           (DSC 1423984 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146528)) ltac:(img_rd) eq_refl)
           (DSC 1424048 1%nat [Z_to_bv 8 192] ltac:(img_rd) eq_refl) (DSC 1424048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 6848)) ltac:(img_rd) eq_refl)
           (DSC 1424088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 153376)) ltac:(img_rd) eq_refl)
           (DSC 1424112 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 3424)) ltac:(img_rd) eq_refl)
           (DSC 1424152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156800)) ltac:(img_rd) eq_refl)
           (DSC 1424176 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156832)) ltac:(img_rd) eq_refl)
           (DSC 1424240 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1424240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
           (DSC 1424280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156960)) ltac:(img_rd) eq_refl)
           (DSC 1424304 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156992)) ltac:(img_rd) eq_refl)
           (DSC 1424368 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157024)) ltac:(img_rd) eq_refl)
           (DSC 1424432 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157056)) ltac:(img_rd) eq_refl)
           (DSC 1424496 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157088)) ltac:(img_rd) eq_refl)
           (DSC 1424560 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157280)) ltac:(img_rd) eq_refl)
           (DSC 1424624 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157664)) ltac:(img_rd) eq_refl)
           (DSC 1424688 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1424728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157728)) ltac:(img_rd) eq_refl)
           (DSC 1424752 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1424792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157792)) ltac:(img_rd) eq_refl)
           (DSC 1424816 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157824)) ltac:(img_rd) eq_refl)
           (DSC 1424880 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1424920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157920)) ltac:(img_rd) eq_refl)
           (DSC 1424944 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1424984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158016)) ltac:(img_rd) eq_refl)
           (DSC 1425008 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158112)) ltac:(img_rd) eq_refl)
           (DSC 1425072 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158208)) ltac:(img_rd) eq_refl)
           (DSC 1425136 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158304)) ltac:(img_rd) eq_refl)
           (DSC 1425200 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158400)) ltac:(img_rd) eq_refl)
           (DSC 1425264 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1425264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
           (DSC 1425304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158528)) ltac:(img_rd) eq_refl)
           (DSC 1425328 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1425368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158592)) ltac:(img_rd) eq_refl)
           (DSC 1425392 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1425432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158656)) ltac:(img_rd) eq_refl)
           (DSC 1425456 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158752)) ltac:(img_rd) eq_refl)
           (DSC 1425520 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158848)) ltac:(img_rd) eq_refl)
           (DSC 1425584 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158944)) ltac:(img_rd) eq_refl)
           (DSC 1425648 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159040)) ltac:(img_rd) eq_refl)
           (DSC 1425712 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159136)) ltac:(img_rd) eq_refl)
           (DSC 1425776 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159232)) ltac:(img_rd) eq_refl)
           (DSC 1425840 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1425880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159552)) ltac:(img_rd) eq_refl)
           (DSC 1425904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1425944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159584)) ltac:(img_rd) eq_refl)
           (DSC 1425968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1426008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159616)) ltac:(img_rd) eq_refl)
           (DSC 1426032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1426072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159648)) ltac:(img_rd) eq_refl)
           (DSC 1426096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1426136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159776)) ltac:(img_rd) eq_refl)
           (DSC 1426160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1426160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1426200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159872)) ltac:(img_rd) eq_refl)
           (DSC 1426224 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 544)) ltac:(img_rd) eq_refl)
           (DSC 1426264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1426272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1381664)) ltac:(img_rd) eq_refl) (DSC 1426288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1426288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1426328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (XCC 8%nat 7029512 8 0 eq_refl) (XCC 9%nat 1423464 8 1423232 eq_refl) (XCC 10%nat 1423372 4 4294967295 eq_refl) (XCC 11%nat 1423272 8 0 eq_refl) (XCC 12%nat 1423288 8 0 eq_refl)
           (XCC 13%nat 1423240 8 0 eq_refl) (XCC 14%nat 1423248 8 0 eq_refl) (XCC 15%nat 1423224 8 1422992 eq_refl) SOlock SOwpos SOwbase SOrpos SOrend (XCC 16%nat 1422984 8 1422752 eq_refl)
           (XCC 17%nat 1422892 4 4294967295 eq_refl) (XCC 18%nat 1422792 8 0 eq_refl) (XCC 19%nat 1422808 8 0 eq_refl) (XCC 20%nat 1422760 8 0 eq_refl) (XCC 21%nat 1422768 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x137cc8) M R1 (Z_to_bv 64 0x1379d8) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x1379d8) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXe.KS_dpXe; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.


  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_2 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1275140 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6896384 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7027520) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x137cc8) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
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
    assert (SHW : forall a n, ((2147469128 <=? a) && (a + n <=? 2147470932) || (2147623588 <=? a) && (a + n <=? 2147623604) || (2147628820 <=? a) && (a + n <=? 2147629172)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x15b8a0 <=? a) && (a + Z.of_nat n <=? 0x15c3a0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpX2_pre.dpX2_pre_conc fx R MV V
           HS64 Hcan HT64 G1 G2 G4
           HSr HSa CWR CDF IMGc (WSG 1426368 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 1426448 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1430320 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027536 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027544 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027552 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7028080 4%nat ltac:(vm_compute; reflexivity) eq_refl)
           (SHW 2147469128 1 eq_refl) (SHW 2147469129 1 eq_refl) (SHW 2147469130 1 eq_refl) (SHW 2147469131 1 eq_refl) (SHW 2147469132 1 eq_refl) (SHW 2147469132 4 eq_refl)
           (SHW 2147469133 1 eq_refl) (SHW 2147469134 1 eq_refl) (SHW 2147469135 1 eq_refl) (SHW 2147469136 4 eq_refl) (SHW 2147469140 1 eq_refl) (SHW 2147469140 4 eq_refl)
           (SHW 2147469141 1 eq_refl) (SHW 2147469142 1 eq_refl) (SHW 2147469143 1 eq_refl) (SHW 2147469148 1 eq_refl) (SHW 2147469149 1 eq_refl) (SHW 2147469150 1 eq_refl)
           (SHW 2147469151 1 eq_refl) (SHW 2147469152 1 eq_refl) (SHW 2147469152 4 eq_refl) (SHW 2147469153 1 eq_refl) (SHW 2147469154 1 eq_refl) (SHW 2147469155 1 eq_refl)
           (SHW 2147469156 4 eq_refl) (SHW 2147469160 1 eq_refl) (SHW 2147469160 4 eq_refl) (SHW 2147469161 1 eq_refl) (SHW 2147469162 1 eq_refl) (SHW 2147469163 1 eq_refl)
           (SHW 2147469164 1 eq_refl) (SHW 2147469165 1 eq_refl) (SHW 2147469166 1 eq_refl) (SHW 2147469167 1 eq_refl) (SHW 2147469168 1 eq_refl) (SHW 2147469169 1 eq_refl)
           (SHW 2147469170 1 eq_refl) (SHW 2147469171 1 eq_refl) (SHW 2147469172 1 eq_refl) (SHW 2147469173 1 eq_refl) (SHW 2147469174 1 eq_refl) (SHW 2147469175 1 eq_refl)
           (SHW 2147469188 1 eq_refl) (SHW 2147469189 1 eq_refl) (SHW 2147469190 1 eq_refl) (SHW 2147469191 1 eq_refl) (SHW 2147469192 1 eq_refl) (SHW 2147469193 1 eq_refl)
           (SHW 2147469194 1 eq_refl) (SHW 2147469195 1 eq_refl) (SHW 2147469196 1 eq_refl) (SHW 2147469196 4 eq_refl) (SHW 2147469197 1 eq_refl) (SHW 2147469198 1 eq_refl)
           (SHW 2147469199 1 eq_refl) (SHW 2147469200 4 eq_refl) (SHW 2147469204 4 eq_refl) (SHW 2147469208 4 eq_refl) (SHW 2147469212 4 eq_refl) (SHW 2147469216 4 eq_refl)
           (SHW 2147469220 4 eq_refl) (SHW 2147469224 8 eq_refl) (SHW 2147469232 8 eq_refl) (SHW 2147469240 8 eq_refl) (SHW 2147469248 8 eq_refl) (SHW 2147469256 8 eq_refl)
           (SHW 2147469264 8 eq_refl) (SHW 2147469272 8 eq_refl) (SHW 2147469280 8 eq_refl) (SHW 2147469288 8 eq_refl) (SHW 2147469296 8 eq_refl) (SHW 2147469304 8 eq_refl)
           (SHW 2147469312 8 eq_refl) (SHW 2147469320 8 eq_refl) (SHW 2147469328 8 eq_refl) (SHW 2147469336 8 eq_refl) (SHW 2147469344 8 eq_refl) (SHW 2147469352 8 eq_refl)
           (SHW 2147469360 8 eq_refl) (SHW 2147469368 8 eq_refl) (SHW 2147469376 8 eq_refl) (SHW 2147469384 8 eq_refl) (SHW 2147469392 8 eq_refl) (SHW 2147469400 8 eq_refl)
           (SHW 2147469408 8 eq_refl) (SHW 2147469416 8 eq_refl) (SHW 2147469424 8 eq_refl) (SHW 2147469432 8 eq_refl) (SHW 2147469440 8 eq_refl) (SHW 2147469448 8 eq_refl)
           (SHW 2147469456 8 eq_refl) (SHW 2147469464 8 eq_refl) (SHW 2147469472 8 eq_refl) (SHW 2147469480 8 eq_refl) (SHW 2147469488 8 eq_refl) (SHW 2147469496 8 eq_refl)
           (SHW 2147469504 8 eq_refl) (SHW 2147469512 8 eq_refl) (SHW 2147469520 8 eq_refl) (SHW 2147469528 8 eq_refl) (SHW 2147469536 8 eq_refl) (SHW 2147469544 8 eq_refl)
           (SHW 2147469552 8 eq_refl) (SHW 2147469560 8 eq_refl) (SHW 2147469568 8 eq_refl) (SHW 2147469576 8 eq_refl) (SHW 2147469584 8 eq_refl) (SHW 2147469592 8 eq_refl)
           (SHW 2147469600 8 eq_refl) (SHW 2147469608 8 eq_refl) (SHW 2147469616 8 eq_refl) (SHW 2147469624 8 eq_refl) (SHW 2147469632 8 eq_refl) (SHW 2147469640 8 eq_refl)
           (SHW 2147469648 8 eq_refl) (SHW 2147469656 8 eq_refl) (SHW 2147469664 8 eq_refl) (SHW 2147469672 8 eq_refl) (SHW 2147469680 8 eq_refl) (SHW 2147469688 8 eq_refl)
           (SHW 2147469696 8 eq_refl) (SHW 2147469704 8 eq_refl) (SHW 2147469712 8 eq_refl) (SHW 2147469720 8 eq_refl) (SHW 2147469728 8 eq_refl) (SHW 2147469736 8 eq_refl)
           (SHW 2147469744 8 eq_refl) (SHW 2147469752 8 eq_refl) (SHW 2147469760 8 eq_refl) (SHW 2147469768 8 eq_refl) (SHW 2147469776 8 eq_refl) (SHW 2147469784 8 eq_refl)
           (SHW 2147469792 8 eq_refl) (SHW 2147469800 8 eq_refl) (SHW 2147469808 8 eq_refl) (SHW 2147469816 8 eq_refl) (SHW 2147469824 8 eq_refl) (SHW 2147469832 8 eq_refl)
           (SHW 2147469840 8 eq_refl) (SHW 2147469848 8 eq_refl) (SHW 2147469856 8 eq_refl) (SHW 2147469864 8 eq_refl) (SHW 2147469872 8 eq_refl) (SHW 2147469880 8 eq_refl)
           (SHW 2147469888 8 eq_refl) (SHW 2147469896 8 eq_refl) (SHW 2147469904 8 eq_refl) (SHW 2147469912 8 eq_refl) (SHW 2147469920 8 eq_refl) (SHW 2147469928 8 eq_refl)
           (SHW 2147469936 8 eq_refl) (SHW 2147469944 8 eq_refl) (SHW 2147469952 8 eq_refl) (SHW 2147469960 8 eq_refl) (SHW 2147469968 8 eq_refl) (SHW 2147469976 8 eq_refl)
           (SHW 2147469984 8 eq_refl) (SHW 2147469992 8 eq_refl) (SHW 2147470000 8 eq_refl) (SHW 2147470008 8 eq_refl) (SHW 2147470016 8 eq_refl) (SHW 2147470024 4 eq_refl)
           (SHW 2147470028 4 eq_refl) (SHW 2147470032 4 eq_refl) (SHW 2147470036 4 eq_refl) (SHW 2147470040 4 eq_refl) (SHW 2147470044 4 eq_refl) (SHW 2147470048 1 eq_refl)
           (SHW 2147470048 4 eq_refl) (SHW 2147470049 1 eq_refl) (SHW 2147470050 1 eq_refl) (SHW 2147470051 1 eq_refl) (SHW 2147470052 1 eq_refl) (SHW 2147470052 4 eq_refl)
           (SHW 2147470053 1 eq_refl) (SHW 2147470054 1 eq_refl) (SHW 2147470055 1 eq_refl) (SHW 2147470056 4 eq_refl) (SHW 2147470060 4 eq_refl) (SHW 2147470064 4 eq_refl)
           (SHW 2147470068 4 eq_refl) (SHW 2147470072 4 eq_refl) (SHW 2147470076 4 eq_refl) (SHW 2147470080 8 eq_refl) (SHW 2147470088 8 eq_refl) (SHW 2147470096 8 eq_refl)
           (SHW 2147470104 8 eq_refl) (SHW 2147470112 8 eq_refl) (SHW 2147470120 8 eq_refl) (SHW 2147470128 8 eq_refl) (SHW 2147470136 8 eq_refl) (SHW 2147470144 8 eq_refl)
           (SHW 2147470152 8 eq_refl) (SHW 2147470160 8 eq_refl) (SHW 2147470168 8 eq_refl) (SHW 2147470176 8 eq_refl) (SHW 2147470184 8 eq_refl) (SHW 2147470192 8 eq_refl)
           (SHW 2147470200 8 eq_refl) (SHW 2147470208 8 eq_refl) (SHW 2147470216 8 eq_refl) (SHW 2147470224 8 eq_refl) (SHW 2147470232 8 eq_refl) (SHW 2147470240 8 eq_refl)
           (SHW 2147470248 8 eq_refl) (SHW 2147470256 8 eq_refl) (SHW 2147470264 8 eq_refl) (SHW 2147470272 8 eq_refl) (SHW 2147470280 8 eq_refl) (SHW 2147470288 8 eq_refl)
           (SHW 2147470296 8 eq_refl) (SHW 2147470304 8 eq_refl) (SHW 2147470312 8 eq_refl) (SHW 2147470320 8 eq_refl) (SHW 2147470328 8 eq_refl) (SHW 2147470336 8 eq_refl)
           (SHW 2147470344 8 eq_refl) (SHW 2147470352 8 eq_refl) (SHW 2147470360 8 eq_refl) (SHW 2147470368 8 eq_refl) (SHW 2147470376 8 eq_refl) (SHW 2147470384 8 eq_refl)
           (SHW 2147470392 8 eq_refl) (SHW 2147470400 8 eq_refl) (SHW 2147470408 8 eq_refl) (SHW 2147470416 8 eq_refl) (SHW 2147470424 8 eq_refl) (SHW 2147470432 8 eq_refl)
           (SHW 2147470440 8 eq_refl) (SHW 2147470448 8 eq_refl) (SHW 2147470452 4 eq_refl) (SHW 2147470456 4 eq_refl) (SHW 2147470456 8 eq_refl) (SHW 2147470460 4 eq_refl)
           (SHW 2147470464 4 eq_refl) (SHW 2147470468 4 eq_refl) (SHW 2147470472 4 eq_refl) (SHW 2147470476 1 eq_refl) (SHW 2147470476 4 eq_refl) (SHW 2147470477 1 eq_refl)
           (SHW 2147470478 1 eq_refl) (SHW 2147470479 1 eq_refl) (SHW 2147470480 1 eq_refl) (SHW 2147470481 1 eq_refl) (SHW 2147470482 1 eq_refl) (SHW 2147470483 1 eq_refl)
           (SHW 2147470484 1 eq_refl) (SHW 2147470484 4 eq_refl) (SHW 2147470485 1 eq_refl) (SHW 2147470486 1 eq_refl) (SHW 2147470487 1 eq_refl) (SHW 2147470488 4 eq_refl)
           (SHW 2147470492 4 eq_refl) (SHW 2147470496 1 eq_refl) (SHW 2147470496 4 eq_refl) (SHW 2147470497 1 eq_refl) (SHW 2147470498 1 eq_refl) (SHW 2147470499 1 eq_refl)
           (SHW 2147470500 1 eq_refl) (SHW 2147470501 1 eq_refl) (SHW 2147470502 1 eq_refl) (SHW 2147470503 1 eq_refl) (SHW 2147470504 1 eq_refl) (SHW 2147470505 1 eq_refl)
           (SHW 2147470506 1 eq_refl) (SHW 2147470507 1 eq_refl) (SHW 2147470508 1 eq_refl) (SHW 2147470509 1 eq_refl) (SHW 2147470510 1 eq_refl) (SHW 2147470511 1 eq_refl)
           (SHW 2147470512 1 eq_refl) (SHW 2147470513 1 eq_refl) (SHW 2147470514 1 eq_refl) (SHW 2147470515 1 eq_refl) (SHW 2147470516 1 eq_refl) (SHW 2147470517 1 eq_refl)
           (SHW 2147470518 1 eq_refl) (SHW 2147470519 1 eq_refl) (SHW 2147470540 1 eq_refl) (SHW 2147470541 1 eq_refl) (SHW 2147470542 1 eq_refl) (SHW 2147470543 1 eq_refl)
           (SHW 2147470588 1 eq_refl) (SHW 2147470589 1 eq_refl) (SHW 2147470590 1 eq_refl) (SHW 2147470591 1 eq_refl) (SHW 2147470592 1 eq_refl) (SHW 2147470593 1 eq_refl)
           (SHW 2147470594 1 eq_refl) (SHW 2147470595 1 eq_refl) (SHW 2147470596 1 eq_refl) (SHW 2147470597 1 eq_refl) (SHW 2147470598 1 eq_refl) (SHW 2147470599 1 eq_refl)
           (SHW 2147470600 1 eq_refl) (SHW 2147470601 1 eq_refl) (SHW 2147470602 1 eq_refl) (SHW 2147470603 1 eq_refl) (SHW 2147470604 1 eq_refl) (SHW 2147470605 1 eq_refl)
           (SHW 2147470606 1 eq_refl) (SHW 2147470607 1 eq_refl) (SHW 2147470608 1 eq_refl) (SHW 2147470608 4 eq_refl) (SHW 2147470609 1 eq_refl) (SHW 2147470610 1 eq_refl)
           (SHW 2147470611 1 eq_refl) (SHW 2147470612 4 eq_refl) (SHW 2147470616 1 eq_refl) (SHW 2147470616 4 eq_refl) (SHW 2147470617 1 eq_refl) (SHW 2147470618 1 eq_refl)
           (SHW 2147470619 1 eq_refl) (SHW 2147470620 1 eq_refl) (SHW 2147470620 4 eq_refl) (SHW 2147470621 1 eq_refl) (SHW 2147470622 1 eq_refl) (SHW 2147470623 1 eq_refl)
           (SHW 2147470624 4 eq_refl) (SHW 2147470628 1 eq_refl) (SHW 2147470628 4 eq_refl) (SHW 2147470629 1 eq_refl) (SHW 2147470630 1 eq_refl) (SHW 2147470631 1 eq_refl)
           (SHW 2147470632 1 eq_refl) (SHW 2147470632 4 eq_refl) (SHW 2147470633 1 eq_refl) (SHW 2147470634 1 eq_refl) (SHW 2147470635 1 eq_refl) (SHW 2147470636 4 eq_refl)
           (SHW 2147470640 1 eq_refl) (SHW 2147470640 4 eq_refl) (SHW 2147470641 1 eq_refl) (SHW 2147470642 1 eq_refl) (SHW 2147470643 1 eq_refl) (SHW 2147470644 1 eq_refl)
           (SHW 2147470644 4 eq_refl) (SHW 2147470645 1 eq_refl) (SHW 2147470646 1 eq_refl) (SHW 2147470647 1 eq_refl) (SHW 2147470648 4 eq_refl) (SHW 2147470652 1 eq_refl)
           (SHW 2147470652 4 eq_refl) (SHW 2147470653 1 eq_refl) (SHW 2147470654 1 eq_refl) (SHW 2147470655 1 eq_refl) (SHW 2147470656 1 eq_refl) (SHW 2147470656 4 eq_refl)
           (SHW 2147470657 1 eq_refl) (SHW 2147470658 1 eq_refl) (SHW 2147470659 1 eq_refl) (SHW 2147470660 4 eq_refl) (SHW 2147470664 1 eq_refl) (SHW 2147470664 4 eq_refl)
           (SHW 2147470665 1 eq_refl) (SHW 2147470666 1 eq_refl) (SHW 2147470667 1 eq_refl) (SHW 2147470668 1 eq_refl) (SHW 2147470668 4 eq_refl) (SHW 2147470669 1 eq_refl)
           (SHW 2147470670 1 eq_refl) (SHW 2147470671 1 eq_refl) (SHW 2147470672 4 eq_refl) (SHW 2147470676 1 eq_refl) (SHW 2147470676 4 eq_refl) (SHW 2147470677 1 eq_refl)
           (SHW 2147470678 1 eq_refl) (SHW 2147470679 1 eq_refl) (SHW 2147470680 1 eq_refl) (SHW 2147470680 4 eq_refl) (SHW 2147470681 1 eq_refl) (SHW 2147470682 1 eq_refl)
           (SHW 2147470683 1 eq_refl) (SHW 2147470684 4 eq_refl) (SHW 2147470688 4 eq_refl) (SHW 2147470692 1 eq_refl) (SHW 2147470692 4 eq_refl) (SHW 2147470693 1 eq_refl)
           (SHW 2147470694 1 eq_refl) (SHW 2147470695 1 eq_refl) (SHW 2147470696 1 eq_refl) (SHW 2147470697 1 eq_refl) (SHW 2147470698 1 eq_refl) (SHW 2147470699 1 eq_refl)
           (SHW 2147470700 1 eq_refl) (SHW 2147470701 1 eq_refl) (SHW 2147470702 1 eq_refl) (SHW 2147470703 1 eq_refl) (SHW 2147470704 1 eq_refl) (SHW 2147470705 1 eq_refl)
           (SHW 2147470706 1 eq_refl) (SHW 2147470707 1 eq_refl) (SHW 2147470708 1 eq_refl) (SHW 2147470709 1 eq_refl) (SHW 2147470710 1 eq_refl) (SHW 2147470711 1 eq_refl)
           (SHW 2147470712 1 eq_refl) (SHW 2147470712 4 eq_refl) (SHW 2147470713 1 eq_refl) (SHW 2147470714 1 eq_refl) (SHW 2147470715 1 eq_refl) (SHW 2147470716 4 eq_refl)
           (SHW 2147470720 1 eq_refl) (SHW 2147470720 4 eq_refl) (SHW 2147470721 1 eq_refl) (SHW 2147470722 1 eq_refl) (SHW 2147470723 1 eq_refl) (SHW 2147470724 1 eq_refl)
           (SHW 2147470724 4 eq_refl) (SHW 2147470725 1 eq_refl) (SHW 2147470726 1 eq_refl) (SHW 2147470727 1 eq_refl) (SHW 2147470728 4 eq_refl) (SHW 2147470732 1 eq_refl)
           (SHW 2147470732 4 eq_refl) (SHW 2147470733 1 eq_refl) (SHW 2147470734 1 eq_refl) (SHW 2147470735 1 eq_refl) (SHW 2147470736 1 eq_refl) (SHW 2147470736 4 eq_refl)
           (SHW 2147470737 1 eq_refl) (SHW 2147470738 1 eq_refl) (SHW 2147470739 1 eq_refl) (SHW 2147470740 4 eq_refl) (SHW 2147470744 1 eq_refl) (SHW 2147470744 4 eq_refl)
           (SHW 2147470745 1 eq_refl) (SHW 2147470746 1 eq_refl) (SHW 2147470747 1 eq_refl) (SHW 2147470748 1 eq_refl) (SHW 2147470748 4 eq_refl) (SHW 2147470749 1 eq_refl)
           (SHW 2147470750 1 eq_refl) (SHW 2147470751 1 eq_refl) (SHW 2147470752 4 eq_refl) (SHW 2147470756 1 eq_refl) (SHW 2147470756 4 eq_refl) (SHW 2147470757 1 eq_refl)
           (SHW 2147470758 1 eq_refl) (SHW 2147470759 1 eq_refl) (SHW 2147470760 1 eq_refl) (SHW 2147470760 4 eq_refl) (SHW 2147470761 1 eq_refl) (SHW 2147470762 1 eq_refl)
           (SHW 2147470763 1 eq_refl) (SHW 2147470764 4 eq_refl) (SHW 2147470768 1 eq_refl) (SHW 2147470768 4 eq_refl) (SHW 2147470769 1 eq_refl) (SHW 2147470770 1 eq_refl)
           (SHW 2147470771 1 eq_refl) (SHW 2147470772 1 eq_refl) (SHW 2147470772 4 eq_refl) (SHW 2147470773 1 eq_refl) (SHW 2147470774 1 eq_refl) (SHW 2147470775 1 eq_refl)
           (SHW 2147470776 4 eq_refl) (SHW 2147470780 1 eq_refl) (SHW 2147470780 4 eq_refl) (SHW 2147470781 1 eq_refl) (SHW 2147470782 1 eq_refl) (SHW 2147470783 1 eq_refl)
           (SHW 2147470784 1 eq_refl) (SHW 2147470785 1 eq_refl) (SHW 2147470786 1 eq_refl) (SHW 2147470787 1 eq_refl) (SHW 2147470824 1 eq_refl) (SHW 2147470825 1 eq_refl)
           (SHW 2147470826 1 eq_refl) (SHW 2147470827 1 eq_refl) (SHW 2147470828 1 eq_refl) (SHW 2147470829 1 eq_refl) (SHW 2147470830 1 eq_refl) (SHW 2147470831 1 eq_refl)
           (SHW 2147470832 1 eq_refl) (SHW 2147470833 1 eq_refl) (SHW 2147470834 1 eq_refl) (SHW 2147470835 1 eq_refl) (SHW 2147470836 1 eq_refl) (SHW 2147470837 1 eq_refl)
           (SHW 2147470838 1 eq_refl) (SHW 2147470839 1 eq_refl) (SHW 2147470852 1 eq_refl) (SHW 2147470852 4 eq_refl) (SHW 2147470853 1 eq_refl) (SHW 2147470854 1 eq_refl)
           (SHW 2147470855 1 eq_refl) (SHW 2147470856 4 eq_refl) (SHW 2147470860 1 eq_refl) (SHW 2147470860 4 eq_refl) (SHW 2147470861 1 eq_refl) (SHW 2147470862 1 eq_refl)
           (SHW 2147470863 1 eq_refl) (SHW 2147470864 1 eq_refl) (SHW 2147470864 4 eq_refl) (SHW 2147470865 1 eq_refl) (SHW 2147470866 1 eq_refl) (SHW 2147470867 1 eq_refl)
           (SHW 2147470868 4 eq_refl) (SHW 2147470872 4 eq_refl) (SHW 2147470876 4 eq_refl) (SHW 2147470880 4 eq_refl) (SHW 2147470884 4 eq_refl) (SHW 2147470888 4 eq_refl)
           (SHW 2147470888 8 eq_refl) (SHW 2147470896 8 eq_refl) (SHW 2147470904 4 eq_refl) (SHW 2147470904 8 eq_refl) (SHW 2147470908 4 eq_refl) (SHW 2147470912 4 eq_refl)
           (SHW 2147470912 8 eq_refl) (SHW 2147470916 4 eq_refl) (SHW 2147470920 4 eq_refl) (SHW 2147470924 4 eq_refl) (SHW 2147470928 1 eq_refl) (SHW 2147470928 4 eq_refl)
           (SHW 2147470929 1 eq_refl) (SHW 2147470930 1 eq_refl) (SHW 2147470931 1 eq_refl) (SHW 2147623588 1 eq_refl) (SHW 2147623588 4 eq_refl) (SHW 2147623589 1 eq_refl)
           (SHW 2147623590 1 eq_refl) (SHW 2147623591 1 eq_refl) (SHW 2147623592 4 eq_refl) (SHW 2147623596 4 eq_refl) (SHW 2147623600 1 eq_refl) (SHW 2147623600 4 eq_refl)
           (SHW 2147623601 1 eq_refl) (SHW 2147623602 1 eq_refl) (SHW 2147623603 1 eq_refl) (SHW 2147628820 1 eq_refl) (SHW 2147628820 4 eq_refl) (SHW 2147628821 1 eq_refl)
           (SHW 2147628822 1 eq_refl) (SHW 2147628823 1 eq_refl) (SHW 2147628824 4 eq_refl) (SHW 2147628828 4 eq_refl) (SHW 2147628832 4 eq_refl) (SHW 2147628836 4 eq_refl)
           (SHW 2147628840 4 eq_refl) (SHW 2147628844 4 eq_refl) (SHW 2147628848 8 eq_refl) (SHW 2147628856 8 eq_refl) (SHW 2147628864 8 eq_refl) (SHW 2147628872 8 eq_refl)
           (SHW 2147628880 8 eq_refl) (SHW 2147628888 8 eq_refl) (SHW 2147628896 8 eq_refl) (SHW 2147628904 8 eq_refl) (SHW 2147628912 8 eq_refl) (SHW 2147628920 8 eq_refl)
           (SHW 2147628928 8 eq_refl) (SHW 2147628936 8 eq_refl) (SHW 2147628944 8 eq_refl) (SHW 2147628952 8 eq_refl) (SHW 2147628960 8 eq_refl) (SHW 2147628968 8 eq_refl)
           (SHW 2147628976 8 eq_refl) (SHW 2147628984 8 eq_refl) (SHW 2147628992 8 eq_refl) (SHW 2147629000 8 eq_refl) (SHW 2147629008 8 eq_refl) (SHW 2147629016 8 eq_refl)
           (SHW 2147629024 8 eq_refl) (SHW 2147629032 8 eq_refl) (SHW 2147629040 8 eq_refl) (SHW 2147629048 8 eq_refl) (SHW 2147629056 8 eq_refl) (SHW 2147629064 8 eq_refl)
           (SHW 2147629072 8 eq_refl) (SHW 2147629080 8 eq_refl) (SHW 2147629088 8 eq_refl) (SHW 2147629096 8 eq_refl) (SHW 2147629104 8 eq_refl) (SHW 2147629112 8 eq_refl)
           (SHW 2147629120 8 eq_refl) (SHW 2147629128 8 eq_refl) (SHW 2147629136 8 eq_refl) (SHW 2147629144 8 eq_refl) (SHW 2147629144 4 eq_refl) (SHW 2147629148 4 eq_refl)
           (SHW 2147629152 8 eq_refl) (SHW 2147629152 4 eq_refl) (SHW 2147629156 4 eq_refl) (SHW 2147629160 8 eq_refl) (SHW 2147629160 4 eq_refl) (SHW 2147629164 4 eq_refl)
           (SHW 2147629168 1 eq_refl) (SHW 2147629168 4 eq_refl) (SHW 2147629169 1 eq_refl) (SHW 2147629170 1 eq_refl) (SHW 2147629171 1 eq_refl) TIDC
           HTr (XCC 0%nat 7028080 4 0 eq_refl) (XCC1 1%nat 7028115 0 eq_refl eq_refl) (XCC 2%nat 7027552 8 7027560 eq_refl) (XCC 3%nat 7027544 4 2 eq_refl) (XCC 22%nat 7027576 8 1277044 eq_refl)
           (XCC 23%nat 7027832 8 716372 eq_refl) (XCC 6%nat 7027540 4 0 eq_refl) (XCC1 24%nat 6889684 0 eq_refl eq_refl) (XCC 4%nat 7027568 8 1277044 eq_refl) (XCC 5%nat 7027824 8 648332 eq_refl) (STC1 10%nat 2038048 0 eq_refl eq_refl)
           (XCC 7%nat 7027560 8 0 eq_refl) (STC1 3%nat 1426448 0 eq_refl eq_refl) (STC 0%nat 1412008 8 1412008 eq_refl) (STC 2%nat 1426368 8 1 eq_refl) (STC 4%nat 1430160 4 1 eq_refl) (STC 5%nat 1430320 8 0 eq_refl)
           (STC1 8%nat 1443672 1 eq_refl eq_refl) (STC 7%nat 1440376 8 2147450880 eq_refl) (DSC 1423520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145984)) ltac:(img_rd) eq_refl) (DSC 1423536 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1438428 1 eq_refl eq_refl) (DSC 1423536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (STC 9%nat 2037280 8 18446744073709551615 eq_refl) (STC 1%nat 1412520 8 1347948 eq_refl) (DSC 1423576 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146016)) ltac:(img_rd) eq_refl) (DSC 1423600 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1423640 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146144)) ltac:(img_rd) eq_refl) (DSC 1423664 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146176)) ltac:(img_rd) eq_refl)
           (DSC 1423728 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1423768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146272)) ltac:(img_rd) eq_refl) (DSC 1423792 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1423832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146304)) ltac:(img_rd) eq_refl) (DSC 1423856 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1423856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1423896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146464)) ltac:(img_rd) eq_refl)
           (DSC 1423920 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl) (DSC 1423984 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146528)) ltac:(img_rd) eq_refl) (DSC 1424048 1%nat [Z_to_bv 8 192] ltac:(img_rd) eq_refl) (DSC 1424048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 6848)) ltac:(img_rd) eq_refl) (DSC 1424088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 153376)) ltac:(img_rd) eq_refl)
           (DSC 1424112 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 3424)) ltac:(img_rd) eq_refl) (DSC 1424152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156800)) ltac:(img_rd) eq_refl) (DSC 1424176 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156832)) ltac:(img_rd) eq_refl) (DSC 1424240 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1424240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1424280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156960)) ltac:(img_rd) eq_refl)
           (DSC 1424304 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156992)) ltac:(img_rd) eq_refl) (DSC 1424368 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157024)) ltac:(img_rd) eq_refl) (DSC 1424432 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157056)) ltac:(img_rd) eq_refl)
           (DSC 1424496 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157088)) ltac:(img_rd) eq_refl) (DSC 1424560 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157280)) ltac:(img_rd) eq_refl) (DSC 1424624 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157664)) ltac:(img_rd) eq_refl)
           (DSC 1424688 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1424728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157728)) ltac:(img_rd) eq_refl) (DSC 1424752 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1424792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157792)) ltac:(img_rd) eq_refl) (DSC 1424816 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157824)) ltac:(img_rd) eq_refl)
           (DSC 1424880 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1424920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157920)) ltac:(img_rd) eq_refl) (DSC 1424944 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1424984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158016)) ltac:(img_rd) eq_refl) (DSC 1425008 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158112)) ltac:(img_rd) eq_refl)
           (DSC 1425072 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158208)) ltac:(img_rd) eq_refl) (DSC 1425136 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158304)) ltac:(img_rd) eq_refl) (DSC 1425200 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158400)) ltac:(img_rd) eq_refl)
           (DSC 1425264 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1425264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1425304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158528)) ltac:(img_rd) eq_refl) (DSC 1425328 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1425368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158592)) ltac:(img_rd) eq_refl) (DSC 1425392 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1425432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158656)) ltac:(img_rd) eq_refl)
           (DSC 1425456 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158752)) ltac:(img_rd) eq_refl) (DSC 1425520 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158848)) ltac:(img_rd) eq_refl) (DSC 1425584 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158944)) ltac:(img_rd) eq_refl)
           (DSC 1425648 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159040)) ltac:(img_rd) eq_refl) (DSC 1425712 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159136)) ltac:(img_rd) eq_refl) (DSC 1425776 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159232)) ltac:(img_rd) eq_refl)
           (DSC 1425840 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1425880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159552)) ltac:(img_rd) eq_refl) (DSC 1425904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1425944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159584)) ltac:(img_rd) eq_refl) (DSC 1425968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159616)) ltac:(img_rd) eq_refl)
           (DSC 1426032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159648)) ltac:(img_rd) eq_refl) (DSC 1426096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1426136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159776)) ltac:(img_rd) eq_refl) (DSC 1426160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1426160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1426200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159872)) ltac:(img_rd) eq_refl)
           (DSC 1426224 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 544)) ltac:(img_rd) eq_refl) (DSC 1426264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1381664)) ltac:(img_rd) eq_refl) (DSC 1426288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1426288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
           (DSC 1426328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 7029512 8 0 eq_refl) (XCC 9%nat 1423464 8 1423232 eq_refl) (XCC 10%nat 1423372 4 4294967295 eq_refl) (XCC 11%nat 1423272 8 0 eq_refl) (XCC 12%nat 1423288 8 0 eq_refl)
           (XCC 13%nat 1423240 8 0 eq_refl) (XCC 14%nat 1423248 8 0 eq_refl) (XCC 15%nat 1423224 8 1422992 eq_refl) SOlock SOwpos SOwbase
           SOwrite CANc SOfd) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
    set (good := fun i : Z => i < 1426336 \/ 1430328 <= i < 7027536 \/ 7027560 <= i < 7028080 \/ 7028084 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x137cc8) M R1 (Z_to_bv 64 0x13f6ac) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1426336) || ((1430328 <=? a) && (a + Z.of_nat n <=? 7027536)) || ((7028084 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7029536) (Z.to_nat (2 * 1)) = Some (zero_lines 1%nat)).
    { apply (LITX 7029536 (Z.to_nat (2 * 1))); [|reflexivity]. change (Z.to_nat (2 * 1)) with (2 * 1%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. reflexivity. }
    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1422992 /\ (1422992 + 124 <= q \/ q + 32 + 16 <= 1422992 + 120) /\ 1422992 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 1%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1422992 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 1%nat)%nat true R1 M1 model1 q 2 7029536 (2 * 1) 0 0 (zero_lines 1%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 1426336) || ((1430328 <=? a) && (a + Z.of_nat n <=? 7027536)) || ((7028084 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 1422992 <= a -> a + n <= 1422992 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1409024 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1422992) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7027520) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
           DDF IMG3 (fun d k Hd Hk => FW3 1423024 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1423032 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1423048 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1423080 8%nat _ SObuf eq_refl)
           (LIT3 1423088 8%nat _ SObufsz eq_refl) (LIT3 7027520 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
           (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1423000 8%nat _ SOrpos eq_refl)
           (LIT3 1423008 8%nat _ SOrend eq_refl) (LIT3 1422984 8%nat _ (XCC 16%nat 1422984 8 1422752 eq_refl) eq_refl) (LIT3 1422892 4%nat _ (XCC 17%nat 1422892 4 4294967295 eq_refl) eq_refl) (LIT3 1422792 8%nat _ (XCC 18%nat 1422792 8 0 eq_refl) eq_refl) (LIT3 1422808 8%nat _ (XCC 19%nat 1422808 8 0 eq_refl) eq_refl) (LIT3 1422760 8%nat _ (XCC 20%nat 1422760 8 0 eq_refl) eq_refl)
           (LIT3 1422768 8%nat _ (XCC 21%nat 1422768 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x13f6b8) M3 R4 (Z_to_bv 64 0x1379d8) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x1379d8) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.


  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_3 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1275140 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6896384 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7027520) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x137cc8) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
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
    assert (SHW : forall a n, ((2147469128 <=? a) && (a + n <=? 2147470932) || (2147623588 <=? a) && (a + n <=? 2147623604) || (2147628820 <=? a) && (a + n <=? 2147629172)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x15b8a0 <=? a) && (a + Z.of_nat n <=? 0x15c3a0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpX3_pre.dpX3_pre_conc fx R MV V
           HS64 Hcan HT64 G1 G2 G4
           HSr HSa CWR CDF IMGc (WSG 1426368 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 1426448 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1430320 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027536 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027544 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027552 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7028080 4%nat ltac:(vm_compute; reflexivity) eq_refl)
           (SHW 2147469128 1 eq_refl) (SHW 2147469129 1 eq_refl) (SHW 2147469130 1 eq_refl) (SHW 2147469131 1 eq_refl) (SHW 2147469132 1 eq_refl) (SHW 2147469132 4 eq_refl)
           (SHW 2147469133 1 eq_refl) (SHW 2147469134 1 eq_refl) (SHW 2147469135 1 eq_refl) (SHW 2147469136 4 eq_refl) (SHW 2147469140 1 eq_refl) (SHW 2147469140 4 eq_refl)
           (SHW 2147469141 1 eq_refl) (SHW 2147469142 1 eq_refl) (SHW 2147469143 1 eq_refl) (SHW 2147469148 1 eq_refl) (SHW 2147469149 1 eq_refl) (SHW 2147469150 1 eq_refl)
           (SHW 2147469151 1 eq_refl) (SHW 2147469152 1 eq_refl) (SHW 2147469152 4 eq_refl) (SHW 2147469153 1 eq_refl) (SHW 2147469154 1 eq_refl) (SHW 2147469155 1 eq_refl)
           (SHW 2147469156 4 eq_refl) (SHW 2147469160 1 eq_refl) (SHW 2147469160 4 eq_refl) (SHW 2147469161 1 eq_refl) (SHW 2147469162 1 eq_refl) (SHW 2147469163 1 eq_refl)
           (SHW 2147469164 1 eq_refl) (SHW 2147469165 1 eq_refl) (SHW 2147469166 1 eq_refl) (SHW 2147469167 1 eq_refl) (SHW 2147469168 1 eq_refl) (SHW 2147469169 1 eq_refl)
           (SHW 2147469170 1 eq_refl) (SHW 2147469171 1 eq_refl) (SHW 2147469172 1 eq_refl) (SHW 2147469173 1 eq_refl) (SHW 2147469174 1 eq_refl) (SHW 2147469175 1 eq_refl)
           (SHW 2147469188 1 eq_refl) (SHW 2147469189 1 eq_refl) (SHW 2147469190 1 eq_refl) (SHW 2147469191 1 eq_refl) (SHW 2147469192 1 eq_refl) (SHW 2147469193 1 eq_refl)
           (SHW 2147469194 1 eq_refl) (SHW 2147469195 1 eq_refl) (SHW 2147469196 1 eq_refl) (SHW 2147469196 4 eq_refl) (SHW 2147469197 1 eq_refl) (SHW 2147469198 1 eq_refl)
           (SHW 2147469199 1 eq_refl) (SHW 2147469200 4 eq_refl) (SHW 2147469204 4 eq_refl) (SHW 2147469208 4 eq_refl) (SHW 2147469212 4 eq_refl) (SHW 2147469216 4 eq_refl)
           (SHW 2147469220 4 eq_refl) (SHW 2147469224 8 eq_refl) (SHW 2147469232 8 eq_refl) (SHW 2147469240 8 eq_refl) (SHW 2147469248 8 eq_refl) (SHW 2147469256 8 eq_refl)
           (SHW 2147469264 8 eq_refl) (SHW 2147469272 8 eq_refl) (SHW 2147469280 8 eq_refl) (SHW 2147469288 8 eq_refl) (SHW 2147469296 8 eq_refl) (SHW 2147469304 8 eq_refl)
           (SHW 2147469312 8 eq_refl) (SHW 2147469320 8 eq_refl) (SHW 2147469328 8 eq_refl) (SHW 2147469336 8 eq_refl) (SHW 2147469344 8 eq_refl) (SHW 2147469352 8 eq_refl)
           (SHW 2147469360 8 eq_refl) (SHW 2147469368 8 eq_refl) (SHW 2147469376 8 eq_refl) (SHW 2147469384 8 eq_refl) (SHW 2147469392 8 eq_refl) (SHW 2147469400 8 eq_refl)
           (SHW 2147469408 8 eq_refl) (SHW 2147469416 8 eq_refl) (SHW 2147469424 8 eq_refl) (SHW 2147469432 8 eq_refl) (SHW 2147469440 8 eq_refl) (SHW 2147469448 8 eq_refl)
           (SHW 2147469456 8 eq_refl) (SHW 2147469464 8 eq_refl) (SHW 2147469472 8 eq_refl) (SHW 2147469480 8 eq_refl) (SHW 2147469488 8 eq_refl) (SHW 2147469496 8 eq_refl)
           (SHW 2147469504 8 eq_refl) (SHW 2147469512 8 eq_refl) (SHW 2147469520 8 eq_refl) (SHW 2147469528 8 eq_refl) (SHW 2147469536 8 eq_refl) (SHW 2147469544 8 eq_refl)
           (SHW 2147469552 8 eq_refl) (SHW 2147469560 8 eq_refl) (SHW 2147469568 8 eq_refl) (SHW 2147469576 8 eq_refl) (SHW 2147469584 8 eq_refl) (SHW 2147469592 8 eq_refl)
           (SHW 2147469600 8 eq_refl) (SHW 2147469608 8 eq_refl) (SHW 2147469616 8 eq_refl) (SHW 2147469624 8 eq_refl) (SHW 2147469632 8 eq_refl) (SHW 2147469640 8 eq_refl)
           (SHW 2147469648 8 eq_refl) (SHW 2147469656 8 eq_refl) (SHW 2147469664 8 eq_refl) (SHW 2147469672 8 eq_refl) (SHW 2147469680 8 eq_refl) (SHW 2147469688 8 eq_refl)
           (SHW 2147469696 8 eq_refl) (SHW 2147469704 8 eq_refl) (SHW 2147469712 8 eq_refl) (SHW 2147469720 8 eq_refl) (SHW 2147469728 8 eq_refl) (SHW 2147469736 8 eq_refl)
           (SHW 2147469744 8 eq_refl) (SHW 2147469752 8 eq_refl) (SHW 2147469760 8 eq_refl) (SHW 2147469768 8 eq_refl) (SHW 2147469776 8 eq_refl) (SHW 2147469784 8 eq_refl)
           (SHW 2147469792 8 eq_refl) (SHW 2147469800 8 eq_refl) (SHW 2147469808 8 eq_refl) (SHW 2147469816 8 eq_refl) (SHW 2147469824 8 eq_refl) (SHW 2147469832 8 eq_refl)
           (SHW 2147469840 8 eq_refl) (SHW 2147469848 8 eq_refl) (SHW 2147469856 8 eq_refl) (SHW 2147469864 8 eq_refl) (SHW 2147469872 8 eq_refl) (SHW 2147469880 8 eq_refl)
           (SHW 2147469888 8 eq_refl) (SHW 2147469896 8 eq_refl) (SHW 2147469904 8 eq_refl) (SHW 2147469912 8 eq_refl) (SHW 2147469920 8 eq_refl) (SHW 2147469928 8 eq_refl)
           (SHW 2147469936 8 eq_refl) (SHW 2147469944 8 eq_refl) (SHW 2147469952 8 eq_refl) (SHW 2147469960 8 eq_refl) (SHW 2147469968 8 eq_refl) (SHW 2147469976 8 eq_refl)
           (SHW 2147469984 8 eq_refl) (SHW 2147469992 8 eq_refl) (SHW 2147470000 8 eq_refl) (SHW 2147470008 8 eq_refl) (SHW 2147470016 8 eq_refl) (SHW 2147470024 4 eq_refl)
           (SHW 2147470028 4 eq_refl) (SHW 2147470032 4 eq_refl) (SHW 2147470036 4 eq_refl) (SHW 2147470040 4 eq_refl) (SHW 2147470044 4 eq_refl) (SHW 2147470048 1 eq_refl)
           (SHW 2147470048 4 eq_refl) (SHW 2147470049 1 eq_refl) (SHW 2147470050 1 eq_refl) (SHW 2147470051 1 eq_refl) (SHW 2147470052 1 eq_refl) (SHW 2147470052 4 eq_refl)
           (SHW 2147470053 1 eq_refl) (SHW 2147470054 1 eq_refl) (SHW 2147470055 1 eq_refl) (SHW 2147470056 4 eq_refl) (SHW 2147470060 4 eq_refl) (SHW 2147470064 4 eq_refl)
           (SHW 2147470068 4 eq_refl) (SHW 2147470072 4 eq_refl) (SHW 2147470076 4 eq_refl) (SHW 2147470080 8 eq_refl) (SHW 2147470088 8 eq_refl) (SHW 2147470096 8 eq_refl)
           (SHW 2147470104 8 eq_refl) (SHW 2147470112 8 eq_refl) (SHW 2147470120 8 eq_refl) (SHW 2147470128 8 eq_refl) (SHW 2147470136 8 eq_refl) (SHW 2147470144 8 eq_refl)
           (SHW 2147470152 8 eq_refl) (SHW 2147470160 8 eq_refl) (SHW 2147470168 8 eq_refl) (SHW 2147470176 8 eq_refl) (SHW 2147470184 8 eq_refl) (SHW 2147470192 8 eq_refl)
           (SHW 2147470200 8 eq_refl) (SHW 2147470208 8 eq_refl) (SHW 2147470216 8 eq_refl) (SHW 2147470224 8 eq_refl) (SHW 2147470232 8 eq_refl) (SHW 2147470240 8 eq_refl)
           (SHW 2147470248 8 eq_refl) (SHW 2147470256 8 eq_refl) (SHW 2147470264 8 eq_refl) (SHW 2147470272 8 eq_refl) (SHW 2147470280 8 eq_refl) (SHW 2147470288 8 eq_refl)
           (SHW 2147470296 8 eq_refl) (SHW 2147470304 8 eq_refl) (SHW 2147470312 8 eq_refl) (SHW 2147470320 8 eq_refl) (SHW 2147470328 8 eq_refl) (SHW 2147470336 8 eq_refl)
           (SHW 2147470344 8 eq_refl) (SHW 2147470352 8 eq_refl) (SHW 2147470360 8 eq_refl) (SHW 2147470368 8 eq_refl) (SHW 2147470376 8 eq_refl) (SHW 2147470384 8 eq_refl)
           (SHW 2147470392 8 eq_refl) (SHW 2147470400 8 eq_refl) (SHW 2147470408 8 eq_refl) (SHW 2147470416 8 eq_refl) (SHW 2147470424 8 eq_refl) (SHW 2147470432 8 eq_refl)
           (SHW 2147470440 8 eq_refl) (SHW 2147470448 8 eq_refl) (SHW 2147470452 4 eq_refl) (SHW 2147470456 4 eq_refl) (SHW 2147470456 8 eq_refl) (SHW 2147470460 4 eq_refl)
           (SHW 2147470464 4 eq_refl) (SHW 2147470468 4 eq_refl) (SHW 2147470472 4 eq_refl) (SHW 2147470476 1 eq_refl) (SHW 2147470476 4 eq_refl) (SHW 2147470477 1 eq_refl)
           (SHW 2147470478 1 eq_refl) (SHW 2147470479 1 eq_refl) (SHW 2147470480 1 eq_refl) (SHW 2147470481 1 eq_refl) (SHW 2147470482 1 eq_refl) (SHW 2147470483 1 eq_refl)
           (SHW 2147470484 1 eq_refl) (SHW 2147470484 4 eq_refl) (SHW 2147470485 1 eq_refl) (SHW 2147470486 1 eq_refl) (SHW 2147470487 1 eq_refl) (SHW 2147470488 4 eq_refl)
           (SHW 2147470492 4 eq_refl) (SHW 2147470496 1 eq_refl) (SHW 2147470496 4 eq_refl) (SHW 2147470497 1 eq_refl) (SHW 2147470498 1 eq_refl) (SHW 2147470499 1 eq_refl)
           (SHW 2147470500 1 eq_refl) (SHW 2147470501 1 eq_refl) (SHW 2147470502 1 eq_refl) (SHW 2147470503 1 eq_refl) (SHW 2147470504 1 eq_refl) (SHW 2147470505 1 eq_refl)
           (SHW 2147470506 1 eq_refl) (SHW 2147470507 1 eq_refl) (SHW 2147470508 1 eq_refl) (SHW 2147470509 1 eq_refl) (SHW 2147470510 1 eq_refl) (SHW 2147470511 1 eq_refl)
           (SHW 2147470512 1 eq_refl) (SHW 2147470513 1 eq_refl) (SHW 2147470514 1 eq_refl) (SHW 2147470515 1 eq_refl) (SHW 2147470516 1 eq_refl) (SHW 2147470517 1 eq_refl)
           (SHW 2147470518 1 eq_refl) (SHW 2147470519 1 eq_refl) (SHW 2147470540 1 eq_refl) (SHW 2147470541 1 eq_refl) (SHW 2147470542 1 eq_refl) (SHW 2147470543 1 eq_refl)
           (SHW 2147470588 1 eq_refl) (SHW 2147470589 1 eq_refl) (SHW 2147470590 1 eq_refl) (SHW 2147470591 1 eq_refl) (SHW 2147470592 1 eq_refl) (SHW 2147470593 1 eq_refl)
           (SHW 2147470594 1 eq_refl) (SHW 2147470595 1 eq_refl) (SHW 2147470596 1 eq_refl) (SHW 2147470597 1 eq_refl) (SHW 2147470598 1 eq_refl) (SHW 2147470599 1 eq_refl)
           (SHW 2147470600 1 eq_refl) (SHW 2147470601 1 eq_refl) (SHW 2147470602 1 eq_refl) (SHW 2147470603 1 eq_refl) (SHW 2147470604 1 eq_refl) (SHW 2147470605 1 eq_refl)
           (SHW 2147470606 1 eq_refl) (SHW 2147470607 1 eq_refl) (SHW 2147470608 1 eq_refl) (SHW 2147470608 4 eq_refl) (SHW 2147470609 1 eq_refl) (SHW 2147470610 1 eq_refl)
           (SHW 2147470611 1 eq_refl) (SHW 2147470612 4 eq_refl) (SHW 2147470616 1 eq_refl) (SHW 2147470616 4 eq_refl) (SHW 2147470617 1 eq_refl) (SHW 2147470618 1 eq_refl)
           (SHW 2147470619 1 eq_refl) (SHW 2147470620 1 eq_refl) (SHW 2147470620 4 eq_refl) (SHW 2147470621 1 eq_refl) (SHW 2147470622 1 eq_refl) (SHW 2147470623 1 eq_refl)
           (SHW 2147470624 4 eq_refl) (SHW 2147470628 1 eq_refl) (SHW 2147470628 4 eq_refl) (SHW 2147470629 1 eq_refl) (SHW 2147470630 1 eq_refl) (SHW 2147470631 1 eq_refl)
           (SHW 2147470632 1 eq_refl) (SHW 2147470632 4 eq_refl) (SHW 2147470633 1 eq_refl) (SHW 2147470634 1 eq_refl) (SHW 2147470635 1 eq_refl) (SHW 2147470636 4 eq_refl)
           (SHW 2147470640 1 eq_refl) (SHW 2147470640 4 eq_refl) (SHW 2147470641 1 eq_refl) (SHW 2147470642 1 eq_refl) (SHW 2147470643 1 eq_refl) (SHW 2147470644 1 eq_refl)
           (SHW 2147470644 4 eq_refl) (SHW 2147470645 1 eq_refl) (SHW 2147470646 1 eq_refl) (SHW 2147470647 1 eq_refl) (SHW 2147470648 4 eq_refl) (SHW 2147470652 1 eq_refl)
           (SHW 2147470652 4 eq_refl) (SHW 2147470653 1 eq_refl) (SHW 2147470654 1 eq_refl) (SHW 2147470655 1 eq_refl) (SHW 2147470656 1 eq_refl) (SHW 2147470656 4 eq_refl)
           (SHW 2147470657 1 eq_refl) (SHW 2147470658 1 eq_refl) (SHW 2147470659 1 eq_refl) (SHW 2147470660 4 eq_refl) (SHW 2147470664 1 eq_refl) (SHW 2147470664 4 eq_refl)
           (SHW 2147470665 1 eq_refl) (SHW 2147470666 1 eq_refl) (SHW 2147470667 1 eq_refl) (SHW 2147470668 1 eq_refl) (SHW 2147470668 4 eq_refl) (SHW 2147470669 1 eq_refl)
           (SHW 2147470670 1 eq_refl) (SHW 2147470671 1 eq_refl) (SHW 2147470672 4 eq_refl) (SHW 2147470676 1 eq_refl) (SHW 2147470676 4 eq_refl) (SHW 2147470677 1 eq_refl)
           (SHW 2147470678 1 eq_refl) (SHW 2147470679 1 eq_refl) (SHW 2147470680 1 eq_refl) (SHW 2147470680 4 eq_refl) (SHW 2147470681 1 eq_refl) (SHW 2147470682 1 eq_refl)
           (SHW 2147470683 1 eq_refl) (SHW 2147470684 4 eq_refl) (SHW 2147470688 4 eq_refl) (SHW 2147470692 1 eq_refl) (SHW 2147470692 4 eq_refl) (SHW 2147470693 1 eq_refl)
           (SHW 2147470694 1 eq_refl) (SHW 2147470695 1 eq_refl) (SHW 2147470696 1 eq_refl) (SHW 2147470697 1 eq_refl) (SHW 2147470698 1 eq_refl) (SHW 2147470699 1 eq_refl)
           (SHW 2147470700 1 eq_refl) (SHW 2147470701 1 eq_refl) (SHW 2147470702 1 eq_refl) (SHW 2147470703 1 eq_refl) (SHW 2147470704 1 eq_refl) (SHW 2147470705 1 eq_refl)
           (SHW 2147470706 1 eq_refl) (SHW 2147470707 1 eq_refl) (SHW 2147470708 1 eq_refl) (SHW 2147470709 1 eq_refl) (SHW 2147470710 1 eq_refl) (SHW 2147470711 1 eq_refl)
           (SHW 2147470712 1 eq_refl) (SHW 2147470712 4 eq_refl) (SHW 2147470713 1 eq_refl) (SHW 2147470714 1 eq_refl) (SHW 2147470715 1 eq_refl) (SHW 2147470716 4 eq_refl)
           (SHW 2147470720 1 eq_refl) (SHW 2147470720 4 eq_refl) (SHW 2147470721 1 eq_refl) (SHW 2147470722 1 eq_refl) (SHW 2147470723 1 eq_refl) (SHW 2147470724 1 eq_refl)
           (SHW 2147470724 4 eq_refl) (SHW 2147470725 1 eq_refl) (SHW 2147470726 1 eq_refl) (SHW 2147470727 1 eq_refl) (SHW 2147470728 4 eq_refl) (SHW 2147470732 1 eq_refl)
           (SHW 2147470732 4 eq_refl) (SHW 2147470733 1 eq_refl) (SHW 2147470734 1 eq_refl) (SHW 2147470735 1 eq_refl) (SHW 2147470736 1 eq_refl) (SHW 2147470736 4 eq_refl)
           (SHW 2147470737 1 eq_refl) (SHW 2147470738 1 eq_refl) (SHW 2147470739 1 eq_refl) (SHW 2147470740 4 eq_refl) (SHW 2147470744 1 eq_refl) (SHW 2147470744 4 eq_refl)
           (SHW 2147470745 1 eq_refl) (SHW 2147470746 1 eq_refl) (SHW 2147470747 1 eq_refl) (SHW 2147470748 1 eq_refl) (SHW 2147470748 4 eq_refl) (SHW 2147470749 1 eq_refl)
           (SHW 2147470750 1 eq_refl) (SHW 2147470751 1 eq_refl) (SHW 2147470752 4 eq_refl) (SHW 2147470756 1 eq_refl) (SHW 2147470756 4 eq_refl) (SHW 2147470757 1 eq_refl)
           (SHW 2147470758 1 eq_refl) (SHW 2147470759 1 eq_refl) (SHW 2147470760 1 eq_refl) (SHW 2147470760 4 eq_refl) (SHW 2147470761 1 eq_refl) (SHW 2147470762 1 eq_refl)
           (SHW 2147470763 1 eq_refl) (SHW 2147470764 4 eq_refl) (SHW 2147470768 1 eq_refl) (SHW 2147470768 4 eq_refl) (SHW 2147470769 1 eq_refl) (SHW 2147470770 1 eq_refl)
           (SHW 2147470771 1 eq_refl) (SHW 2147470772 1 eq_refl) (SHW 2147470772 4 eq_refl) (SHW 2147470773 1 eq_refl) (SHW 2147470774 1 eq_refl) (SHW 2147470775 1 eq_refl)
           (SHW 2147470776 4 eq_refl) (SHW 2147470780 1 eq_refl) (SHW 2147470780 4 eq_refl) (SHW 2147470781 1 eq_refl) (SHW 2147470782 1 eq_refl) (SHW 2147470783 1 eq_refl)
           (SHW 2147470784 1 eq_refl) (SHW 2147470785 1 eq_refl) (SHW 2147470786 1 eq_refl) (SHW 2147470787 1 eq_refl) (SHW 2147470824 1 eq_refl) (SHW 2147470825 1 eq_refl)
           (SHW 2147470826 1 eq_refl) (SHW 2147470827 1 eq_refl) (SHW 2147470828 1 eq_refl) (SHW 2147470829 1 eq_refl) (SHW 2147470830 1 eq_refl) (SHW 2147470831 1 eq_refl)
           (SHW 2147470832 1 eq_refl) (SHW 2147470833 1 eq_refl) (SHW 2147470834 1 eq_refl) (SHW 2147470835 1 eq_refl) (SHW 2147470836 1 eq_refl) (SHW 2147470837 1 eq_refl)
           (SHW 2147470838 1 eq_refl) (SHW 2147470839 1 eq_refl) (SHW 2147470852 1 eq_refl) (SHW 2147470852 4 eq_refl) (SHW 2147470853 1 eq_refl) (SHW 2147470854 1 eq_refl)
           (SHW 2147470855 1 eq_refl) (SHW 2147470856 4 eq_refl) (SHW 2147470860 1 eq_refl) (SHW 2147470860 4 eq_refl) (SHW 2147470861 1 eq_refl) (SHW 2147470862 1 eq_refl)
           (SHW 2147470863 1 eq_refl) (SHW 2147470864 1 eq_refl) (SHW 2147470864 4 eq_refl) (SHW 2147470865 1 eq_refl) (SHW 2147470866 1 eq_refl) (SHW 2147470867 1 eq_refl)
           (SHW 2147470868 4 eq_refl) (SHW 2147470872 4 eq_refl) (SHW 2147470876 4 eq_refl) (SHW 2147470880 4 eq_refl) (SHW 2147470884 4 eq_refl) (SHW 2147470888 4 eq_refl)
           (SHW 2147470888 8 eq_refl) (SHW 2147470896 8 eq_refl) (SHW 2147470904 4 eq_refl) (SHW 2147470904 8 eq_refl) (SHW 2147470908 4 eq_refl) (SHW 2147470912 4 eq_refl)
           (SHW 2147470912 8 eq_refl) (SHW 2147470916 4 eq_refl) (SHW 2147470920 4 eq_refl) (SHW 2147470924 4 eq_refl) (SHW 2147470928 1 eq_refl) (SHW 2147470928 4 eq_refl)
           (SHW 2147470929 1 eq_refl) (SHW 2147470930 1 eq_refl) (SHW 2147470931 1 eq_refl) (SHW 2147623588 1 eq_refl) (SHW 2147623588 4 eq_refl) (SHW 2147623589 1 eq_refl)
           (SHW 2147623590 1 eq_refl) (SHW 2147623591 1 eq_refl) (SHW 2147623592 4 eq_refl) (SHW 2147623596 4 eq_refl) (SHW 2147623600 1 eq_refl) (SHW 2147623600 4 eq_refl)
           (SHW 2147623601 1 eq_refl) (SHW 2147623602 1 eq_refl) (SHW 2147623603 1 eq_refl) (SHW 2147628820 1 eq_refl) (SHW 2147628820 4 eq_refl) (SHW 2147628821 1 eq_refl)
           (SHW 2147628822 1 eq_refl) (SHW 2147628823 1 eq_refl) (SHW 2147628824 4 eq_refl) (SHW 2147628828 4 eq_refl) (SHW 2147628832 4 eq_refl) (SHW 2147628836 4 eq_refl)
           (SHW 2147628840 4 eq_refl) (SHW 2147628844 4 eq_refl) (SHW 2147628848 8 eq_refl) (SHW 2147628856 8 eq_refl) (SHW 2147628864 8 eq_refl) (SHW 2147628872 8 eq_refl)
           (SHW 2147628880 8 eq_refl) (SHW 2147628888 8 eq_refl) (SHW 2147628896 8 eq_refl) (SHW 2147628904 8 eq_refl) (SHW 2147628912 8 eq_refl) (SHW 2147628920 8 eq_refl)
           (SHW 2147628928 8 eq_refl) (SHW 2147628936 8 eq_refl) (SHW 2147628944 8 eq_refl) (SHW 2147628952 8 eq_refl) (SHW 2147628960 8 eq_refl) (SHW 2147628968 8 eq_refl)
           (SHW 2147628976 8 eq_refl) (SHW 2147628984 8 eq_refl) (SHW 2147628992 8 eq_refl) (SHW 2147629000 8 eq_refl) (SHW 2147629008 8 eq_refl) (SHW 2147629016 8 eq_refl)
           (SHW 2147629024 8 eq_refl) (SHW 2147629032 8 eq_refl) (SHW 2147629040 8 eq_refl) (SHW 2147629048 8 eq_refl) (SHW 2147629056 8 eq_refl) (SHW 2147629064 8 eq_refl)
           (SHW 2147629072 8 eq_refl) (SHW 2147629080 8 eq_refl) (SHW 2147629088 8 eq_refl) (SHW 2147629096 8 eq_refl) (SHW 2147629104 8 eq_refl) (SHW 2147629112 8 eq_refl)
           (SHW 2147629120 8 eq_refl) (SHW 2147629128 8 eq_refl) (SHW 2147629136 8 eq_refl) (SHW 2147629144 8 eq_refl) (SHW 2147629144 4 eq_refl) (SHW 2147629148 4 eq_refl)
           (SHW 2147629152 8 eq_refl) (SHW 2147629152 4 eq_refl) (SHW 2147629156 4 eq_refl) (SHW 2147629160 8 eq_refl) (SHW 2147629160 4 eq_refl) (SHW 2147629164 4 eq_refl)
           (SHW 2147629168 1 eq_refl) (SHW 2147629168 4 eq_refl) (SHW 2147629169 1 eq_refl) (SHW 2147629170 1 eq_refl) (SHW 2147629171 1 eq_refl) TIDC
           HTr (XCC 0%nat 7028080 4 0 eq_refl) (XCC1 1%nat 7028115 0 eq_refl eq_refl) (XCC 2%nat 7027552 8 7027560 eq_refl) (XCC 3%nat 7027544 4 2 eq_refl) (XCC 22%nat 7027576 8 1277044 eq_refl)
           (XCC 23%nat 7027832 8 716372 eq_refl) (XCC 6%nat 7027540 4 0 eq_refl) (XCC1 24%nat 6889684 0 eq_refl eq_refl) (XCC 4%nat 7027568 8 1277044 eq_refl) (XCC 5%nat 7027824 8 648332 eq_refl) (STC1 10%nat 2038048 0 eq_refl eq_refl)
           (XCC 7%nat 7027560 8 0 eq_refl) (STC1 3%nat 1426448 0 eq_refl eq_refl) (STC 0%nat 1412008 8 1412008 eq_refl) (STC 2%nat 1426368 8 1 eq_refl) (STC 4%nat 1430160 4 1 eq_refl) (STC 5%nat 1430320 8 0 eq_refl)
           (STC1 8%nat 1443672 1 eq_refl eq_refl) (STC 7%nat 1440376 8 2147450880 eq_refl) (DSC 1423520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145984)) ltac:(img_rd) eq_refl) (DSC 1423536 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1438428 1 eq_refl eq_refl) (DSC 1423536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (STC 9%nat 2037280 8 18446744073709551615 eq_refl) (STC 1%nat 1412520 8 1347948 eq_refl) (DSC 1423576 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146016)) ltac:(img_rd) eq_refl) (DSC 1423600 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1423640 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146144)) ltac:(img_rd) eq_refl) (DSC 1423664 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146176)) ltac:(img_rd) eq_refl)
           (DSC 1423728 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1423768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146272)) ltac:(img_rd) eq_refl) (DSC 1423792 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1423832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146304)) ltac:(img_rd) eq_refl) (DSC 1423856 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1423856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1423896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146464)) ltac:(img_rd) eq_refl)
           (DSC 1423920 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl) (DSC 1423984 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146528)) ltac:(img_rd) eq_refl) (DSC 1424048 1%nat [Z_to_bv 8 192] ltac:(img_rd) eq_refl) (DSC 1424048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 6848)) ltac:(img_rd) eq_refl) (DSC 1424088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 153376)) ltac:(img_rd) eq_refl)
           (DSC 1424112 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 3424)) ltac:(img_rd) eq_refl) (DSC 1424152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156800)) ltac:(img_rd) eq_refl) (DSC 1424176 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156832)) ltac:(img_rd) eq_refl) (DSC 1424240 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1424240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1424280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156960)) ltac:(img_rd) eq_refl)
           (DSC 1424304 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156992)) ltac:(img_rd) eq_refl) (DSC 1424368 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157024)) ltac:(img_rd) eq_refl) (DSC 1424432 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157056)) ltac:(img_rd) eq_refl)
           (DSC 1424496 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157088)) ltac:(img_rd) eq_refl) (DSC 1424560 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157280)) ltac:(img_rd) eq_refl) (DSC 1424624 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157664)) ltac:(img_rd) eq_refl)
           (DSC 1424688 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1424728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157728)) ltac:(img_rd) eq_refl) (DSC 1424752 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1424792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157792)) ltac:(img_rd) eq_refl) (DSC 1424816 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157824)) ltac:(img_rd) eq_refl)
           (DSC 1424880 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1424920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157920)) ltac:(img_rd) eq_refl) (DSC 1424944 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1424984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158016)) ltac:(img_rd) eq_refl) (DSC 1425008 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158112)) ltac:(img_rd) eq_refl)
           (DSC 1425072 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158208)) ltac:(img_rd) eq_refl) (DSC 1425136 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158304)) ltac:(img_rd) eq_refl) (DSC 1425200 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158400)) ltac:(img_rd) eq_refl)
           (DSC 1425264 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1425264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1425304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158528)) ltac:(img_rd) eq_refl) (DSC 1425328 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1425368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158592)) ltac:(img_rd) eq_refl) (DSC 1425392 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1425432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158656)) ltac:(img_rd) eq_refl)
           (DSC 1425456 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158752)) ltac:(img_rd) eq_refl) (DSC 1425520 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158848)) ltac:(img_rd) eq_refl) (DSC 1425584 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158944)) ltac:(img_rd) eq_refl)
           (DSC 1425648 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159040)) ltac:(img_rd) eq_refl) (DSC 1425712 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159136)) ltac:(img_rd) eq_refl) (DSC 1425776 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159232)) ltac:(img_rd) eq_refl)
           (DSC 1425840 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1425880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159552)) ltac:(img_rd) eq_refl) (DSC 1425904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1425944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159584)) ltac:(img_rd) eq_refl) (DSC 1425968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159616)) ltac:(img_rd) eq_refl)
           (DSC 1426032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159648)) ltac:(img_rd) eq_refl) (DSC 1426096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1426136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159776)) ltac:(img_rd) eq_refl) (DSC 1426160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1426160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1426200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159872)) ltac:(img_rd) eq_refl)
           (DSC 1426224 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 544)) ltac:(img_rd) eq_refl) (DSC 1426264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1381664)) ltac:(img_rd) eq_refl) (DSC 1426288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1426288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
           (DSC 1426328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 7029512 8 0 eq_refl) (XCC 9%nat 1423464 8 1423232 eq_refl) (XCC 10%nat 1423372 4 4294967295 eq_refl) (XCC 11%nat 1423272 8 0 eq_refl) (XCC 12%nat 1423288 8 0 eq_refl)
           (XCC 13%nat 1423240 8 0 eq_refl) (XCC 14%nat 1423248 8 0 eq_refl) (XCC 15%nat 1423224 8 1422992 eq_refl) SOlock SOwpos SOwbase
           SOwrite CANc SOfd) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
    set (good := fun i : Z => i < 1426336 \/ 1430328 <= i < 7027536 \/ 7027560 <= i < 7028080 \/ 7028084 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x137cc8) M R1 (Z_to_bv 64 0x13f6ac) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1426336) || ((1430328 <=? a) && (a + Z.of_nat n <=? 7027536)) || ((7028084 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7029536) (Z.to_nat (2 * 2)) = Some (zero_lines 2%nat)).
    { apply (LITX 7029536 (Z.to_nat (2 * 2))); [|reflexivity]. change (Z.to_nat (2 * 2)) with (2 * 2%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. reflexivity. }
    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1422992 /\ (1422992 + 124 <= q \/ q + 32 + 16 <= 1422992 + 120) /\ 1422992 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 2%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1422992 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 2%nat)%nat true R1 M1 model1 q 2 7029536 (2 * 2) 0 0 (zero_lines 2%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 1426336) || ((1430328 <=? a) && (a + Z.of_nat n <=? 7027536)) || ((7028084 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 1422992 <= a -> a + n <= 1422992 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1409024 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1422992) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7027520) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
           DDF IMG3 (fun d k Hd Hk => FW3 1423024 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1423032 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1423048 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1423080 8%nat _ SObuf eq_refl)
           (LIT3 1423088 8%nat _ SObufsz eq_refl) (LIT3 7027520 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
           (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1423000 8%nat _ SOrpos eq_refl)
           (LIT3 1423008 8%nat _ SOrend eq_refl) (LIT3 1422984 8%nat _ (XCC 16%nat 1422984 8 1422752 eq_refl) eq_refl) (LIT3 1422892 4%nat _ (XCC 17%nat 1422892 4 4294967295 eq_refl) eq_refl) (LIT3 1422792 8%nat _ (XCC 18%nat 1422792 8 0 eq_refl) eq_refl) (LIT3 1422808 8%nat _ (XCC 19%nat 1422808 8 0 eq_refl) eq_refl) (LIT3 1422760 8%nat _ (XCC 20%nat 1422760 8 0 eq_refl) eq_refl)
           (LIT3 1422768 8%nat _ (XCC 21%nat 1422768 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x13f6b8) M3 R4 (Z_to_bv 64 0x1379d8) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x1379d8) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.


  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_4 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1275140 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6896384 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7027520) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x137cc8) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
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
    assert (SHW : forall a n, ((2147469128 <=? a) && (a + n <=? 2147470932) || (2147623588 <=? a) && (a + n <=? 2147623604) || (2147628820 <=? a) && (a + n <=? 2147629172)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x15b8a0 <=? a) && (a + Z.of_nat n <=? 0x15c3a0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpX4_pre.dpX4_pre_conc fx R MV V
           HS64 Hcan HT64 G1 G2 G4
           HSr HSa CWR CDF IMGc (WSG 1426368 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 1426448 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1430320 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027536 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027544 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7027552 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 7028080 4%nat ltac:(vm_compute; reflexivity) eq_refl)
           (SHW 2147469128 1 eq_refl) (SHW 2147469129 1 eq_refl) (SHW 2147469130 1 eq_refl) (SHW 2147469131 1 eq_refl) (SHW 2147469132 1 eq_refl) (SHW 2147469132 4 eq_refl)
           (SHW 2147469133 1 eq_refl) (SHW 2147469134 1 eq_refl) (SHW 2147469135 1 eq_refl) (SHW 2147469136 4 eq_refl) (SHW 2147469140 1 eq_refl) (SHW 2147469140 4 eq_refl)
           (SHW 2147469141 1 eq_refl) (SHW 2147469142 1 eq_refl) (SHW 2147469143 1 eq_refl) (SHW 2147469148 1 eq_refl) (SHW 2147469149 1 eq_refl) (SHW 2147469150 1 eq_refl)
           (SHW 2147469151 1 eq_refl) (SHW 2147469152 1 eq_refl) (SHW 2147469152 4 eq_refl) (SHW 2147469153 1 eq_refl) (SHW 2147469154 1 eq_refl) (SHW 2147469155 1 eq_refl)
           (SHW 2147469156 4 eq_refl) (SHW 2147469160 1 eq_refl) (SHW 2147469160 4 eq_refl) (SHW 2147469161 1 eq_refl) (SHW 2147469162 1 eq_refl) (SHW 2147469163 1 eq_refl)
           (SHW 2147469164 1 eq_refl) (SHW 2147469165 1 eq_refl) (SHW 2147469166 1 eq_refl) (SHW 2147469167 1 eq_refl) (SHW 2147469168 1 eq_refl) (SHW 2147469169 1 eq_refl)
           (SHW 2147469170 1 eq_refl) (SHW 2147469171 1 eq_refl) (SHW 2147469172 1 eq_refl) (SHW 2147469173 1 eq_refl) (SHW 2147469174 1 eq_refl) (SHW 2147469175 1 eq_refl)
           (SHW 2147469188 1 eq_refl) (SHW 2147469189 1 eq_refl) (SHW 2147469190 1 eq_refl) (SHW 2147469191 1 eq_refl) (SHW 2147469192 1 eq_refl) (SHW 2147469193 1 eq_refl)
           (SHW 2147469194 1 eq_refl) (SHW 2147469195 1 eq_refl) (SHW 2147469196 1 eq_refl) (SHW 2147469196 4 eq_refl) (SHW 2147469197 1 eq_refl) (SHW 2147469198 1 eq_refl)
           (SHW 2147469199 1 eq_refl) (SHW 2147469200 4 eq_refl) (SHW 2147469204 4 eq_refl) (SHW 2147469208 4 eq_refl) (SHW 2147469212 4 eq_refl) (SHW 2147469216 4 eq_refl)
           (SHW 2147469220 4 eq_refl) (SHW 2147469224 8 eq_refl) (SHW 2147469232 8 eq_refl) (SHW 2147469240 8 eq_refl) (SHW 2147469248 8 eq_refl) (SHW 2147469256 8 eq_refl)
           (SHW 2147469264 8 eq_refl) (SHW 2147469272 8 eq_refl) (SHW 2147469280 8 eq_refl) (SHW 2147469288 8 eq_refl) (SHW 2147469296 8 eq_refl) (SHW 2147469304 8 eq_refl)
           (SHW 2147469312 8 eq_refl) (SHW 2147469320 8 eq_refl) (SHW 2147469328 8 eq_refl) (SHW 2147469336 8 eq_refl) (SHW 2147469344 8 eq_refl) (SHW 2147469352 8 eq_refl)
           (SHW 2147469360 8 eq_refl) (SHW 2147469368 8 eq_refl) (SHW 2147469376 8 eq_refl) (SHW 2147469384 8 eq_refl) (SHW 2147469392 8 eq_refl) (SHW 2147469400 8 eq_refl)
           (SHW 2147469408 8 eq_refl) (SHW 2147469416 8 eq_refl) (SHW 2147469424 8 eq_refl) (SHW 2147469432 8 eq_refl) (SHW 2147469440 8 eq_refl) (SHW 2147469448 8 eq_refl)
           (SHW 2147469456 8 eq_refl) (SHW 2147469464 8 eq_refl) (SHW 2147469472 8 eq_refl) (SHW 2147469480 8 eq_refl) (SHW 2147469488 8 eq_refl) (SHW 2147469496 8 eq_refl)
           (SHW 2147469504 8 eq_refl) (SHW 2147469512 8 eq_refl) (SHW 2147469520 8 eq_refl) (SHW 2147469528 8 eq_refl) (SHW 2147469536 8 eq_refl) (SHW 2147469544 8 eq_refl)
           (SHW 2147469552 8 eq_refl) (SHW 2147469560 8 eq_refl) (SHW 2147469568 8 eq_refl) (SHW 2147469576 8 eq_refl) (SHW 2147469584 8 eq_refl) (SHW 2147469592 8 eq_refl)
           (SHW 2147469600 8 eq_refl) (SHW 2147469608 8 eq_refl) (SHW 2147469616 8 eq_refl) (SHW 2147469624 8 eq_refl) (SHW 2147469632 8 eq_refl) (SHW 2147469640 8 eq_refl)
           (SHW 2147469648 8 eq_refl) (SHW 2147469656 8 eq_refl) (SHW 2147469664 8 eq_refl) (SHW 2147469672 8 eq_refl) (SHW 2147469680 8 eq_refl) (SHW 2147469688 8 eq_refl)
           (SHW 2147469696 8 eq_refl) (SHW 2147469704 8 eq_refl) (SHW 2147469712 8 eq_refl) (SHW 2147469720 8 eq_refl) (SHW 2147469728 8 eq_refl) (SHW 2147469736 8 eq_refl)
           (SHW 2147469744 8 eq_refl) (SHW 2147469752 8 eq_refl) (SHW 2147469760 8 eq_refl) (SHW 2147469768 8 eq_refl) (SHW 2147469776 8 eq_refl) (SHW 2147469784 8 eq_refl)
           (SHW 2147469792 8 eq_refl) (SHW 2147469800 8 eq_refl) (SHW 2147469808 8 eq_refl) (SHW 2147469816 8 eq_refl) (SHW 2147469824 8 eq_refl) (SHW 2147469832 8 eq_refl)
           (SHW 2147469840 8 eq_refl) (SHW 2147469848 8 eq_refl) (SHW 2147469856 8 eq_refl) (SHW 2147469864 8 eq_refl) (SHW 2147469872 8 eq_refl) (SHW 2147469880 8 eq_refl)
           (SHW 2147469888 8 eq_refl) (SHW 2147469896 8 eq_refl) (SHW 2147469904 8 eq_refl) (SHW 2147469912 8 eq_refl) (SHW 2147469920 8 eq_refl) (SHW 2147469928 8 eq_refl)
           (SHW 2147469936 8 eq_refl) (SHW 2147469944 8 eq_refl) (SHW 2147469952 8 eq_refl) (SHW 2147469960 8 eq_refl) (SHW 2147469968 8 eq_refl) (SHW 2147469976 8 eq_refl)
           (SHW 2147469984 8 eq_refl) (SHW 2147469992 8 eq_refl) (SHW 2147470000 8 eq_refl) (SHW 2147470008 8 eq_refl) (SHW 2147470016 8 eq_refl) (SHW 2147470024 4 eq_refl)
           (SHW 2147470028 4 eq_refl) (SHW 2147470032 4 eq_refl) (SHW 2147470036 4 eq_refl) (SHW 2147470040 4 eq_refl) (SHW 2147470044 4 eq_refl) (SHW 2147470048 1 eq_refl)
           (SHW 2147470048 4 eq_refl) (SHW 2147470049 1 eq_refl) (SHW 2147470050 1 eq_refl) (SHW 2147470051 1 eq_refl) (SHW 2147470052 1 eq_refl) (SHW 2147470052 4 eq_refl)
           (SHW 2147470053 1 eq_refl) (SHW 2147470054 1 eq_refl) (SHW 2147470055 1 eq_refl) (SHW 2147470056 4 eq_refl) (SHW 2147470060 4 eq_refl) (SHW 2147470064 4 eq_refl)
           (SHW 2147470068 4 eq_refl) (SHW 2147470072 4 eq_refl) (SHW 2147470076 4 eq_refl) (SHW 2147470080 8 eq_refl) (SHW 2147470088 8 eq_refl) (SHW 2147470096 8 eq_refl)
           (SHW 2147470104 8 eq_refl) (SHW 2147470112 8 eq_refl) (SHW 2147470120 8 eq_refl) (SHW 2147470128 8 eq_refl) (SHW 2147470136 8 eq_refl) (SHW 2147470144 8 eq_refl)
           (SHW 2147470152 8 eq_refl) (SHW 2147470160 8 eq_refl) (SHW 2147470168 8 eq_refl) (SHW 2147470176 8 eq_refl) (SHW 2147470184 8 eq_refl) (SHW 2147470192 8 eq_refl)
           (SHW 2147470200 8 eq_refl) (SHW 2147470208 8 eq_refl) (SHW 2147470216 8 eq_refl) (SHW 2147470224 8 eq_refl) (SHW 2147470232 8 eq_refl) (SHW 2147470240 8 eq_refl)
           (SHW 2147470248 8 eq_refl) (SHW 2147470256 8 eq_refl) (SHW 2147470264 8 eq_refl) (SHW 2147470272 8 eq_refl) (SHW 2147470280 8 eq_refl) (SHW 2147470288 8 eq_refl)
           (SHW 2147470296 8 eq_refl) (SHW 2147470304 8 eq_refl) (SHW 2147470312 8 eq_refl) (SHW 2147470320 8 eq_refl) (SHW 2147470328 8 eq_refl) (SHW 2147470336 8 eq_refl)
           (SHW 2147470344 8 eq_refl) (SHW 2147470352 8 eq_refl) (SHW 2147470360 8 eq_refl) (SHW 2147470368 8 eq_refl) (SHW 2147470376 8 eq_refl) (SHW 2147470384 8 eq_refl)
           (SHW 2147470392 8 eq_refl) (SHW 2147470400 8 eq_refl) (SHW 2147470408 8 eq_refl) (SHW 2147470416 8 eq_refl) (SHW 2147470424 8 eq_refl) (SHW 2147470432 8 eq_refl)
           (SHW 2147470440 8 eq_refl) (SHW 2147470448 8 eq_refl) (SHW 2147470452 4 eq_refl) (SHW 2147470456 4 eq_refl) (SHW 2147470456 8 eq_refl) (SHW 2147470460 4 eq_refl)
           (SHW 2147470464 4 eq_refl) (SHW 2147470468 4 eq_refl) (SHW 2147470472 4 eq_refl) (SHW 2147470476 1 eq_refl) (SHW 2147470476 4 eq_refl) (SHW 2147470477 1 eq_refl)
           (SHW 2147470478 1 eq_refl) (SHW 2147470479 1 eq_refl) (SHW 2147470480 1 eq_refl) (SHW 2147470481 1 eq_refl) (SHW 2147470482 1 eq_refl) (SHW 2147470483 1 eq_refl)
           (SHW 2147470484 1 eq_refl) (SHW 2147470484 4 eq_refl) (SHW 2147470485 1 eq_refl) (SHW 2147470486 1 eq_refl) (SHW 2147470487 1 eq_refl) (SHW 2147470488 4 eq_refl)
           (SHW 2147470492 4 eq_refl) (SHW 2147470496 1 eq_refl) (SHW 2147470496 4 eq_refl) (SHW 2147470497 1 eq_refl) (SHW 2147470498 1 eq_refl) (SHW 2147470499 1 eq_refl)
           (SHW 2147470500 1 eq_refl) (SHW 2147470501 1 eq_refl) (SHW 2147470502 1 eq_refl) (SHW 2147470503 1 eq_refl) (SHW 2147470504 1 eq_refl) (SHW 2147470505 1 eq_refl)
           (SHW 2147470506 1 eq_refl) (SHW 2147470507 1 eq_refl) (SHW 2147470508 1 eq_refl) (SHW 2147470509 1 eq_refl) (SHW 2147470510 1 eq_refl) (SHW 2147470511 1 eq_refl)
           (SHW 2147470512 1 eq_refl) (SHW 2147470513 1 eq_refl) (SHW 2147470514 1 eq_refl) (SHW 2147470515 1 eq_refl) (SHW 2147470516 1 eq_refl) (SHW 2147470517 1 eq_refl)
           (SHW 2147470518 1 eq_refl) (SHW 2147470519 1 eq_refl) (SHW 2147470540 1 eq_refl) (SHW 2147470541 1 eq_refl) (SHW 2147470542 1 eq_refl) (SHW 2147470543 1 eq_refl)
           (SHW 2147470588 1 eq_refl) (SHW 2147470589 1 eq_refl) (SHW 2147470590 1 eq_refl) (SHW 2147470591 1 eq_refl) (SHW 2147470592 1 eq_refl) (SHW 2147470593 1 eq_refl)
           (SHW 2147470594 1 eq_refl) (SHW 2147470595 1 eq_refl) (SHW 2147470596 1 eq_refl) (SHW 2147470597 1 eq_refl) (SHW 2147470598 1 eq_refl) (SHW 2147470599 1 eq_refl)
           (SHW 2147470600 1 eq_refl) (SHW 2147470601 1 eq_refl) (SHW 2147470602 1 eq_refl) (SHW 2147470603 1 eq_refl) (SHW 2147470604 1 eq_refl) (SHW 2147470605 1 eq_refl)
           (SHW 2147470606 1 eq_refl) (SHW 2147470607 1 eq_refl) (SHW 2147470608 1 eq_refl) (SHW 2147470608 4 eq_refl) (SHW 2147470609 1 eq_refl) (SHW 2147470610 1 eq_refl)
           (SHW 2147470611 1 eq_refl) (SHW 2147470612 4 eq_refl) (SHW 2147470616 1 eq_refl) (SHW 2147470616 4 eq_refl) (SHW 2147470617 1 eq_refl) (SHW 2147470618 1 eq_refl)
           (SHW 2147470619 1 eq_refl) (SHW 2147470620 1 eq_refl) (SHW 2147470620 4 eq_refl) (SHW 2147470621 1 eq_refl) (SHW 2147470622 1 eq_refl) (SHW 2147470623 1 eq_refl)
           (SHW 2147470624 4 eq_refl) (SHW 2147470628 1 eq_refl) (SHW 2147470628 4 eq_refl) (SHW 2147470629 1 eq_refl) (SHW 2147470630 1 eq_refl) (SHW 2147470631 1 eq_refl)
           (SHW 2147470632 1 eq_refl) (SHW 2147470632 4 eq_refl) (SHW 2147470633 1 eq_refl) (SHW 2147470634 1 eq_refl) (SHW 2147470635 1 eq_refl) (SHW 2147470636 4 eq_refl)
           (SHW 2147470640 1 eq_refl) (SHW 2147470640 4 eq_refl) (SHW 2147470641 1 eq_refl) (SHW 2147470642 1 eq_refl) (SHW 2147470643 1 eq_refl) (SHW 2147470644 1 eq_refl)
           (SHW 2147470644 4 eq_refl) (SHW 2147470645 1 eq_refl) (SHW 2147470646 1 eq_refl) (SHW 2147470647 1 eq_refl) (SHW 2147470648 4 eq_refl) (SHW 2147470652 1 eq_refl)
           (SHW 2147470652 4 eq_refl) (SHW 2147470653 1 eq_refl) (SHW 2147470654 1 eq_refl) (SHW 2147470655 1 eq_refl) (SHW 2147470656 1 eq_refl) (SHW 2147470656 4 eq_refl)
           (SHW 2147470657 1 eq_refl) (SHW 2147470658 1 eq_refl) (SHW 2147470659 1 eq_refl) (SHW 2147470660 4 eq_refl) (SHW 2147470664 1 eq_refl) (SHW 2147470664 4 eq_refl)
           (SHW 2147470665 1 eq_refl) (SHW 2147470666 1 eq_refl) (SHW 2147470667 1 eq_refl) (SHW 2147470668 1 eq_refl) (SHW 2147470668 4 eq_refl) (SHW 2147470669 1 eq_refl)
           (SHW 2147470670 1 eq_refl) (SHW 2147470671 1 eq_refl) (SHW 2147470672 4 eq_refl) (SHW 2147470676 1 eq_refl) (SHW 2147470676 4 eq_refl) (SHW 2147470677 1 eq_refl)
           (SHW 2147470678 1 eq_refl) (SHW 2147470679 1 eq_refl) (SHW 2147470680 1 eq_refl) (SHW 2147470680 4 eq_refl) (SHW 2147470681 1 eq_refl) (SHW 2147470682 1 eq_refl)
           (SHW 2147470683 1 eq_refl) (SHW 2147470684 4 eq_refl) (SHW 2147470688 4 eq_refl) (SHW 2147470692 1 eq_refl) (SHW 2147470692 4 eq_refl) (SHW 2147470693 1 eq_refl)
           (SHW 2147470694 1 eq_refl) (SHW 2147470695 1 eq_refl) (SHW 2147470696 1 eq_refl) (SHW 2147470697 1 eq_refl) (SHW 2147470698 1 eq_refl) (SHW 2147470699 1 eq_refl)
           (SHW 2147470700 1 eq_refl) (SHW 2147470701 1 eq_refl) (SHW 2147470702 1 eq_refl) (SHW 2147470703 1 eq_refl) (SHW 2147470704 1 eq_refl) (SHW 2147470705 1 eq_refl)
           (SHW 2147470706 1 eq_refl) (SHW 2147470707 1 eq_refl) (SHW 2147470708 1 eq_refl) (SHW 2147470709 1 eq_refl) (SHW 2147470710 1 eq_refl) (SHW 2147470711 1 eq_refl)
           (SHW 2147470712 1 eq_refl) (SHW 2147470712 4 eq_refl) (SHW 2147470713 1 eq_refl) (SHW 2147470714 1 eq_refl) (SHW 2147470715 1 eq_refl) (SHW 2147470716 4 eq_refl)
           (SHW 2147470720 1 eq_refl) (SHW 2147470720 4 eq_refl) (SHW 2147470721 1 eq_refl) (SHW 2147470722 1 eq_refl) (SHW 2147470723 1 eq_refl) (SHW 2147470724 1 eq_refl)
           (SHW 2147470724 4 eq_refl) (SHW 2147470725 1 eq_refl) (SHW 2147470726 1 eq_refl) (SHW 2147470727 1 eq_refl) (SHW 2147470728 4 eq_refl) (SHW 2147470732 1 eq_refl)
           (SHW 2147470732 4 eq_refl) (SHW 2147470733 1 eq_refl) (SHW 2147470734 1 eq_refl) (SHW 2147470735 1 eq_refl) (SHW 2147470736 1 eq_refl) (SHW 2147470736 4 eq_refl)
           (SHW 2147470737 1 eq_refl) (SHW 2147470738 1 eq_refl) (SHW 2147470739 1 eq_refl) (SHW 2147470740 4 eq_refl) (SHW 2147470744 1 eq_refl) (SHW 2147470744 4 eq_refl)
           (SHW 2147470745 1 eq_refl) (SHW 2147470746 1 eq_refl) (SHW 2147470747 1 eq_refl) (SHW 2147470748 1 eq_refl) (SHW 2147470748 4 eq_refl) (SHW 2147470749 1 eq_refl)
           (SHW 2147470750 1 eq_refl) (SHW 2147470751 1 eq_refl) (SHW 2147470752 4 eq_refl) (SHW 2147470756 1 eq_refl) (SHW 2147470756 4 eq_refl) (SHW 2147470757 1 eq_refl)
           (SHW 2147470758 1 eq_refl) (SHW 2147470759 1 eq_refl) (SHW 2147470760 1 eq_refl) (SHW 2147470760 4 eq_refl) (SHW 2147470761 1 eq_refl) (SHW 2147470762 1 eq_refl)
           (SHW 2147470763 1 eq_refl) (SHW 2147470764 4 eq_refl) (SHW 2147470768 1 eq_refl) (SHW 2147470768 4 eq_refl) (SHW 2147470769 1 eq_refl) (SHW 2147470770 1 eq_refl)
           (SHW 2147470771 1 eq_refl) (SHW 2147470772 1 eq_refl) (SHW 2147470772 4 eq_refl) (SHW 2147470773 1 eq_refl) (SHW 2147470774 1 eq_refl) (SHW 2147470775 1 eq_refl)
           (SHW 2147470776 4 eq_refl) (SHW 2147470780 1 eq_refl) (SHW 2147470780 4 eq_refl) (SHW 2147470781 1 eq_refl) (SHW 2147470782 1 eq_refl) (SHW 2147470783 1 eq_refl)
           (SHW 2147470784 1 eq_refl) (SHW 2147470785 1 eq_refl) (SHW 2147470786 1 eq_refl) (SHW 2147470787 1 eq_refl) (SHW 2147470824 1 eq_refl) (SHW 2147470825 1 eq_refl)
           (SHW 2147470826 1 eq_refl) (SHW 2147470827 1 eq_refl) (SHW 2147470828 1 eq_refl) (SHW 2147470829 1 eq_refl) (SHW 2147470830 1 eq_refl) (SHW 2147470831 1 eq_refl)
           (SHW 2147470832 1 eq_refl) (SHW 2147470833 1 eq_refl) (SHW 2147470834 1 eq_refl) (SHW 2147470835 1 eq_refl) (SHW 2147470836 1 eq_refl) (SHW 2147470837 1 eq_refl)
           (SHW 2147470838 1 eq_refl) (SHW 2147470839 1 eq_refl) (SHW 2147470852 1 eq_refl) (SHW 2147470852 4 eq_refl) (SHW 2147470853 1 eq_refl) (SHW 2147470854 1 eq_refl)
           (SHW 2147470855 1 eq_refl) (SHW 2147470856 4 eq_refl) (SHW 2147470860 1 eq_refl) (SHW 2147470860 4 eq_refl) (SHW 2147470861 1 eq_refl) (SHW 2147470862 1 eq_refl)
           (SHW 2147470863 1 eq_refl) (SHW 2147470864 1 eq_refl) (SHW 2147470864 4 eq_refl) (SHW 2147470865 1 eq_refl) (SHW 2147470866 1 eq_refl) (SHW 2147470867 1 eq_refl)
           (SHW 2147470868 4 eq_refl) (SHW 2147470872 4 eq_refl) (SHW 2147470876 4 eq_refl) (SHW 2147470880 4 eq_refl) (SHW 2147470884 4 eq_refl) (SHW 2147470888 4 eq_refl)
           (SHW 2147470888 8 eq_refl) (SHW 2147470896 8 eq_refl) (SHW 2147470904 4 eq_refl) (SHW 2147470904 8 eq_refl) (SHW 2147470908 4 eq_refl) (SHW 2147470912 4 eq_refl)
           (SHW 2147470912 8 eq_refl) (SHW 2147470916 4 eq_refl) (SHW 2147470920 4 eq_refl) (SHW 2147470924 4 eq_refl) (SHW 2147470928 1 eq_refl) (SHW 2147470928 4 eq_refl)
           (SHW 2147470929 1 eq_refl) (SHW 2147470930 1 eq_refl) (SHW 2147470931 1 eq_refl) (SHW 2147623588 1 eq_refl) (SHW 2147623588 4 eq_refl) (SHW 2147623589 1 eq_refl)
           (SHW 2147623590 1 eq_refl) (SHW 2147623591 1 eq_refl) (SHW 2147623592 4 eq_refl) (SHW 2147623596 4 eq_refl) (SHW 2147623600 1 eq_refl) (SHW 2147623600 4 eq_refl)
           (SHW 2147623601 1 eq_refl) (SHW 2147623602 1 eq_refl) (SHW 2147623603 1 eq_refl) (SHW 2147628820 1 eq_refl) (SHW 2147628820 4 eq_refl) (SHW 2147628821 1 eq_refl)
           (SHW 2147628822 1 eq_refl) (SHW 2147628823 1 eq_refl) (SHW 2147628824 4 eq_refl) (SHW 2147628828 4 eq_refl) (SHW 2147628832 4 eq_refl) (SHW 2147628836 4 eq_refl)
           (SHW 2147628840 4 eq_refl) (SHW 2147628844 4 eq_refl) (SHW 2147628848 8 eq_refl) (SHW 2147628856 8 eq_refl) (SHW 2147628864 8 eq_refl) (SHW 2147628872 8 eq_refl)
           (SHW 2147628880 8 eq_refl) (SHW 2147628888 8 eq_refl) (SHW 2147628896 8 eq_refl) (SHW 2147628904 8 eq_refl) (SHW 2147628912 8 eq_refl) (SHW 2147628920 8 eq_refl)
           (SHW 2147628928 8 eq_refl) (SHW 2147628936 8 eq_refl) (SHW 2147628944 8 eq_refl) (SHW 2147628952 8 eq_refl) (SHW 2147628960 8 eq_refl) (SHW 2147628968 8 eq_refl)
           (SHW 2147628976 8 eq_refl) (SHW 2147628984 8 eq_refl) (SHW 2147628992 8 eq_refl) (SHW 2147629000 8 eq_refl) (SHW 2147629008 8 eq_refl) (SHW 2147629016 8 eq_refl)
           (SHW 2147629024 8 eq_refl) (SHW 2147629032 8 eq_refl) (SHW 2147629040 8 eq_refl) (SHW 2147629048 8 eq_refl) (SHW 2147629056 8 eq_refl) (SHW 2147629064 8 eq_refl)
           (SHW 2147629072 8 eq_refl) (SHW 2147629080 8 eq_refl) (SHW 2147629088 8 eq_refl) (SHW 2147629096 8 eq_refl) (SHW 2147629104 8 eq_refl) (SHW 2147629112 8 eq_refl)
           (SHW 2147629120 8 eq_refl) (SHW 2147629128 8 eq_refl) (SHW 2147629136 8 eq_refl) (SHW 2147629144 8 eq_refl) (SHW 2147629144 4 eq_refl) (SHW 2147629148 4 eq_refl)
           (SHW 2147629152 8 eq_refl) (SHW 2147629152 4 eq_refl) (SHW 2147629156 4 eq_refl) (SHW 2147629160 8 eq_refl) (SHW 2147629160 4 eq_refl) (SHW 2147629164 4 eq_refl)
           (SHW 2147629168 1 eq_refl) (SHW 2147629168 4 eq_refl) (SHW 2147629169 1 eq_refl) (SHW 2147629170 1 eq_refl) (SHW 2147629171 1 eq_refl) TIDC
           HTr (XCC 0%nat 7028080 4 0 eq_refl) (XCC1 1%nat 7028115 0 eq_refl eq_refl) (XCC 2%nat 7027552 8 7027560 eq_refl) (XCC 3%nat 7027544 4 2 eq_refl) (XCC 22%nat 7027576 8 1277044 eq_refl)
           (XCC 23%nat 7027832 8 716372 eq_refl) (XCC 6%nat 7027540 4 0 eq_refl) (XCC1 24%nat 6889684 0 eq_refl eq_refl) (XCC 4%nat 7027568 8 1277044 eq_refl) (XCC 5%nat 7027824 8 648332 eq_refl) (STC1 10%nat 2038048 0 eq_refl eq_refl)
           (XCC 7%nat 7027560 8 0 eq_refl) (STC1 3%nat 1426448 0 eq_refl eq_refl) (STC 0%nat 1412008 8 1412008 eq_refl) (STC 2%nat 1426368 8 1 eq_refl) (STC 4%nat 1430160 4 1 eq_refl) (STC 5%nat 1430320 8 0 eq_refl)
           (STC1 8%nat 1443672 1 eq_refl eq_refl) (STC 7%nat 1440376 8 2147450880 eq_refl) (DSC 1423520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145984)) ltac:(img_rd) eq_refl) (DSC 1423536 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1438428 1 eq_refl eq_refl) (DSC 1423536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (STC 9%nat 2037280 8 18446744073709551615 eq_refl) (STC 1%nat 1412520 8 1347948 eq_refl) (DSC 1423576 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146016)) ltac:(img_rd) eq_refl) (DSC 1423600 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1423640 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146144)) ltac:(img_rd) eq_refl) (DSC 1423664 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146176)) ltac:(img_rd) eq_refl)
           (DSC 1423728 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1423768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146272)) ltac:(img_rd) eq_refl) (DSC 1423792 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1423832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146304)) ltac:(img_rd) eq_refl) (DSC 1423856 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1423856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1423896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146464)) ltac:(img_rd) eq_refl)
           (DSC 1423920 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl) (DSC 1423984 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146528)) ltac:(img_rd) eq_refl) (DSC 1424048 1%nat [Z_to_bv 8 192] ltac:(img_rd) eq_refl) (DSC 1424048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 6848)) ltac:(img_rd) eq_refl) (DSC 1424088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 153376)) ltac:(img_rd) eq_refl)
           (DSC 1424112 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 3424)) ltac:(img_rd) eq_refl) (DSC 1424152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156800)) ltac:(img_rd) eq_refl) (DSC 1424176 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156832)) ltac:(img_rd) eq_refl) (DSC 1424240 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1424240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1424280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156960)) ltac:(img_rd) eq_refl)
           (DSC 1424304 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156992)) ltac:(img_rd) eq_refl) (DSC 1424368 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157024)) ltac:(img_rd) eq_refl) (DSC 1424432 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157056)) ltac:(img_rd) eq_refl)
           (DSC 1424496 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157088)) ltac:(img_rd) eq_refl) (DSC 1424560 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1424600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157280)) ltac:(img_rd) eq_refl) (DSC 1424624 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157664)) ltac:(img_rd) eq_refl)
           (DSC 1424688 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1424728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157728)) ltac:(img_rd) eq_refl) (DSC 1424752 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1424792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157792)) ltac:(img_rd) eq_refl) (DSC 1424816 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157824)) ltac:(img_rd) eq_refl)
           (DSC 1424880 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1424920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157920)) ltac:(img_rd) eq_refl) (DSC 1424944 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1424984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158016)) ltac:(img_rd) eq_refl) (DSC 1425008 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158112)) ltac:(img_rd) eq_refl)
           (DSC 1425072 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158208)) ltac:(img_rd) eq_refl) (DSC 1425136 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158304)) ltac:(img_rd) eq_refl) (DSC 1425200 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158400)) ltac:(img_rd) eq_refl)
           (DSC 1425264 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1425264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1425304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158528)) ltac:(img_rd) eq_refl) (DSC 1425328 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1425368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158592)) ltac:(img_rd) eq_refl) (DSC 1425392 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1425432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158656)) ltac:(img_rd) eq_refl)
           (DSC 1425456 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158752)) ltac:(img_rd) eq_refl) (DSC 1425520 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158848)) ltac:(img_rd) eq_refl) (DSC 1425584 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158944)) ltac:(img_rd) eq_refl)
           (DSC 1425648 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159040)) ltac:(img_rd) eq_refl) (DSC 1425712 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1425752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159136)) ltac:(img_rd) eq_refl) (DSC 1425776 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159232)) ltac:(img_rd) eq_refl)
           (DSC 1425840 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1425880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159552)) ltac:(img_rd) eq_refl) (DSC 1425904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1425944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159584)) ltac:(img_rd) eq_refl) (DSC 1425968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159616)) ltac:(img_rd) eq_refl)
           (DSC 1426032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159648)) ltac:(img_rd) eq_refl) (DSC 1426096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1426136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159776)) ltac:(img_rd) eq_refl) (DSC 1426160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1426160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1426200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159872)) ltac:(img_rd) eq_refl)
           (DSC 1426224 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 544)) ltac:(img_rd) eq_refl) (DSC 1426264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1381664)) ltac:(img_rd) eq_refl) (DSC 1426288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1426288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
           (DSC 1426328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 7029512 8 0 eq_refl) (XCC 9%nat 1423464 8 1423232 eq_refl) (XCC 10%nat 1423372 4 4294967295 eq_refl) (XCC 11%nat 1423272 8 0 eq_refl) (XCC 12%nat 1423288 8 0 eq_refl)
           (XCC 13%nat 1423240 8 0 eq_refl) (XCC 14%nat 1423248 8 0 eq_refl) (XCC 15%nat 1423224 8 1422992 eq_refl) SOlock SOwpos SOwbase
           SOwrite CANc SOfd) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
    set (good := fun i : Z => i < 1426336 \/ 1430328 <= i < 7027536 \/ 7027560 <= i < 7028080 \/ 7028084 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x137cc8) M R1 (Z_to_bv 64 0x13f6ac) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1426336) || ((1430328 <=? a) && (a + Z.of_nat n <=? 7027536)) || ((7028084 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7029536) (Z.to_nat (2 * 3)) = Some (zero_lines 3%nat)).
    { apply (LITX 7029536 (Z.to_nat (2 * 3))); [|reflexivity]. change (Z.to_nat (2 * 3)) with (2 * 3%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). destruct (BC 2 ltac:(lia)) as (B2a & B2b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. apply rdn_cons1; [lia | exact B2a|]. apply rdn_cons1; [lia | exact B2b|]. reflexivity. }
    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1422992 /\ (1422992 + 124 <= q \/ q + 32 + 16 <= 1422992 + 120) /\ 1422992 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 3%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1422992 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 3%nat)%nat true R1 M1 model1 q 2 7029536 (2 * 3) 0 0 (zero_lines 3%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 1426336) || ((1430328 <=? a) && (a + Z.of_nat n <=? 7027536)) || ((7028084 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 1422992 <= a -> a + n <= 1422992 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1409024 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1422992) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7027520) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
           DDF IMG3 (fun d k Hd Hk => FW3 1423024 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1423032 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1423048 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1423080 8%nat _ SObuf eq_refl)
           (LIT3 1423088 8%nat _ SObufsz eq_refl) (LIT3 7027520 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
           (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1423000 8%nat _ SOrpos eq_refl)
           (LIT3 1423008 8%nat _ SOrend eq_refl) (LIT3 1422984 8%nat _ (XCC 16%nat 1422984 8 1422752 eq_refl) eq_refl) (LIT3 1422892 4%nat _ (XCC 17%nat 1422892 4 4294967295 eq_refl) eq_refl) (LIT3 1422792 8%nat _ (XCC 18%nat 1422792 8 0 eq_refl) eq_refl) (LIT3 1422808 8%nat _ (XCC 19%nat 1422808 8 0 eq_refl) eq_refl) (LIT3 1422760 8%nat _ (XCC 20%nat 1422760 8 0 eq_refl) eq_refl)
           (LIT3 1422768 8%nat _ (XCC 21%nat 1422768 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x13f6b8) M3 R4 (Z_to_bv 64 0x1379d8) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x1379d8) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

End Exit.
End FPX_1.
