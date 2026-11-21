(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed rdn_cons1, msteps_vis_fx, exit_preB and 4 more. *)
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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0248. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.ShapeLaws OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvPiece OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DiagLoopK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvStdio OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0248.NraDrvPrintfK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0248.NraDrvPrintf1.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraDrvExit. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Na0DrvP_dpXB Na0DrvP_dpX2B_pre Na0DrvP_dpX3B_pre Na0DrvP_dpX4B_pre. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraDrvExit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0ExitCells OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DrvP_dpXB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DrvP_dpX2B_pre OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DrvP_dpX3B_pre OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DrvP_dpX4B_pre OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232.Na0DrvP_dpXd_2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232.Na0DrvP_dpXd_3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232.Na0DrvP_dpXd_4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_NraDrvExitB () := "C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses;subrelationC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedI45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes3nat02I46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr07I46Stdlib9micromega7EnvRing5PExpr00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00K46Stdlib9micromega7EnvRing5PExpr01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic3and00C47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2eq00C47Corelib9RelationsDRelation_Definitions8relationC47Corelib4Init3Nat3mulI46Stdlib;setoid_ring<Ring_polynom5PExpr00K47Corelib4Init9Datatypes4list01K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib9micromega7EnvRing5PExpr05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega:ZMicromega=Zeval_formulaC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions5bv_eqC47Corelib7Classes9Morphisms@subrelation_reflC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_00634Spec:zero_linesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2or00K46Stdlib;setoid_ring<Ring_polynom5PExpr05C56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic3notC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms6ProperC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic8f_equal2C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib;NraDrvExitB8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA5lzinvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c49OSSVerify5KrLib;NraDrvExitB5exitBC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib;NraDrvExitB9exit_preBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK7stdoutAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0248=NraDrvPrintf18stdoutXAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asanANa0DrvP_dpX2B_preAAS0DRVP_dpX2B_pre7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_01199Na0DrvLib@store_ok_definedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC49OSSVerify5KrLib:NraDrvExit<wsg_writableC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib:NraDrvExit;sh_writableC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List<nth_error_InC49OSSVerify5KrLib:NraDrvExit;ex_cell_visC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_00356ArtMem:art_bytes1C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib;NraDrvExitB<cells_at_nthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio8img_cellC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib4asanANa0DrvP_dpX2B_preAAS0DRVP_dpX2B_pre>dpX2B_pre_concC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_lzinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool<orb_true_iffC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC59OSSVerify5KrLib7Mh_0119;Na0DrvStdio6rdn_trC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addc49OSSVerify5KrLib;NraDrvExitB9rdn_cons1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK6wv_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0248=NraDrvPrintf15nl_ptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00639ShapeLaws>t_exit_has_nilC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib7Mh_0116:As0DrvKitA;sbm_lazy_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA=sbm_halted_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK8sbm_fds'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7wv_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK6wv_iovC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom3Pol00C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z8max_specC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_2>AS0DRVP_dpXd_27alignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic8eq_transC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_2>AS0DRVP_dpXd_2;dpXd_2_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctKsame_but_materialized_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA9lzinv_sbmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKArz_exit_at_lit_lzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib7sbm_fdsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c49OSSVerify5KrLib;NraDrvExitB=msteps_vis_fxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7wv_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7wv_loopC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega6VarMap4findC46Stdlib9micromega5Tauto7eval_bfC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9Morphisms;ProperProxyC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00C47Corelib7Program6Basics4implK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio8EX_CELLSC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib;NraDrvExitB:XC_CELLS_BC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK5SOBUFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asanANa0DrvP_dpX2B_preAAS0DRVP_dpX2B_pre<KS_dpX2B_preC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C47Corelib7Classes?RelationClasses=iff_ReflexiveI4ELinuxProcessSemantics?LinuxProcessSem5State5event00I46Stdlib;setoid_ring<Ring_polynom3Mon00I47Corelib7Numbers7BinNums8positive00C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7WV_KEEPC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_2>AS0DRVP_dpXd_29KS_dpXd_2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib;NraDrvExitB;fetch_exitAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX?is_ecall_ECALLWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asanANa0DrvP_dpX3B_preAAS0DRVP_dpX3B_pre7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asanANa0DrvP_dpX3B_preAAS0DRVP_dpX3B_pre>dpX3B_pre_concC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_3>AS0DRVP_dpXd_37alignedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_3>AS0DRVP_dpXd_3;dpXd_3_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asanANa0DrvP_dpX3B_preAAS0DRVP_dpX3B_pre<KS_dpX3B_preC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_3>AS0DRVP_dpXd_39KS_dpXd_3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asanANa0DrvP_dpX4B_preAAS0DRVP_dpX4B_pre7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asanANa0DrvP_dpX4B_preAAS0DRVP_dpX4B_pre>dpX4B_pre_concC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_4>AS0DRVP_dpXd_47alignedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_4>AS0DRVP_dpXd_4;dpXd_4_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asanANa0DrvP_dpX4B_preAAS0DRVP_dpX4B_pre<KS_dpX4B_preC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232>Na0DrvP_dpXd_4>AS0DRVP_dpXd_49KS_dpXd_4C1?~~~~~~~~~~~~~~~".
Ltac2 kr_t_NraDrvExitB () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c49OSSVerify5KrLib;NraDrvExitB8cells_atC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6to_natC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List<nth_error_InC47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01C46Stdlib6ZArith4Zdiv9Zplus_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedC59OSSVerify5KrLib7Mh_00387SeqExec7rdn_appC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC59OSSVerify5KrLib7Mh_01059SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib7Mh_0116:As0DrvKitA5lzinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct6hcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitAEmrestrict_munrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0036=AsanAcctShapeGsrz_msteps_restricted_TC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I47Corelib4Init9Datatypes4bool00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs8asegs_wxC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01c49OSSVerify5KrLib;NraDrvExitB9exit_preBC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK7stdoutAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0248=NraDrvPrintf18stdoutXAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib;NraDrvExitB5exitBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib4asan<Na0DrvP_dpXB<AS0DRVP_dpXB7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_01199Na0DrvLib@store_ok_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC49OSSVerify5KrLib:NraDrvExit<wsg_writableC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib:NraDrvExit;sh_writableC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib:NraDrvExit;ex_cell_visC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_00356ArtMem:art_bytes1C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib;NraDrvExitB<cells_at_nthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio8img_cellC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8f_equal2C47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib4asan<Na0DrvP_dpXB<AS0DRVP_dpXB9dpXB_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_lzinvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib7Mh_0116:As0DrvKitA=sbm_halted_eqC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKArz_exit_at_lit_lzC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC59OSSVerify5KrLib7Mh_01199Na0DrvLib7sbm_fdsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c49OSSVerify5KrLib;NraDrvExitB=msteps_vis_fxC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbC47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio8EX_CELLSC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib;NraDrvExitB:XC_CELLS_BC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK5SOBUFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib4asan<Na0DrvP_dpXB<AS0DRVP_dpXB7KS_dpXBC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib;NraDrvExitB;fetch_exitAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX?is_ecall_ECALLWC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00". Local Ltac lia := L5FastLiaT.plia2.
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
ltac2:(KReplay.run1 (kr_t_NraDrvExitB ()) [] "h01ch11xh22HCh32Hnh42MVh51ah61ih71lh81nh91vp;1p;2p;3p;4p;5p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9P0p1001fp4p710p9P0g002^R1p4p710p8P0g003?R2p4p710p8P0P2p4p7210p8p1003\p4p70p1004Lp4p710p8p1004jp4p70p1005Xp4p710p8g0064j10Tg006Yj1>Tg0077j16Tg007Zj14Tg008<j2;Tg008\j1:Tg009<j2CTg00:5j3?Tg00:Sj42Tg00;3j27Tg00;Uj31TP2j35Tg00;oj29Tg00<Uj3=Tg00=2j1ETg00=Rj43Tg00>Cj2DTP1j3<Tg00?Kj38Tg00?bj3BTg00@Dj5@Tg00@ej6ATg00A@#0#0#0R1#0#0#0#>R2#6%>1#6R1#4[g00AeR0/;0R3/;0R4#:g00BCf5R5f4R6'C%44A?456P3P0P0P0f3R7f2R8C2f1R9C2,7431%:1R1#4R:g00BbR;f8R<f0R=9530R>9500,92R?A=00>#ER>C3A=30=,92,D>,71R131X04R2f6R@5<4A84=<P;f;P?P>C3=1:1X04P9O1[^14[f7R<984=P;f:P?P>C3=1:1X04P9O1[^14P;f9P?P>C3=1:1X04=<4<[AB42@P9P3P0P0P0P6P7C2P8C2R8P4P@P5P8P=D@EAW3W2X90X80X50W6W7W4o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_NraDrvExitB ()) [] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9P0p1001fp4p710p9P0p1002^p4p710p8P0p1003?R1p4p710p8P0P1p4p7210p8p1003\p4p70p1004Lp4p710p8p1004jp4p70p1005Xp4p710p8g0064j11Tg006Yj14Tg0077j17Tg007Zj1>Tg00F2j16Tg00Q2j2;Tg00Qej3:Tg00;3j25Tg00Kjj28Tg00RHj13Tg00;oj29Tg00Rmj2=Tg00;Uj3<Tf0R1#1#1p=2%31#3p=0g00A@R1#1#2#2R0#4R2#7R3#>R4%01#2#0#6R51;255:2,53'8g00Bb%10#4%21#0#1#0#0#2#3#0#1#0#1#2#6'9'=g00So,535<4do"). Qed.

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

(* [comment removed for export] *)
Definition XC_CELLS_B : list (Z * Z * Z) :=
  [(7028080, 4, 0); (7028115, 1, 0); (7027552, 8, 7027560); (7027544, 4, 4); (7027568, 8, 1277044); (7027824, 8, 648332); (7027540, 4, 0); (7027560, 8, 0); (7029512, 8, 0); (1423464, 8, 1423232); (1423372, 4, 4294967295); (1423272, 8, 0); (1423288, 8, 0); (1423240, 8, 0); (1423248, 8, 0); (1423224, 8, 1422992); (1422984, 8, 1422752); (1422892, 4, 4294967295); (1422792, 8, 0); (1422808, 8, 0); (1422760, 8, 0); (1422768, 8, 0); (7027576, 8, 1277044); (7027832, 8, 716372); (6889684, 1, 0); (7027584, 8, 997176); (7027592, 8, 477636); (7027840, 8, 1422544); (7027848, 8, 0)].
Definition exitB (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS_B
  /\ rdn ASEGS MV (Z_to_bv 64 6896216) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x15b8a0 <= i < 0x15c3a0 -> MV (Z_to_bv 64 i) = None).


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
  Local Abbreviation ex_cell_vis := (@NraDrvExit.ex_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hex M0).
  Local Abbreviation sh_writable := (@NraDrvExit.sh_writable scfg L ar IL HI ICok ILY sp0 Hsp DL M0).
  Local Abbreviation wsg_writable := (@NraDrvExit.wsg_writable sp0 Hsp M0).

  Definition exit_preB (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1409024 -> MV (Z_to_bv 64 i) = None)
    /\ exitB tid MV.

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_0B : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preB LB LK cr A M model S tid ->
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
    assert (HSa : AS0DRVP_dpXB.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : Mh_0084.L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : Mh_0084.L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> Mh_0084.L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147469128 <=? a) && (a + n <=? 2147470932) || (2147623588 <=? a) && (a + n <=? 2147623604) || (2147628820 <=? a) && (a + n <=? 2147629172)) = true -> Mh_0084.L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_B i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_B i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_B i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x15b8a0 <=? a) && (a + Z.of_nat n <=? 0x15c3a0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXB.dpXB_conc fx R MV V
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
           (XCC 2%nat 7027552 8 7027560 eq_refl) (XCC 3%nat 7027544 4 4 eq_refl) (XCC 26%nat 7027592 8 477636 eq_refl) (XCC 28%nat 7027848 8 0 eq_refl) (XCC 6%nat 7027540 4 0 eq_refl)
           (STC1 11%nat 1430164 0 eq_refl eq_refl) (XCC 25%nat 7027584 8 997176 eq_refl) (XCC 27%nat 7027840 8 1422544 eq_refl) (XCC 22%nat 7027576 8 1277044 eq_refl)
           (XCC 23%nat 7027832 8 716372 eq_refl) (XCC1 24%nat 6889684 0 eq_refl eq_refl) (XCC 4%nat 7027568 8 1277044 eq_refl) (XCC 5%nat 7027824 8 648332 eq_refl)
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
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXB.KS_dpXB; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_2B : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preB LB LK cr A M model S tid ->
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
    assert (HSa : AS0DRVP_dpX2B_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : Mh_0084.L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : Mh_0084.L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> Mh_0084.L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147469128 <=? a) && (a + n <=? 2147470932) || (2147623588 <=? a) && (a + n <=? 2147623604) || (2147628820 <=? a) && (a + n <=? 2147629172)) = true -> Mh_0084.L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_B i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_B i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_B i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x15b8a0 <=? a) && (a + Z.of_nat n <=? 0x15c3a0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpX2B_pre.dpX2B_pre_conc fx R MV V
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
           HTr (XCC 0%nat 7028080 4 0 eq_refl) (XCC1 1%nat 7028115 0 eq_refl eq_refl) (XCC 2%nat 7027552 8 7027560 eq_refl) (XCC 3%nat 7027544 4 4 eq_refl) (XCC 26%nat 7027592 8 477636 eq_refl)
           (XCC 28%nat 7027848 8 0 eq_refl) (XCC 6%nat 7027540 4 0 eq_refl) (STC1 11%nat 1430164 0 eq_refl eq_refl) (XCC 25%nat 7027584 8 997176 eq_refl) (XCC 27%nat 7027840 8 1422544 eq_refl) (XCC 22%nat 7027576 8 1277044 eq_refl)
           (XCC 23%nat 7027832 8 716372 eq_refl) (XCC1 24%nat 6889684 0 eq_refl eq_refl) (XCC 4%nat 7027568 8 1277044 eq_refl) (XCC 5%nat 7027824 8 648332 eq_refl) (STC1 10%nat 2038048 0 eq_refl eq_refl) (XCC 7%nat 7027560 8 0 eq_refl)
           (STC1 3%nat 1426448 0 eq_refl eq_refl) (STC 0%nat 1412008 8 1412008 eq_refl) (STC 2%nat 1426368 8 1 eq_refl) (STC 4%nat 1430160 4 1 eq_refl) (STC 5%nat 1430320 8 0 eq_refl) (STC1 8%nat 1443672 1 eq_refl eq_refl)
           (STC 7%nat 1440376 8 2147450880 eq_refl) (DSC 1423520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145984)) ltac:(img_rd) eq_refl) (DSC 1423536 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1438428 1 eq_refl eq_refl) (DSC 1423536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 2037280 8 18446744073709551615 eq_refl)
           (STC 1%nat 1412520 8 1347948 eq_refl) (DSC 1423576 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146016)) ltac:(img_rd) eq_refl) (DSC 1423600 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1423640 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1423648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146144)) ltac:(img_rd) eq_refl) (DSC 1423664 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146176)) ltac:(img_rd) eq_refl) (DSC 1423728 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1423728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1423768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146272)) ltac:(img_rd) eq_refl) (DSC 1423792 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1423840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146304)) ltac:(img_rd) eq_refl) (DSC 1423856 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1423856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1423896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146464)) ltac:(img_rd) eq_refl) (DSC 1423920 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1423920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl) (DSC 1423984 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146528)) ltac:(img_rd) eq_refl) (DSC 1424048 1%nat [Z_to_bv 8 192] ltac:(img_rd) eq_refl) (DSC 1424048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 6848)) ltac:(img_rd) eq_refl) (DSC 1424088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 153376)) ltac:(img_rd) eq_refl) (DSC 1424112 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1424112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 3424)) ltac:(img_rd) eq_refl) (DSC 1424152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156800)) ltac:(img_rd) eq_refl) (DSC 1424176 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156832)) ltac:(img_rd) eq_refl) (DSC 1424240 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1424240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1424280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156960)) ltac:(img_rd) eq_refl) (DSC 1424304 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1424304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156992)) ltac:(img_rd) eq_refl) (DSC 1424368 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157024)) ltac:(img_rd) eq_refl) (DSC 1424432 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157056)) ltac:(img_rd) eq_refl) (DSC 1424496 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1424496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157088)) ltac:(img_rd) eq_refl) (DSC 1424560 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157280)) ltac:(img_rd) eq_refl) (DSC 1424624 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157664)) ltac:(img_rd) eq_refl) (DSC 1424688 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
           (DSC 1424688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1424728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157728)) ltac:(img_rd) eq_refl) (DSC 1424752 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1424792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157792)) ltac:(img_rd) eq_refl) (DSC 1424816 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157824)) ltac:(img_rd) eq_refl) (DSC 1424880 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1424880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1424920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157920)) ltac:(img_rd) eq_refl) (DSC 1424944 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1424984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158016)) ltac:(img_rd) eq_refl) (DSC 1425008 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158112)) ltac:(img_rd) eq_refl) (DSC 1425072 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1425072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158208)) ltac:(img_rd) eq_refl) (DSC 1425136 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158304)) ltac:(img_rd) eq_refl) (DSC 1425200 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158400)) ltac:(img_rd) eq_refl) (DSC 1425264 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1425264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1425304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158528)) ltac:(img_rd) eq_refl) (DSC 1425328 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1425368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158592)) ltac:(img_rd) eq_refl) (DSC 1425392 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1425432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158656)) ltac:(img_rd) eq_refl) (DSC 1425456 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1425456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158752)) ltac:(img_rd) eq_refl) (DSC 1425520 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158848)) ltac:(img_rd) eq_refl) (DSC 1425584 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158944)) ltac:(img_rd) eq_refl) (DSC 1425648 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1425648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159040)) ltac:(img_rd) eq_refl) (DSC 1425712 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159136)) ltac:(img_rd) eq_refl) (DSC 1425776 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159232)) ltac:(img_rd) eq_refl) (DSC 1425840 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1425840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1425880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159552)) ltac:(img_rd) eq_refl) (DSC 1425904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1425944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159584)) ltac:(img_rd) eq_refl) (DSC 1425968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159616)) ltac:(img_rd) eq_refl) (DSC 1426032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1426032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159648)) ltac:(img_rd) eq_refl) (DSC 1426096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1426144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159776)) ltac:(img_rd) eq_refl) (DSC 1426160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1426160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1426200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159872)) ltac:(img_rd) eq_refl) (DSC 1426224 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1426224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 544)) ltac:(img_rd) eq_refl) (DSC 1426264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1381664)) ltac:(img_rd) eq_refl) (DSC 1426288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1426288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1426328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (XCC 8%nat 7029512 8 0 eq_refl) (XCC 9%nat 1423464 8 1423232 eq_refl) (XCC 10%nat 1423372 4 4294967295 eq_refl) (XCC 11%nat 1423272 8 0 eq_refl) (XCC 12%nat 1423288 8 0 eq_refl) (XCC 13%nat 1423240 8 0 eq_refl)
           (XCC 14%nat 1423248 8 0 eq_refl) (XCC 15%nat 1423224 8 1422992 eq_refl) SOlock SOwpos SOwbase SOwrite
           CANc SOfd) as
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
    assert (DWR : Mh_0084.L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : Mh_0084.L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
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
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_3B : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preB LB LK cr A M model S tid ->
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
    assert (HSa : AS0DRVP_dpX3B_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : Mh_0084.L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : Mh_0084.L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> Mh_0084.L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147469128 <=? a) && (a + n <=? 2147470932) || (2147623588 <=? a) && (a + n <=? 2147623604) || (2147628820 <=? a) && (a + n <=? 2147629172)) = true -> Mh_0084.L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_B i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_B i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_B i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x15b8a0 <=? a) && (a + Z.of_nat n <=? 0x15c3a0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpX3B_pre.dpX3B_pre_conc fx R MV V
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
           HTr (XCC 0%nat 7028080 4 0 eq_refl) (XCC1 1%nat 7028115 0 eq_refl eq_refl) (XCC 2%nat 7027552 8 7027560 eq_refl) (XCC 3%nat 7027544 4 4 eq_refl) (XCC 26%nat 7027592 8 477636 eq_refl)
           (XCC 28%nat 7027848 8 0 eq_refl) (XCC 6%nat 7027540 4 0 eq_refl) (STC1 11%nat 1430164 0 eq_refl eq_refl) (XCC 25%nat 7027584 8 997176 eq_refl) (XCC 27%nat 7027840 8 1422544 eq_refl) (XCC 22%nat 7027576 8 1277044 eq_refl)
           (XCC 23%nat 7027832 8 716372 eq_refl) (XCC1 24%nat 6889684 0 eq_refl eq_refl) (XCC 4%nat 7027568 8 1277044 eq_refl) (XCC 5%nat 7027824 8 648332 eq_refl) (STC1 10%nat 2038048 0 eq_refl eq_refl) (XCC 7%nat 7027560 8 0 eq_refl)
           (STC1 3%nat 1426448 0 eq_refl eq_refl) (STC 0%nat 1412008 8 1412008 eq_refl) (STC 2%nat 1426368 8 1 eq_refl) (STC 4%nat 1430160 4 1 eq_refl) (STC 5%nat 1430320 8 0 eq_refl) (STC1 8%nat 1443672 1 eq_refl eq_refl)
           (STC 7%nat 1440376 8 2147450880 eq_refl) (DSC 1423520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145984)) ltac:(img_rd) eq_refl) (DSC 1423536 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1438428 1 eq_refl eq_refl) (DSC 1423536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 2037280 8 18446744073709551615 eq_refl)
           (STC 1%nat 1412520 8 1347948 eq_refl) (DSC 1423576 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146016)) ltac:(img_rd) eq_refl) (DSC 1423600 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1423640 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1423648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146144)) ltac:(img_rd) eq_refl) (DSC 1423664 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146176)) ltac:(img_rd) eq_refl) (DSC 1423728 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1423728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1423768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146272)) ltac:(img_rd) eq_refl) (DSC 1423792 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1423840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146304)) ltac:(img_rd) eq_refl) (DSC 1423856 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1423856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1423896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146464)) ltac:(img_rd) eq_refl) (DSC 1423920 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1423920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl) (DSC 1423984 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146528)) ltac:(img_rd) eq_refl) (DSC 1424048 1%nat [Z_to_bv 8 192] ltac:(img_rd) eq_refl) (DSC 1424048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 6848)) ltac:(img_rd) eq_refl) (DSC 1424088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 153376)) ltac:(img_rd) eq_refl) (DSC 1424112 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1424112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 3424)) ltac:(img_rd) eq_refl) (DSC 1424152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156800)) ltac:(img_rd) eq_refl) (DSC 1424176 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156832)) ltac:(img_rd) eq_refl) (DSC 1424240 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1424240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1424280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156960)) ltac:(img_rd) eq_refl) (DSC 1424304 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1424304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156992)) ltac:(img_rd) eq_refl) (DSC 1424368 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157024)) ltac:(img_rd) eq_refl) (DSC 1424432 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157056)) ltac:(img_rd) eq_refl) (DSC 1424496 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1424496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157088)) ltac:(img_rd) eq_refl) (DSC 1424560 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157280)) ltac:(img_rd) eq_refl) (DSC 1424624 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157664)) ltac:(img_rd) eq_refl) (DSC 1424688 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
           (DSC 1424688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1424728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157728)) ltac:(img_rd) eq_refl) (DSC 1424752 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1424792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157792)) ltac:(img_rd) eq_refl) (DSC 1424816 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157824)) ltac:(img_rd) eq_refl) (DSC 1424880 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1424880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1424920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157920)) ltac:(img_rd) eq_refl) (DSC 1424944 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1424984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158016)) ltac:(img_rd) eq_refl) (DSC 1425008 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158112)) ltac:(img_rd) eq_refl) (DSC 1425072 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1425072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158208)) ltac:(img_rd) eq_refl) (DSC 1425136 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158304)) ltac:(img_rd) eq_refl) (DSC 1425200 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158400)) ltac:(img_rd) eq_refl) (DSC 1425264 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1425264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1425304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158528)) ltac:(img_rd) eq_refl) (DSC 1425328 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1425368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158592)) ltac:(img_rd) eq_refl) (DSC 1425392 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1425432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158656)) ltac:(img_rd) eq_refl) (DSC 1425456 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1425456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158752)) ltac:(img_rd) eq_refl) (DSC 1425520 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158848)) ltac:(img_rd) eq_refl) (DSC 1425584 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158944)) ltac:(img_rd) eq_refl) (DSC 1425648 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1425648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159040)) ltac:(img_rd) eq_refl) (DSC 1425712 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159136)) ltac:(img_rd) eq_refl) (DSC 1425776 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159232)) ltac:(img_rd) eq_refl) (DSC 1425840 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1425840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1425880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159552)) ltac:(img_rd) eq_refl) (DSC 1425904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1425944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159584)) ltac:(img_rd) eq_refl) (DSC 1425968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159616)) ltac:(img_rd) eq_refl) (DSC 1426032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1426032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159648)) ltac:(img_rd) eq_refl) (DSC 1426096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1426144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159776)) ltac:(img_rd) eq_refl) (DSC 1426160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1426160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1426200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159872)) ltac:(img_rd) eq_refl) (DSC 1426224 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1426224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 544)) ltac:(img_rd) eq_refl) (DSC 1426264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1381664)) ltac:(img_rd) eq_refl) (DSC 1426288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1426288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1426328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (XCC 8%nat 7029512 8 0 eq_refl) (XCC 9%nat 1423464 8 1423232 eq_refl) (XCC 10%nat 1423372 4 4294967295 eq_refl) (XCC 11%nat 1423272 8 0 eq_refl) (XCC 12%nat 1423288 8 0 eq_refl) (XCC 13%nat 1423240 8 0 eq_refl)
           (XCC 14%nat 1423248 8 0 eq_refl) (XCC 15%nat 1423224 8 1422992 eq_refl) SOlock SOwpos SOwbase SOwrite
           CANc SOfd) as
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
    assert (DWR : Mh_0084.L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : Mh_0084.L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
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
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_4B : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preB LB LK cr A M model S tid ->
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
    assert (HSa : AS0DRVP_dpX4B_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : Mh_0084.L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : Mh_0084.L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> Mh_0084.L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147469128 <=? a) && (a + n <=? 2147470932) || (2147623588 <=? a) && (a + n <=? 2147623604) || (2147628820 <=? a) && (a + n <=? 2147629172)) = true -> Mh_0084.L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_B i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_B i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_B i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (Mh_0035.ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x15b8a0 <=? a) && (a + Z.of_nat n <=? 0x15c3a0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpX4B_pre.dpX4B_pre_conc fx R MV V
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
           HTr (XCC 0%nat 7028080 4 0 eq_refl) (XCC1 1%nat 7028115 0 eq_refl eq_refl) (XCC 2%nat 7027552 8 7027560 eq_refl) (XCC 3%nat 7027544 4 4 eq_refl) (XCC 26%nat 7027592 8 477636 eq_refl)
           (XCC 28%nat 7027848 8 0 eq_refl) (XCC 6%nat 7027540 4 0 eq_refl) (STC1 11%nat 1430164 0 eq_refl eq_refl) (XCC 25%nat 7027584 8 997176 eq_refl) (XCC 27%nat 7027840 8 1422544 eq_refl) (XCC 22%nat 7027576 8 1277044 eq_refl)
           (XCC 23%nat 7027832 8 716372 eq_refl) (XCC1 24%nat 6889684 0 eq_refl eq_refl) (XCC 4%nat 7027568 8 1277044 eq_refl) (XCC 5%nat 7027824 8 648332 eq_refl) (STC1 10%nat 2038048 0 eq_refl eq_refl) (XCC 7%nat 7027560 8 0 eq_refl)
           (STC1 3%nat 1426448 0 eq_refl eq_refl) (STC 0%nat 1412008 8 1412008 eq_refl) (STC 2%nat 1426368 8 1 eq_refl) (STC 4%nat 1430160 4 1 eq_refl) (STC 5%nat 1430320 8 0 eq_refl) (STC1 8%nat 1443672 1 eq_refl eq_refl)
           (STC 7%nat 1440376 8 2147450880 eq_refl) (DSC 1423520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145984)) ltac:(img_rd) eq_refl) (DSC 1423536 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1438428 1 eq_refl eq_refl) (DSC 1423536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 2037280 8 18446744073709551615 eq_refl)
           (STC 1%nat 1412520 8 1347948 eq_refl) (DSC 1423576 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146016)) ltac:(img_rd) eq_refl) (DSC 1423600 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1423600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1423640 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1423648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146144)) ltac:(img_rd) eq_refl) (DSC 1423664 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146176)) ltac:(img_rd) eq_refl) (DSC 1423728 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1423728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1423768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146272)) ltac:(img_rd) eq_refl) (DSC 1423792 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1423840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146304)) ltac:(img_rd) eq_refl) (DSC 1423856 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1423856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1423896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146464)) ltac:(img_rd) eq_refl) (DSC 1423920 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1423920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1423960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1423968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl) (DSC 1423984 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1423984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146528)) ltac:(img_rd) eq_refl) (DSC 1424048 1%nat [Z_to_bv 8 192] ltac:(img_rd) eq_refl) (DSC 1424048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 6848)) ltac:(img_rd) eq_refl) (DSC 1424088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 153376)) ltac:(img_rd) eq_refl) (DSC 1424112 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1424112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 3424)) ltac:(img_rd) eq_refl) (DSC 1424152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156800)) ltac:(img_rd) eq_refl) (DSC 1424176 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156832)) ltac:(img_rd) eq_refl) (DSC 1424240 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1424240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1424280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156960)) ltac:(img_rd) eq_refl) (DSC 1424304 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1424304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 156992)) ltac:(img_rd) eq_refl) (DSC 1424368 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157024)) ltac:(img_rd) eq_refl) (DSC 1424432 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157056)) ltac:(img_rd) eq_refl) (DSC 1424496 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1424496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157088)) ltac:(img_rd) eq_refl) (DSC 1424560 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157280)) ltac:(img_rd) eq_refl) (DSC 1424624 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157664)) ltac:(img_rd) eq_refl) (DSC 1424688 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
           (DSC 1424688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1424728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157728)) ltac:(img_rd) eq_refl) (DSC 1424752 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1424752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1424792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157792)) ltac:(img_rd) eq_refl) (DSC 1424816 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1424816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1424856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157824)) ltac:(img_rd) eq_refl) (DSC 1424880 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1424880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1424920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1424928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 157920)) ltac:(img_rd) eq_refl) (DSC 1424944 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1424944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1424984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1424992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158016)) ltac:(img_rd) eq_refl) (DSC 1425008 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158112)) ltac:(img_rd) eq_refl) (DSC 1425072 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1425072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158208)) ltac:(img_rd) eq_refl) (DSC 1425136 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158304)) ltac:(img_rd) eq_refl) (DSC 1425200 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158400)) ltac:(img_rd) eq_refl) (DSC 1425264 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1425264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1425304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158528)) ltac:(img_rd) eq_refl) (DSC 1425328 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1425368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158592)) ltac:(img_rd) eq_refl) (DSC 1425392 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1425392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1425432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158656)) ltac:(img_rd) eq_refl) (DSC 1425456 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1425456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158752)) ltac:(img_rd) eq_refl) (DSC 1425520 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158848)) ltac:(img_rd) eq_refl) (DSC 1425584 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 158944)) ltac:(img_rd) eq_refl) (DSC 1425648 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1425648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159040)) ltac:(img_rd) eq_refl) (DSC 1425712 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159136)) ltac:(img_rd) eq_refl) (DSC 1425776 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1425776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1425816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159232)) ltac:(img_rd) eq_refl) (DSC 1425840 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1425840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1425880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1425888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159552)) ltac:(img_rd) eq_refl) (DSC 1425904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1425944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1425952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159584)) ltac:(img_rd) eq_refl) (DSC 1425968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1425968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159616)) ltac:(img_rd) eq_refl) (DSC 1426032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1426032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159648)) ltac:(img_rd) eq_refl) (DSC 1426096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1426096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1426136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1426144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159776)) ltac:(img_rd) eq_refl) (DSC 1426160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1426160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1426200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 159872)) ltac:(img_rd) eq_refl) (DSC 1426224 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1426224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 544)) ltac:(img_rd) eq_refl) (DSC 1426264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1426272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1381664)) ltac:(img_rd) eq_refl) (DSC 1426288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1426288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1426328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (XCC 8%nat 7029512 8 0 eq_refl) (XCC 9%nat 1423464 8 1423232 eq_refl) (XCC 10%nat 1423372 4 4294967295 eq_refl) (XCC 11%nat 1423272 8 0 eq_refl) (XCC 12%nat 1423288 8 0 eq_refl) (XCC 13%nat 1423240 8 0 eq_refl)
           (XCC 14%nat 1423248 8 0 eq_refl) (XCC 15%nat 1423224 8 1422992 eq_refl) SOlock SOwpos SOwbase SOwrite
           CANc SOfd) as
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
    assert (DWR : Mh_0084.L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : Mh_0084.L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
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
