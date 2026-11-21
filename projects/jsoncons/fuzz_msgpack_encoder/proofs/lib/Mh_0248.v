(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed nl_pt, printf1_run, printf2_run and 2 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0DrvPrintf1.v, lines 83-91, 96, 114-143, 153-461. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0248 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes3nat02I46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00I46Stdlib9micromega7EnvRing5PExpr00C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init9Datatypes4prod00K46Stdlib9micromega=RingMicromega5Psatz07I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3powK45stdpp9bitvector;definitions2bv01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or02I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega:ZMicromega;ZArithProof03I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvI46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega:ZMicromega=Zeval_formulaC46Stdlib9micromega5Tauto7eval_bfC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t01C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes6option01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK7stdoutAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio;pr_cell_visC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib7Mh_00356ArtMem:art_bytes1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC79OSSVerify5KrLib4asan7Mh_0232<Na0DrvP_dpA3<AS0DRVP_dpA37alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_01199Na0DrvLib@store_ok_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib7Mh_0119;Na0DrvStdio7stk_sh0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses7rew_iffI47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib7Mh_0089:IcptIfaceA:icl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA;aicl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio7img_sh0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv?cell_zero_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232<Na0DrvP_dpA3<AS0DRVP_dpA39dpA3_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK3WpfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib3CWAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio6rdn_trC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib7Mh_0119;Na0DrvPiece9drv_pieceC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega6VarMap1t02C46Stdlib9micromega6VarMap4findK46Stdlib9micromega7EnvRing5PExpr05C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op201I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs7IMG_W_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio8PR_CELLSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib4Init5Logic4True01c59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK5SOBUFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232<Na0DrvP_dpA3<AS0DRVP_dpA37KS_dpA3C1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses;subrelationC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismI46Stdlib;setoid_ring<Ring_polynom5PExpr00C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3lebC47Corelib9RelationsDRelation_Definitions8relationC45stdpp9bitvector;definitions5bv_eqK46Stdlib;setoid_ring<Ring_polynom5PExpr04C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9Morphisms@subrelation_reflC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3maxC47Corelib7Classes9MorphismsBsubrelation_properK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC59OSSVerify5KrLib7Mh_00634Spec1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0248=NraDrvPrintf18stdout0AC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsc59OSSVerify5KrLib7Mh_0248=NraDrvPrintf18stdoutXAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0248=NraDrvPrintf14Wpf1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232;Na0DrvP_dpA;AS0DRVP_dpA7alignedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232;Na0DrvP_dpA;AS0DRVP_dpA8dpA_concC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indc59OSSVerify5KrLib7Mh_0248=NraDrvPrintf13TRfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK8sbm_fds'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib7di_haltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00438AgentLib=errno_ret_litC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232ANa0DrvP_dpB_nottyAAS0DRVP_dpB_notty7alignedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232ANa0DrvP_dpB_nottyAAS0DRVP_dpB_notty>dpB_notty_concC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio8img_cellC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_lzinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA5lzinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK6wv_bufC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0248=NraDrvPrintf15nl_ptC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7wv_regsC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom3Pol00C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z8max_specC59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK6wv_iovC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib7sbm_vmlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA=sbm_halted_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib8ahid_sbmC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool8orb_propC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC79OSSVerify5KrLib4asan7Mh_0232<Na0DrvP_dpCd<AS0DRVP_dpCd7alignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232<Na0DrvP_dpCd<AS0DRVP_dpCd9dpCd_concC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC47Corelib7Classes9Morphisms;ProperProxyC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC59OSSVerify5KrLib7Mh_00368AsanAcctKsame_but_materialized_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7wv_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7wv_loopC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive:v_addi_pc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKArz_ioctl_winsz_lzC1?~~~~~~~~~~~~~~~K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Program6Basics4implC79OSSVerify5KrLib4asan7Mh_0232;Na0DrvP_dpA;AS0DRVP_dpA6KS_dpAC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232ANa0DrvP_dpB_nottyAAS0DRVP_dpB_notty<KS_dpB_nottyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7WV_KEEPC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232<Na0DrvP_dpCd<AS0DRVP_dpCd7KS_dpCdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOTTYI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs6c_keptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0248=NraDrvPrintf1<fetch_ioctlAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX?is_ecall_ECALLWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0248=NraDrvPrintf17nl_imgAC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom3Mon00C47Corelib7Classes?RelationClasses=iff_Reflexivec59OSSVerify5KrLib7Mh_0248=NraDrvPrintf16le4_m1C1?~~~~~~~~~~~~~~~".
Module NraDrvPrintfK.
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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvPiece OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvStdio.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232.Na0DrvP_dpA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232.Na0DrvP_dpA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232.Na0DrvP_dpA4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_NraDrvPrintfK () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3powK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK7stdoutAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio;pr_cell_visC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib7Mh_00356ArtMem:art_bytes1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC79OSSVerify5KrLib4asan7Mh_0232<Na0DrvP_dpA2<AS0DRVP_dpA27alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_01199Na0DrvLib@store_ok_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio7stk_sh0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C46Stdlib9micromega;ZifyClasses6eq_iffI47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib7Mh_0089:IcptIfaceA:icl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA;aicl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio7img_sh0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv?cell_zero_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib4Init5Logic7and_indC69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232<Na0DrvP_dpA2<AS0DRVP_dpA29dpA2_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK3WpfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib3CWAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio6rdn_trC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib7Mh_0119;Na0DrvPiece9drv_pieceC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0248=NraDrvPrintfK5SOBUFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio8PR_CELLSC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232<Na0DrvP_dpA2<AS0DRVP_dpA27KS_dpA2C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib7Mh_0119;Na0Drv_defs7IMG_W_AC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232<Na0DrvP_dpA4<AS0DRVP_dpA47alignedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232<Na0DrvP_dpA4<AS0DRVP_dpA49dpA4_concC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0232<Na0DrvP_dpA4<AS0DRVP_dpA47KS_dpA4C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SOBUF : Z := 7029536.
Definition stdoutA (j : Z) (MV : word -> option byte) : Prop :=
  rdn ASEGS MV (Z_to_bv 64 1422992) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5))                       (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423088) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024))                 (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423024) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (SOBUF + 1024)))       (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423032) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (SOBUF + 2 * j)))      (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423048) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SOBUF))                (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423132) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))           (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423136) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))           (* [comment removed for export] *)
  /\ (forall a n, 1422992 <= a -> a + n <= 1422992 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
  /\ (forall a n, SOBUF <= a -> a + n <= SOBUF + 1024 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
  /\ (forall i, 0 <= i < j -> rdn ASEGS MV (Z_to_bv 64 (SOBUF + 2 * i)) 1 = Some [Z_to_bv 8 48] /\ rdn ASEGS MV (Z_to_bv 64 (SOBUF + 2 * i + 1)) 1 = Some [Z_to_bv 8 10]).

(* [comment removed for export] *)
Definition Wpf (S j a : Z) : Prop :=
  S - 3232 <= a < S \/ 1422992 <= a < 1422996 \/ 1423032 <= a < 1423040 \/ SOBUF + 2 * j <= a < SOBUF + 2 * j + 2.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section PrintfK.
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
  Hypothesis Hpr : incl PR_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation rom := (seg_rom ASEGS).

  Lemma printf2_run : forall LB LK cr A M (model : Model) R (S canz : Z) K,
    dinvA LB LK cr A M model ->
    let MV := mrestrict (ahid A model) M in
    usp - 4096 <= S -> S + 32 <= usp -> S mod 16 = 0 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 716480 -> getr R 2%bv = Z_to_bv 64 S -> getr R 10%bv = Z_to_bv 64 86406 -> getr R 11%bv = Z_to_bv 64 (S + 24) ->
    (forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true) ->
    (forall i, 65536 <= i < 1409024 -> MV (Z_to_bv 64 i) = None) ->
    rdn ASEGS MV (Z_to_bv 64 7027520) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    rdn ASEGS MV (Z_to_bv 64 (S + 24)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    stdoutA 0 MV ->
    (forall (fx' : PropExec.FPState) R' M1 (model1 : Model),
        dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
        (forall x, In x AS0DRVP_dpA2.KS_dpA2 -> getr R' (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))) ->
        getr R' 10%bv = Z_to_bv 64 2 ->
        stdoutA 1 (mrestrict (ahid A model1) M1) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 0 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 0 a -> mrestrict (ahid A model1) M1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
        (forall a : word, MV a <> None -> mrestrict (ahid A model1) M1 a <> None) ->
        srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xaeec0) M1 rom) model1) K) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx R (Z_to_bv 64 0x6a2d4) M rom) model) K.
  Proof.
    intros LB LK cr A M model R S canz K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 WIN IMG CAN ARG SO KONT.
    pose proof Hsp as Hsp'. destruct SO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & FW & BW & BC).
    assert (PC : forall a n v, In (a, n, v) PR_CELLS -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hin; exact (pr_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hpr M0 _ _ _ _ _ _ a n v D Hin)).
    assert (P1 : forall a v, In (a, 1, v) PR_CELLS -> 0 <= v < 2 ^ 64 -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros a v Hin Hv. rewrite <- (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem.art_bytes1 v Hv). exact (PC a 1 v Hin). }
    set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
    destruct (AS0DRVP_dpA2.dpA2_conc fx R MV V) as (fx' & R' & MV' & GR & _ & FRZ & MS & KS & _ & Q10 & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & O4).
    all: cbn [V].
    all: try assumption.
    all: try (clear - Hsp' HS1 HS2 Hcan; lia).
    - (* [comment removed for export] *) intros d k Hd Hk. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *) intros i Hi. apply (store_ok_defined sp0); [lia|]. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *)
      intros i Hi. apply (stk_sh0 scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ _ D).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      clear - Hsp' Hal HS1 HS2 HS16 Hi. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x15180 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - (* [comment removed for export] *)
      apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x6b4300 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - intros d k Hd Hk. apply (FW 1422992 4); lia.
    - intros d k Hd Hk. apply (FW 1423032 8); lia.
    - intros d k Hd Hk. apply (BW 7029536 1); unfold SOBUF; lia.
    - intros d k Hd Hk. apply (BW 7029537 1); unfold SOBUF; lia.
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PC 0x15fa78 8 0x7fff8000 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x158c20 8 0x146850 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x158c28 8 0x14056c ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PC 0x158da0 8 0x148d68 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x158da8 8 0x14916c ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - (* [comment removed for export] *)
      unfold V in FRZ, MS; cbn beta iota in FRZ, MS.
      assert (FRW : forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 0 a -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
      { intros a Ha Hn. apply FRZ; [exact Ha | | | | |]; intros X; apply Hn; unfold Wpf, SOBUF; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx' R (Z_to_bv 64 0x6a2d4) R' (Z_to_bv 64 0xaeec0) MV' (Wpf S 0) K D MS GR FRW).
      + intros a [Ha|[Ha|[Ha|Ha]]]; unfold CWA; [right; left; lia | | |]; right; right.
        * exists 0x15b5a0, 0x15b8a0. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        * exists 0x15b5a0, 0x15b8a0. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        * exists 0x693b30, 0x6b4fb8. split; [unfold IMG_W_A; cbn [In]; tauto | unfold SOBUF in Ha; lia].
      + intros M1 model1 D1 SBM VIS FR1. apply (KONT fx' R' M1 model1 D1 SBM KS Q10); [|exact FR1 | rewrite VIS; exact FRW | rewrite VIS; exact GR].
        rewrite VIS. unfold stdoutA.
        assert (TR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
                     (forall i, a <= i < a + Z.of_nat n -> ~ Wpf S 0 i) -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Hr Ha Hn Ho. apply (rdn_tr MV MV' a n bs Hr Ha Hn). intros i Hi. apply FRW; [lia | exact (Ho i Hi)]. }
        split; [exact O1|]. split; [apply TR; [exact F2 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F3 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [exact O2|].
        split; [apply TR; [exact F5 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F6 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F7 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (FW a n); assumption|].
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (BW a n); assumption|].
        intros i Hi. destruct (Z.eq_dec i 0) as [->|N]; [split; [exact O4 | exact O3]|].
        destruct (BC i ltac:(lia)) as (B1 & B2).
        split; (apply TR; [assumption | unfold SOBUF; lia | unfold SOBUF; cbn; lia | intros x Hx; unfold Wpf, SOBUF in *; cbn in Hx; lia]).
  Qed.

  Lemma printf3_run : forall LB LK cr A M (model : Model) R (S canz : Z) K,
    dinvA LB LK cr A M model ->
    let MV := mrestrict (ahid A model) M in
    usp - 4096 <= S -> S + 32 <= usp -> S mod 16 = 0 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 716480 -> getr R 2%bv = Z_to_bv 64 S -> getr R 10%bv = Z_to_bv 64 86406 -> getr R 11%bv = Z_to_bv 64 (S + 24) ->
    (forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true) ->
    (forall i, 65536 <= i < 1409024 -> MV (Z_to_bv 64 i) = None) ->
    rdn ASEGS MV (Z_to_bv 64 7027520) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    rdn ASEGS MV (Z_to_bv 64 (S + 24)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    stdoutA 1 MV ->
    (forall (fx' : PropExec.FPState) R' M1 (model1 : Model),
        dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
        (forall x, In x AS0DRVP_dpA3.KS_dpA3 -> getr R' (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))) ->
        getr R' 10%bv = Z_to_bv 64 2 ->
        stdoutA 2 (mrestrict (ahid A model1) M1) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 1 a -> mrestrict (ahid A model1) M1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
        (forall a : word, MV a <> None -> mrestrict (ahid A model1) M1 a <> None) ->
        srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xaeec0) M1 rom) model1) K) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx R (Z_to_bv 64 0x6a2d4) M rom) model) K.
  Proof.
    intros LB LK cr A M model R S canz K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 WIN IMG CAN ARG SO KONT.
    pose proof Hsp as Hsp'. destruct SO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & FW & BW & BC).
    assert (PC : forall a n v, In (a, n, v) PR_CELLS -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hin; exact (pr_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hpr M0 _ _ _ _ _ _ a n v D Hin)).
    assert (P1 : forall a v, In (a, 1, v) PR_CELLS -> 0 <= v < 2 ^ 64 -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros a v Hin Hv. rewrite <- (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem.art_bytes1 v Hv). exact (PC a 1 v Hin). }
    set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
    destruct (AS0DRVP_dpA3.dpA3_conc fx R MV V) as (fx' & R' & MV' & GR & _ & FRZ & MS & KS & _ & Q10 & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & O4).
    all: cbn [V].
    all: try assumption.
    all: try (clear - Hsp' HS1 HS2 Hcan; lia).
    - (* [comment removed for export] *) intros d k Hd Hk. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *) intros i Hi. apply (store_ok_defined sp0); [lia|]. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *)
      intros i Hi. apply (stk_sh0 scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ _ D).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      clear - Hsp' Hal HS1 HS2 HS16 Hi. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x15180 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - (* [comment removed for export] *)
      apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x6b4300 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - intros d k Hd Hk. apply (FW 1422992 4); lia.
    - intros d k Hd Hk. apply (FW 1423032 8); lia.
    - intros d k Hd Hk. apply (BW 7029538 1); unfold SOBUF; lia.
    - intros d k Hd Hk. apply (BW 7029539 1); unfold SOBUF; lia.
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PC 0x15fa78 8 0x7fff8000 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x158c20 8 0x146850 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x158c28 8 0x14056c ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PC 0x158da0 8 0x148d68 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x158da8 8 0x14916c ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - (* [comment removed for export] *)
      unfold V in FRZ, MS; cbn beta iota in FRZ, MS.
      assert (FRW : forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 1 a -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
      { intros a Ha Hn. apply FRZ; [exact Ha | | | | |]; intros X; apply Hn; unfold Wpf, SOBUF; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx' R (Z_to_bv 64 0x6a2d4) R' (Z_to_bv 64 0xaeec0) MV' (Wpf S 1) K D MS GR FRW).
      + intros a [Ha|[Ha|[Ha|Ha]]]; unfold CWA; [right; left; lia | | |]; right; right.
        * exists 0x15b5a0, 0x15b8a0. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        * exists 0x15b5a0, 0x15b8a0. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        * exists 0x693b30, 0x6b4fb8. split; [unfold IMG_W_A; cbn [In]; tauto | unfold SOBUF in Ha; lia].
      + intros M1 model1 D1 SBM VIS FR1. apply (KONT fx' R' M1 model1 D1 SBM KS Q10); [|exact FR1 | rewrite VIS; exact FRW | rewrite VIS; exact GR].
        rewrite VIS. unfold stdoutA.
        assert (TR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
                     (forall i, a <= i < a + Z.of_nat n -> ~ Wpf S 1 i) -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Hr Ha Hn Ho. apply (rdn_tr MV MV' a n bs Hr Ha Hn). intros i Hi. apply FRW; [lia | exact (Ho i Hi)]. }
        split; [exact O1|]. split; [apply TR; [exact F2 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F3 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [exact O2|].
        split; [apply TR; [exact F5 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F6 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F7 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (FW a n); assumption|].
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (BW a n); assumption|].
        intros i Hi. destruct (Z.eq_dec i 1) as [->|N]; [split; [exact O4 | exact O3]|].
        destruct (BC i ltac:(lia)) as (B1 & B2).
        split; (apply TR; [assumption | unfold SOBUF; lia | unfold SOBUF; cbn; lia | intros x Hx; unfold Wpf, SOBUF in *; cbn in Hx; lia]).
  Qed.

  Lemma printf4_run : forall LB LK cr A M (model : Model) R (S canz : Z) K,
    dinvA LB LK cr A M model ->
    let MV := mrestrict (ahid A model) M in
    usp - 4096 <= S -> S + 32 <= usp -> S mod 16 = 0 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 716480 -> getr R 2%bv = Z_to_bv 64 S -> getr R 10%bv = Z_to_bv 64 86406 -> getr R 11%bv = Z_to_bv 64 (S + 24) ->
    (forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true) ->
    (forall i, 65536 <= i < 1409024 -> MV (Z_to_bv 64 i) = None) ->
    rdn ASEGS MV (Z_to_bv 64 7027520) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    rdn ASEGS MV (Z_to_bv 64 (S + 24)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    stdoutA 2 MV ->
    (forall (fx' : PropExec.FPState) R' M1 (model1 : Model),
        dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
        (forall x, In x AS0DRVP_dpA4.KS_dpA4 -> getr R' (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))) ->
        getr R' 10%bv = Z_to_bv 64 2 ->
        stdoutA 3 (mrestrict (ahid A model1) M1) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 2 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 2 a -> mrestrict (ahid A model1) M1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
        (forall a : word, MV a <> None -> mrestrict (ahid A model1) M1 a <> None) ->
        srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xaeec0) M1 rom) model1) K) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx R (Z_to_bv 64 0x6a2d4) M rom) model) K.
  Proof.
    intros LB LK cr A M model R S canz K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 WIN IMG CAN ARG SO KONT.
    pose proof Hsp as Hsp'. destruct SO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & FW & BW & BC).
    assert (PC : forall a n v, In (a, n, v) PR_CELLS -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hin; exact (pr_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hpr M0 _ _ _ _ _ _ a n v D Hin)).
    assert (P1 : forall a v, In (a, 1, v) PR_CELLS -> 0 <= v < 2 ^ 64 -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros a v Hin Hv. rewrite <- (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem.art_bytes1 v Hv). exact (PC a 1 v Hin). }
    set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
    destruct (AS0DRVP_dpA4.dpA4_conc fx R MV V) as (fx' & R' & MV' & GR & _ & FRZ & MS & KS & _ & Q10 & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & O4).
    all: cbn [V].
    all: try assumption.
    all: try (clear - Hsp' HS1 HS2 Hcan; lia).
    - (* [comment removed for export] *) intros d k Hd Hk. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *) intros i Hi. apply (store_ok_defined sp0); [lia|]. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *)
      intros i Hi. apply (stk_sh0 scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ _ D).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      clear - Hsp' Hal HS1 HS2 HS16 Hi. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x15180 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - (* [comment removed for export] *)
      apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x6b4300 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - intros d k Hd Hk. apply (FW 1422992 4); lia.
    - intros d k Hd Hk. apply (FW 1423032 8); lia.
    - intros d k Hd Hk. apply (BW 7029540 1); unfold SOBUF; lia.
    - intros d k Hd Hk. apply (BW 7029541 1); unfold SOBUF; lia.
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PC 0x15fa78 8 0x7fff8000 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x158c20 8 0x146850 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x158c28 8 0x14056c ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PC 0x158da0 8 0x148d68 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x158da8 8 0x14916c ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - (* [comment removed for export] *)
      unfold V in FRZ, MS; cbn beta iota in FRZ, MS.
      assert (FRW : forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 2 a -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
      { intros a Ha Hn. apply FRZ; [exact Ha | | | | |]; intros X; apply Hn; unfold Wpf, SOBUF; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx' R (Z_to_bv 64 0x6a2d4) R' (Z_to_bv 64 0xaeec0) MV' (Wpf S 2) K D MS GR FRW).
      + intros a [Ha|[Ha|[Ha|Ha]]]; unfold CWA; [right; left; lia | | |]; right; right.
        * exists 0x15b5a0, 0x15b8a0. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        * exists 0x15b5a0, 0x15b8a0. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        * exists 0x693b30, 0x6b4fb8. split; [unfold IMG_W_A; cbn [In]; tauto | unfold SOBUF in Ha; lia].
      + intros M1 model1 D1 SBM VIS FR1. apply (KONT fx' R' M1 model1 D1 SBM KS Q10); [|exact FR1 | rewrite VIS; exact FRW | rewrite VIS; exact GR].
        rewrite VIS. unfold stdoutA.
        assert (TR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
                     (forall i, a <= i < a + Z.of_nat n -> ~ Wpf S 2 i) -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Hr Ha Hn Ho. apply (rdn_tr MV MV' a n bs Hr Ha Hn). intros i Hi. apply FRW; [lia | exact (Ho i Hi)]. }
        split; [exact O1|]. split; [apply TR; [exact F2 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F3 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [exact O2|].
        split; [apply TR; [exact F5 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F6 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F7 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (FW a n); assumption|].
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (BW a n); assumption|].
        intros i Hi. destruct (Z.eq_dec i 2) as [->|N]; [split; [exact O4 | exact O3]|].
        destruct (BC i ltac:(lia)) as (B1 & B2).
        split; (apply TR; [assumption | unfold SOBUF; lia | unfold SOBUF; cbn; lia | intros x Hx; unfold Wpf, SOBUF in *; cbn in Hx; lia]).
  Qed.

End PrintfK.
End FPX_1.
End NraDrvPrintfK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.
Module NraDrvPrintf1.
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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.ShapeLaws OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvPiece OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DiagLoopK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvStdio OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0248.NraDrvPrintfK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232.Na0DrvP_dpA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232.Na0DrvP_dpB_notty OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0232.Na0DrvP_dpCd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_NraDrvPrintf1 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4list00C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib7Mh_0119;Na0DrvStdio6rdn_trC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic8f_equal2C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01I47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC59OSSVerify5KrLib7Mh_01059SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2or00C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib6di_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib=nolazy_of_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK:nolazy_rngC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K47Corelib4Init5Logic2or01K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic2or02C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00". Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition stdout0A (MV : word -> option byte) : Prop :=
  rdn ASEGS MV (Z_to_bv 64 1423132) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))             (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1422992) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5))                    (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423088) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024))                 (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423024) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))                    (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423128) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))                    (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423080) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SOBUF))                (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423136) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 10))                   (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423064) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1311504))               (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423112) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))                    (* [comment removed for export] *)
  /\ (forall a n, 1422992 <= a -> a + n <= 1422992 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
  /\ (forall a n, SOBUF <= a -> a + n <= SOBUF + 1024 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true).

(* [comment removed for export] *)
Definition stdoutXA (MV : word -> option byte) : Prop :=
  rdn ASEGS MV (Z_to_bv 64 1423064) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1308196))                  (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423112) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))                    (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423080) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SOBUF))                (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423000) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))                    (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1423008) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition Wpf1 (S a : Z) : Prop := S - 3232 <= a < S \/ 1422992 <= a < 1422992 + 232 \/ SOBUF <= a < SOBUF + 1024.

(* [comment removed for export] *)
Lemma TRf : forall (MVa MVb : word -> option byte) (W : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> MVb (Z_to_bv 64 a) = MVa (Z_to_bv 64 a)) ->
  forall a (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> ~ W i) -> rdn ASEGS MVb (Z_to_bv 64 a) n = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_NraDrvPrintf1 ()) [] "h02Hah14__x1h24__x2h34__x3h41ah51ih62FRh72Hih82Hnh92Hoh:2Hrh;3MVah<3MVbh=1Wh>7__arithh?4__ffh@6__sat0hA6__sat1hB8__varmaphC5__withD2bshE4cstrhF1np;1p;2p;3p;4p;9p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9P0p1001fp4p710p9p1002^p4p70p1003Np4p710p8p1003lp4p70p1004Zp4p7210p8g0056j13Tg005[j1JTg0069j1BTg006\j1@Tg007>j1ITg007\j2UTg0089j20Tg008Uj28Tg0090j1ATg009Ij2MTg009oj3<Tg00:Ij1DTg00:ij4bTg00;Zj2_Tg00<<j17Tg00<\j25Tg00=9j21Tg00=Uj1VTg00>:j2TTg00>bj3STg00?Fj1;Tg00?ej26Tg00@Nj3:Tg00A7j2CTg00Acj1RTg00BCj3GTg00Bcj2HTg00CAj4QTg00C_j1PTg00D=j1NTg00Dhj2=Tg00EKj1LTg00F0j3OTg00FSj4>Tg00G>j1KTg00G`j2FTg00HCj3aTg00Hfj2`Tg00IHj2^Tg00Ibj2]Tg00JNj3\Tg00Jmj4YTg00K_l9ZTg00L^j7[Tg00MBj7XTg00Mfj8WTg00NJR0f0R1'1p=2g00NhR2f1R3g00OFP1C>p=9P3g00OmR4g00PLR5P5g00PlR6P1g00QLF[p=4f2R7P4P5P5P6P3P1FXp=Ef3R8P4P5P5P6P7P3P1GWp=?g00QlR4#3R9#3#3R:#3#3#3R;#JR<#B%J:#BR:#@R=[R>p-0\2%21%I9R?%I;R;'UR@,01'8P7P3O1#Af4RA1M<7RBO1f5RCPBO15<=[[^42g00RQ%D:R:%@:g00S0f6R=PBP3Cb1_:13<%28R:%78,5A/1@11=1%7C,5=,01'8f9RBP3O1#A[^52f:PBP=PCPAP8P7P3f7RD/11%7=,5D,01'8PBP3%VD%7D#21T?;100?%2;100@[[%2?RBg00TER=AS?;3UW0%2@\=^0Bg00TaRBg00UMR=#;R;#;RE#;RF,62162E162=R=5:25:2g00UlRE'C%;F,62162;=:2=5:2/CE%RB5GB3G%DBP21H27P31H28CQ%P2%N2RB1=29R91=24RE'9,4BP2PEg00VXR=%L4,=29O29R4C>,4B5EB%K5R5PB1F2?=a2<R<,94,4BP5PB1F20R4/99,4BP5194E,4BP2PEP=P<C>,4B5EBC?C?C?1`B6P1P7g00W?RBg00W_R6'^1]17=<B6dA\203CYb?bBbCX12X22X3211311537,01'81578/1@108@,8:\:[[^12^22^32P1f;#7f<PCPAPDf8O6b>b@bAbEP7P3P1O2O3W7X52M9ZW9W8W0W:WDWFX42W6W=X<>W;o"). Qed.

Lemma le4_m1 : word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615) = word_to_le_bytes 4 (Z_to_bv 64 4294967295).
Proof.
ltac2:(KReplay.run1 (kr_t_NraDrvPrintf1 ()) [] "h01Hh12b1h22b2h31np;1p;3p;2p;:p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9P0p1001fp4p710p9p1002^p4p70p1003Np4p710p8p1003lp4p70p1004Zp4p7210p8g0056j18Tg005[j1>Tg0069j16Tg00:Ij1@Tg00BCj1Ej37Tg00EKj14Tg007>j12Tg00Acj1?Tg009oj35Tg00X?j23Tg00Xij3DTg00IHj29Tg00YMl::Tg00?Fj1;Tg009Ij2=Tg00Ykj2<Tg00[3j2BTg00[fj3ATf0R0#4#4p=C%40#4#4#4p=0f3R1f2R2f1R3/B03Ap=1g00QlR4#8#8#8R5#>R6#6R7%@7R8P8%E7R9P6%44#C#0R4#2R:P6%04#0R4#0#0R;#0#0R<#0#0R=#0#0R>#0#0R?#0#0#2R@C1RAP6P:P6%2<R<C1RBP6P:P6%2?C1R?P6P:P6%2>C1R>P6P:P6%2=C1R=%?7RC577RD577RE577P6P:P6%2;C1R;P6P:P6%24C1R4P6P:P6P:C1R:=77CRF577RG577g00\IRH%60RI%63RJg008U%62?530g00NhRK1312131335RL[1323132055K%61?523[RMf4#6?512\LAD230P0n2001000000120000000W2W1W3R3PM^2J^1I^3HRHP0P6PAPB136B,9KO4b0P7P8P8P9P?P;PEPGP3PHP0P6P?P;136;,9KO4b0P7P8P8P9P>P4PDPFP3PHP0P6P>P41364,9KO4b0P7P8P8P9P=P:PCPCP3PHP0P6P=P:136:,9KO4b0198CM::M::M::M::g00UM#;#;#;#;RC%85#8#8#>R5/=@'<1=5<,<C558do"). Qed.
Lemma nl_imgA : rdn ASEGS (fun _ => None) (Z_to_bv 64 86408) 1 = Some [Z_to_bv 8 10].
Proof.
ltac2:(KReplay.run1 (kr_t_NraDrvPrintf1 ()) [] "p;1p;2p;3p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9P0p1001fp4p710p9p1002^p4p70p1003Np4p710p8p1003lp4p70p1004Zp4p7210p8g0056j10Tg005[j16Tg0069j13Tg00:Ij1BTg006\j1<Tg00EKj11Tg007>j14Tg00[3j2;Tg00[fj3:Tg00Acj19Tg00BCj35Tg00;Zj27Tg00IHj2ATg00G>j1@Tg009Ij28Tg00?Fj1=Tg00:ij4>Tg009oj3?Tf0#0#0p=2g00Ql#0R0#2R1#6R2#3R3#BR4#<R5%10#0R0#4R61;265:2%93R7553,74'Ag00S0%01#2#6R1#3%@3U%10#0#2#1#1#0#2#1#0#2#4,81g00UM#=C>1826=537,745?5do"). Qed.
Lemma fetch_ioctlA : fetch_word ASEGS (Z_to_bv 64 0x14036c) = Some ECALLW.
Proof.
ltac2:(KReplay.run1 (kr_t_NraDrvPrintf1 ()) [] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9P0p1001fp4p710p9p1002^p4p70p1003Np4p710p8p1003lp4p70p1004Zp4p7210p8g0056j12Tg005[j14Tg0069j16Tg006\j1=Tg00EKj10Tg007>j15Tg00[3j2;Tg00[fj3:Tg00;Zj23Tg00IHj27Tg009Ij28Tg00\gj29Tg009oj3<Tf0#2#2p=1g00QlR0#2#1#1R1#4R2#6R3#=R4%00#0#1#0#0#5R51;255:2,33'7g00S0%21#4%20#0#1#1#1#1#0#0#2#0#0#2#0#0#1#5'8'9g00]i,335<4do"). Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Printf1.
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
  Hypothesis Hpr : incl PR_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation rom := (seg_rom ASEGS).

  (* [comment removed for export] *)
  #[using="scfg L C IL HIok Hsp DL"] Lemma nl_pt : forall LB LK cr A M (model : Model) x, dinvA LB LK cr A M model -> 0 <= x < 2 ^ 64 -> (x < 0x6b6000 \/ usp - 8388608 <= x) ->
    page_in_ranges (page_base_of x) (m_vm_lazy model) = false.
  Proof.
    intros LB LK cr A M model x D Hx Hc.
    assert (U : bv_unsigned (Z_to_bv 64 x) = x) by (apply u64_lit; lia).
    pose proof (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ model (Z_to_bv 64 x) 1 (di_inv _ _ _ _ _ _ _ _ _ _ D) ltac:(rewrite U; lia)) as X.
    assert (Y : forall k, 0 <= k < 1 -> bv_unsigned (Z_to_bv 64 x) + k < 7036928 \/ usp - 8388608 <= bv_unsigned (Z_to_bv 64 x) + k \/ in_block LB (bv_unsigned (Z_to_bv 64 x) + k))
      by (intros k Hk; rewrite U; destruct Hc; [left | right; left]; lia).
    specialize (X Y 0 ltac:(lia)). rewrite U, Z.add_0_r in X. exact X.
  Qed.

  Lemma printf1_run : forall LB LK cr A M (model : Model) R (S canz : Z) K,
    dinvA LB LK cr A M model ->
    let MV := mrestrict (ahid A model) M in
    usp - 4096 <= S -> S + 32 <= usp -> S mod 16 = 0 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 716480 -> getr R 2%bv = Z_to_bv 64 S -> getr R 10%bv = Z_to_bv 64 86406 -> getr R 11%bv = Z_to_bv 64 (S + 24) ->
    (forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true) ->
    (forall i, 65536 <= i < 1409024 -> MV (Z_to_bv 64 i) = None) ->
    rdn ASEGS MV (Z_to_bv 64 7027520) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    rdn ASEGS MV (Z_to_bv 64 (S + 24)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    stdout0A MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    K [] ->
    (forall (fx' : PropExec.FPState) R' M1 (model1 : Model),
        dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
        (forall r, In r c_kept -> getr R' r = getr R r) ->
        getr R' 10%bv = Z_to_bv 64 2 ->
        stdoutA 0 (mrestrict (ahid A model1) M1) -> stdoutXA (mrestrict (ahid A model1) M1) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf1 S a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf1 S a -> mrestrict (ahid A model1) M1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
        (forall a : word, MV a <> None -> mrestrict (ahid A model1) M1 a <> None) ->
        srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xaeec0) M1 rom) model1) K) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx R (Z_to_bv 64 0x6a2d4) M rom) model) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
  Proof.
    intros LB LK cr A M model R S canz K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 WIN IMG CAN ARG SO FD1 HK0 KONT.
    pose proof Hsp as Hsp'. destruct SO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FW & BW).
    assert (PCg : forall LK' cr' A' M' (model' : Model), dinvA LB LK' cr' A' M' model' -> forall a n v, In (a, n, v) PR_CELLS ->
                  rdn ASEGS (mrestrict (ahid A' model') M') (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros LK' cr' A' M' model' D' a n v Hin; exact (pr_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hpr M0 _ _ _ _ _ _ a n v D' Hin)).
    assert (P1g : forall LK' cr' A' M' (model' : Model), dinvA LB LK' cr' A' M' model' -> forall a v, In (a, 1, v) PR_CELLS -> 0 <= v < 2 ^ 64 ->
                  rdn ASEGS (mrestrict (ahid A' model') M') (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros LK' cr' A' M' model' D' a v Hin Hv. rewrite <- (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem.art_bytes1 v Hv). exact (PCg _ _ _ _ _ D' a 1 v Hin). }
    (* [comment removed for export] *)
    set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
    destruct (AS0DRVP_dpA.dpA_conc fx R MV V) as
(fx1 & R1' & MV1 & AGR & _ & AFRZ & AMS & AKS & Ar1 & Ar2 & Ar5 & Ar8 & Ar9 & Ar10 & Ar11 & Ar12 & Ar13 & Ar14 & Ar15 & Ar16 & Ar17 & Ar18 & Ar19 & Ar20 & Ar21 & Ar22 & Ar23 & Ar24 & Ar25 & Ar26 & Ar27 & Aa892264 & Am1096 & Am1088 & Am1080 & Am1064 & Am1056 & Am1048 & Am1040 & Am1032 & Am1024 & Am1016 & Aa892232 & Am1104 & Aa6361368 & Am832 & Am1072 & Am1000 & Am976 & Am992 & Am1008 & Am984 & Am896 & Am464 & Am968 & Am960 & Am904 & Am928 & Am576 & Am912 & Am920 & Am936 & Am952 & Am944 & Am568 & Am560 & Am552 & Am544 & Am536 & Am528 & Am520 & Am512 & Am504 & Am496 & Am488 & Am480 & Am472 & Aa892224 & Aa892208 & Aa892200 & Aa892248 & Aa892328 & Aa892192 & Am176 & Am184 & Am192 & Am200 & Am168 & Am456 & Am160 & Am152 & Am144 & Am136 & Am128 & Am120 & Am112 & Am104 & Am96 & Am88 & Am80 & Am72 & Am64 & Am56 & Am40 & Am32 & Am24 & Am16 & Am8 & Ad1 & Ad2 & Ad3 & Ad4).
    all: cbn [V].
    all: try assumption.
    all: try (clear - Hsp' HS1 HS2 Hcan; lia).
    - (* [comment removed for export] *) intros d k Hd Hk. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *) intros i Hi. apply (store_ok_defined sp0); [lia|]. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *)
      intros i Hi. apply (stk_sh0 scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ _ D).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      clear - Hsp' Hal HS1 HS2 HS16 Hi. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x15180 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - (* [comment removed for export] *)
      apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x6b4300 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - intros d k Hd Hk. apply (FW 1422992 4); lia.
    - intros d k Hd Hk. apply (FW 1423000 8); lia.
    - intros d k Hd Hk. apply (FW 1423008 8); lia.
    - intros d k Hd Hk. apply (FW 1423024 8); lia.
    - intros d k Hd Hk. apply (FW 1423032 8); lia.
    - intros d k Hd Hk. apply (FW 1423048 8); lia.
    - intros d k Hd Hk. apply (FW 1423064 8); lia.
    - intros d k Hd Hk. apply (FW 1423128 4); lia.
    - intros d k Hd Hk. apply (BW 7029536 1); unfold SOBUF; lia.
    - apply (P1g _ _ _ _ _ D); [unfold PR_CELLS; cbn [In]; tauto | lia].
    - apply (P1g _ _ _ _ _ D); [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PCg _ _ _ _ _ D 0x15fa78 8 0x7fff8000 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PCg _ _ _ _ _ D 0x158c20 8 0x146850 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PCg _ _ _ _ _ D 0x158c28 8 0x14056c ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - apply (P1g _ _ _ _ _ D); [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PCg _ _ _ _ _ D 0x158da0 8 0x148d68 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PCg _ _ _ _ _ D 0x158da8 8 0x14916c ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - (* [comment removed for export] *)
      unfold V in AFRZ, AMS; cbn beta iota in AFRZ, AMS. cbn [V] in *.
      set (WA := fun a : Z => S - 3232 <= a < S \/ 1422992 <= a < 1422996 \/ 1423000 <= a < 1423016 \/ 1423024 <= a < 1423040 \/ 1423048 <= a < 1423056 \/ 1423064 <= a < 1423072 \/ 1423128 <= a < 1423132 \/ a = 7029536).
      assert (FRA : forall a, 0 <= a < 2 ^ 64 -> ~ WA a -> MV1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
      { intros a Ha Hn. apply AFRZ; [exact Ha | | | | | | | | | |]; intros X; apply Hn; unfold WA; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx1 R (Z_to_bv 64 0x6a2d4) R1' (Z_to_bv 64 0x14036c) MV1 WA _ D AMS AGR FRA).
      { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
        destruct (Z.eq_dec a 7029536) as [->|Ne].
        - exists 0x693b30, 0x6b4fb8. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        - exists 0x15b5a0, 0x15b8a0. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha Ne; lia]. }
      intros M1 model1 D1 SBM1 VIS1 FRM1.
      subst MV1.
      set (MVa := mrestrict (ahid A model1) M1) in *.
      (* [comment removed for export] *)
      assert (WIN1 : forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVa (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MVa _ AGR); apply (WIN a n); assumption).
      assert (FW1 : forall a n, 1422992 <= a -> a + n <= 1422992 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVa (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MVa _ AGR); apply (FW a n); assumption).
      assert (BW1 : forall a n, SOBUF <= a -> a + n <= SOBUF + 1024 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVa (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MVa _ AGR); apply (BW a n); assumption).
      assert (IMG1 : forall i, 65536 <= i < 1409024 -> MVa (Z_to_bv 64 i) = None).
      { intros i Hi. rewrite FRA; [apply IMG; exact Hi | lia | unfold WA; clear - Hsp' HS1 HS2 Hi; lia]. }
      assert (CAN1 : rdn ASEGS MVa (Z_to_bv 64 7027520) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz))).
      { apply (TRf _ _ _ FRA _ _ _ CAN); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (F1a : rdn ASEGS MVa (Z_to_bv 64 1423132) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))).
      { apply (TRf _ _ _ FRA _ _ _ F1); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (F3a : rdn ASEGS MVa (Z_to_bv 64 1423088) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024))).
      { apply (TRf _ _ _ FRA _ _ _ F3); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (F6a : rdn ASEGS MVa (Z_to_bv 64 1423080) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SOBUF))).
      { apply (TRf _ _ _ FRA _ _ _ F6); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (F9a : rdn ASEGS MVa (Z_to_bv 64 1423112) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
      { apply (TRf _ _ _ FRA _ _ _ F9); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (FD1a : fd_lookup (m_fds model1) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite (sbm_fds' _ _ SBM1); exact FD1).
      (* [comment removed for export] *)
      eapply (rz_ioctl_winsz_lz ASEGS scfg R1' _ M1 model1 ECALLW (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)));
        [exact fetch_ioctlA | apply is_ecall_ECALLW | exact (di_halt _ _ _ _ _ _ _ _ _ _ D1) | exact Ar17 | exact Ar10 | rewrite u64_lit by lia; lia
        | exact FD1a | reflexivity | exact Ar11 |].
      rewrite v_addi_pc4 by lia. change (0x14036c + 4) with 0x140370.
      set (R1b := regupd R1' 10%bv (errno_ret ENOTTY)).
      assert (RBo : forall r : reg, r <> 10%bv -> getr R1b r = getr R1' r) by (intros r Hr; unfold R1b; apply getr_other; exact Hr).
      assert (RB10 : getr R1b 10%bv = Z_to_bv 64 18446744073709551591).
      { unfold R1b. rewrite getr_same by (intros X; discriminate X). rewrite errno_ret_lit. apply bv_eq. reflexivity. }
      (* [comment removed for export] *)
      set (VB := fun n : nat => match n with 2%nat => S - 1104 | 40%nat => canz | _ => 0 end).
      assert (Bg2 : getr R1b (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (S - 1104)) by (rewrite RBo by (intros X; discriminate X); exact Ar2).
      assert (Bg8 : getr R1b (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 7027520) by (rewrite RBo by (intros X; discriminate X); exact Ar8).
      assert (Bg9 : getr R1b (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1) by (rewrite RBo by (intros X; discriminate X); exact Ar9).
      assert (Bg13 : getr R1b (Z_to_bv 5 (Z.of_nat 13)) = Z_to_bv 64 86408) by (rewrite RBo by (intros X; discriminate X); exact Ar13).
      assert (Bg15 : getr R1b (Z_to_bv 5 (Z.of_nat 15)) = Z_to_bv 64 1) by (rewrite RBo by (intros X; discriminate X); exact Ar15).
      assert (Bg16 : getr R1b (Z_to_bv 5 (Z.of_nat 16)) = Z_to_bv 64 1422992) by (rewrite RBo by (intros X; discriminate X); exact Ar16).
      assert (Bg18 : getr R1b (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 86408) by (rewrite RBo by (intros X; discriminate X); exact Ar18).
      assert (Bg19 : getr R1b (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 1) by (rewrite RBo by (intros X; discriminate X); exact Ar19).
      assert (Bg20 : getr R1b (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 0) by (rewrite RBo by (intros X; discriminate X); exact Ar20).
      assert (Bg21 : getr R1b (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 86409) by (rewrite RBo by (intros X; discriminate X); exact Ar21).
      assert (Bg22 : getr R1b (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 1) by (rewrite RBo by (intros X; discriminate X); exact Ar22).
      destruct (AS0DRVP_dpB_notty.dpB_notty_conc fx1 R1b MVa VB ltac:(cbn [VB]; clear - Hsp' HS1 HS2; lia) Hcan Bg2 Bg8 Bg9 RB10 Bg13 Bg15 Bg16 Bg18 Bg19 Bg20 Bg21 Bg22
                  ltac:(cbn [VB]; clear - Hsp' HS1 HS2; lia)) as
(fx2 & R2' & MV2 & BGR & _ & BFRZ & BMS & BKS & Br1 & Br2 & Br8 & Br9 & Br10 & Br11 & Br12 & Br13 & Br17 & Br18 & Br19 & Br21 & Br22 & Bm80 & Bm88 & Bm96 & Bm104 & Bm72 & Bm64 & Bm56 & Bm48 & Bm40 & Bm32 & Bm24 & Bm16 & Bm8 & Ba892336 & Bd1).
      all: cbn [VB].
      { unfold AS0DRVP_dpB_notty.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      { intros d k Hd Hk. apply (WIN1 (S - 1104 - 112) 112); clear - Hsp' HS1 HS2 Hd Hk; lia. }
      { intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN1 (S - 1104 - 112) 112); clear - Hsp' HS1 HS2 Hi; lia. }
      { exact IMG1. }
      { intros d k Hd Hk. apply (FW1 1423136 4); lia. }
      { exact CAN1. }
      { exact Aa892232. }
      { exact Aa892248. }
      { exact F9a. }
      unfold VB in BFRZ, BMS; cbn beta iota in BFRZ, BMS. cbn [VB] in *.
      set (WB := fun a : Z => S - 1216 <= a < S - 1104 \/ 1423136 <= a < 1423140).
      assert (FRB : forall a, 0 <= a < 2 ^ 64 -> ~ WB a -> MV2 (Z_to_bv 64 a) = MVa (Z_to_bv 64 a)).
      { intros a Ha Hn. apply BFRZ; [exact Ha | |]; intros X; apply Hn; unfold WB; clear - X; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M1 model1 fx1 fx2 R1b (Z_to_bv 64 0x140370) R2' (Z_to_bv 64 0x13f6ac) MV2 WB _ D1 BMS BGR FRB).
      { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
        exists 0x15b5a0, 0x15b8a0. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha; lia]. }
      intros M2 model2 D2 SBM2 VIS2 FRM2.
      subst MV2. set (MVb := mrestrict (ahid A model2) M2) in *.
      (* [comment removed for export] *)
      assert (WIN2 : forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVb (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVa MVb _ BGR); apply (WIN1 a n); assumption).
      assert (IMG2 : forall i, 65536 <= i < 1409024 -> MVb (Z_to_bv 64 i) = None).
      { intros i Hi. rewrite FRB; [apply IMG1; exact Hi | lia | unfold WB; clear - Hsp' HS1 HS2 Hi; lia]. }
      assert (F9b : rdn ASEGS MVb (Z_to_bv 64 1423112) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
      { apply (TRf _ _ _ FRB _ _ _ F9a); [lia | cbn; lia | intros i Hi X; unfold WB in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (DATA1 : rdn ASEGS MVb (Z_to_bv 64 7029536) 1 = Some [Z_to_bv 8 48]).
      { apply (TRf _ _ _ FRB _ _ _ Aa6361368); [lia | cbn; lia | intros i Hi X; unfold WB in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (DATA2 : rdn ASEGS MVb (Z_to_bv 64 86408) 1 = Some [Z_to_bv 8 10]).
      { apply (img_cell MVb 86408 1 _ nl_imgA); [lia | cbn; lia | intros i Hi; apply IMG2; cbn in Hi; lia]. }
      assert (FD1b : fd_lookup (m_fds model2) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite (sbm_fds' _ _ SBM2); exact FD1a).
      (* [comment removed for export] *)
      pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D2) as (HH2 & HL2 & HA2 & HM2 & Hh2).
      set (q := S - 1104 - 104) in *.
      assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
      assert (Hf : 0 <= 1422992 /\ (1422992 + 124 <= q \/ q + 32 + 16 <= 1422992 + 120) /\ 1422992 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
      assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model2) = false).
      { intros x Hx. apply (nl_pt _ _ _ _ _ _ x D2); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
      unfold W. change (map (WriteEv (Z_to_bv 64 1)) [Z_to_bv 8 48; Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 1)) ([Z_to_bv 8 48] ++ [Z_to_bv 8 10])).
      apply (wv_loop scfg (ahid A model2) A HH2 (m_vm_lazy model2) HL2 HA2 1422992 1 ltac:(lia) q (q + 32) Hq Hf NLq K HK0 2%nat true R2' M2 model2 q 2 7029536 1 86408 1 [Z_to_bv 8 48] [Z_to_bv 8 10]).
      { cbn. lia. }
      { reflexivity. }
      { exact HM2. }
      { exact Hh2. }
      { exact FD1b. }
      { exact (di_rdr _ _ _ _ _ _ _ _ _ _ D2). }
      { unfold wv_regs. repeat split; try assumption. }
      { fold MVb. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
        split; [exact Bm104|]. split; [replace (q + 8) with (S - 1104 - 96) by (unfold q; ring); exact Bm96|].
        split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN2 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
        split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA1|];
                intros x Hx; apply (nl_pt _ _ _ _ _ _ x D2); lia|].
        split; [intros X; discriminate X|]. intros _.
        split; [replace (q + 16) with (S - 1104 - 88) by (unfold q; ring); exact Bm88|].
        split; [replace (q + 24) with (S - 1104 - 80) by (unfold q; ring); exact Bm80|].
        split; [|lia].
        unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA2|].
        intros x Hx; apply (nl_pt _ _ _ _ _ _ x D2); lia. }
      { lia. }
      { exact F9b. }
      (* [comment removed for export] *)
      intros R3 M3 model3 MI3 SBM3 KR3 FRM3 FRV3 GRM3 GRV3.
      assert (D3 : dinvA LB LK cr A M3 model3).
      { apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M2 M3 model2 model3 D2).
        - intros a Ha Hn. apply FRM3; [exact Ha|]. intros X. apply Hn. unfold CWA. right; left. unfold q in X. clear - Hsp' HS1 HS2 X. lia.
        - exact GRM3.
        - exact (sbm_vml _ _ SBM3).
        - exact MI3.
        - rewrite (sbm_halted_eq _ _ SBM3). exact Hh2.
        - exact (sbm_rdrA _ _ SBM3). }
      pose proof (ahid_sbm A model2 model3 SBM3) as AH3.
      set (MVc := mrestrict (ahid A model3) M3) in *.
      assert (EQc : mrestrict (ahid A model2) M3 = MVc) by (unfold MVc; rewrite AH3; reflexivity).
      rewrite EQc in FRV3, GRV3. fold MVb in FRV3, GRV3.
      set (SC := S - 1104 - 112) in *.
      assert (FRca : forall i, 0 <= i < 2 ^ 64 -> ~ (SC <= i < S - 1104) -> ~ (1423136 <= i < 1423140) -> MVc (Z_to_bv 64 i) = MVa (Z_to_bv 64 i)).
      { intros i Hi N1 N2. rewrite FRV3 by (unfold q, SC in *; clear - Hi N1; lia). apply FRB; [exact Hi | unfold WB, SC in *; clear - N1 N2; lia]. }
      assert (cellA : forall off k (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 (S - k)) n = Some bs ->
                (off + k =? 1216) && (Z.of_nat n <=? k) && (k <=? 1104) = true -> rdn ASEGS MVc (Z_to_bv 64 (SC + off)) n = Some bs).
      { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
        apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (SC + off) with (S - k) by (unfold SC; lia).
        apply (rdn_tr MVa MVc _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
        intros i Hi. apply FRca; unfold SC; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
      assert (cellB : forall off k (n : nat) bs, rdn ASEGS MVb (Z_to_bv 64 (S - 1104 - k)) n = Some bs ->
                (off + k =? 112) && (Z.of_nat n <=? k) && (k <=? 72) = true -> rdn ASEGS MVc (Z_to_bv 64 (SC + off)) n = Some bs).
      { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
        apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (SC + off) with (S - 1104 - k) by (unfold SC; lia).
        apply (rdn_tr MVb MVc _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
        intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
      assert (cellL : forall a (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 a) n = Some bs ->
                (0 <=? a) && (a + Z.of_nat n <=? 10000000) && ((a + Z.of_nat n <=? 1423136) || (1423140 <=? a)) = true -> rdn ASEGS MVc (Z_to_bv 64 a) n = Some bs).
      { intros a n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
        apply Z.leb_le in Hb1, Hb2. apply orb_prop in Hb3. rewrite !Z.leb_le in Hb3.
        apply (rdn_tr MVa MVc _ _ _ Hr); [exact Hb1 | lia|].
        intros i Hi. apply FRca; unfold SC; clear - Hsp' HS1 HS2 Hb1 Hb2 Hb3 Hi; lia. }
      assert (WIN3 : forall a n, usp - 6144513 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVc (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVb MVc _ GRV3); apply (WIN2 a n); assumption).
      assert (FW3 : forall a n, 1422992 <= a -> a + n <= 1422992 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVc (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVb MVc _ GRV3); apply (store_ok_mono ASEGS k MVa MVb _ BGR); apply (FW1 a n); assumption).
      assert (IMG3 : forall i, 65536 <= i < 1409024 -> MVc (Z_to_bv 64 i) = None).
      { intros i Hi. rewrite FRV3; [apply IMG2; exact Hi | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
      assert (ST910489 : rdn ASEGS MVc (Z_to_bv 64 1443673) 1 = Some [Z_to_bv 8 1]) by (apply (P1g _ _ _ _ _ D3); [unfold PR_CELLS; cbn [In]; tauto | lia]).
      assert (ST881824 : rdn ASEGS MVc (Z_to_bv 64 1412512) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1346920)))
        by exact (PCg _ _ _ _ _ D3 0x158da0 8 0x148d68 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
      (* [comment removed for export] *)
      assert (R3k : forall r : reg, In r WV_KEEP -> getr R3 r = getr R2' r) by exact KR3.
      assert (R2k : forall x, In x AS0DRVP_dpB_notty.KS_dpB_notty -> getr R2' (Z_to_bv 5 (Z.of_nat x)) = getr R1' (Z_to_bv 5 (Z.of_nat x))).
      { intros x Hx. rewrite (BKS x Hx). apply RBo. intros X. unfold AS0DRVP_dpB_notty.KS_dpB_notty in Hx. cbn [In] in Hx.
        repeat (destruct Hx as [<-|Hx]; [discriminate X|]). exact Hx. }
      set (VC := fun n : nat => match n with
                 | 2%nat => SC | 40%nat => canz
                 | 8%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 8))) | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
                 | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
                 | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
                 | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22))) | 23%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 23)))
                 | 24%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 24))) | 25%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 25)))
                 | 26%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 26))) | 27%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 27)))
                 | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18))) | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19)))
                 | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20))) | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
                 | 125%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 25))) | 127%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 27)))
                 | _ => 0 end).
      assert (Cg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VC 2%nat)) by (eapply eq_trans; [exact (R3k 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Br2]).
      assert (Cg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 1) by (eapply eq_trans; [exact (R3k 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Br8]).
      assert (Cg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1422992) by (eapply eq_trans; [exact (R3k 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Br9]).
      assert (Cg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7027520) by (eapply eq_trans; [exact (R3k 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Br21]).
      assert (Cg23 : getr R3 (Z_to_bv 5 (Z.of_nat 23)) = Z_to_bv 64 86408).
      { eapply eq_trans; [exact (R3k 23%bv ltac:(unfold WV_KEEP; cbn [In]; tauto))|]. eapply eq_trans; [|exact Ar23]. apply (R2k 23%nat). unfold AS0DRVP_dpB_notty.KS_dpB_notty. cbn [In]. tauto. }
      assert (Cg24 : getr R3 (Z_to_bv 5 (Z.of_nat 24)) = Z_to_bv 64 1).
      { eapply eq_trans; [exact (R3k 24%bv ltac:(unfold WV_KEEP; cbn [In]; tauto))|]. eapply eq_trans; [|exact Ar24]. apply (R2k 24%nat). unfold AS0DRVP_dpB_notty.KS_dpB_notty. cbn [In]. tauto. }
      assert (Cg26 : getr R3 (Z_to_bv 5 (Z.of_nat 26)) = Z_to_bv 64 1).
      { eapply eq_trans; [exact (R3k 26%bv ltac:(unfold WV_KEEP; cbn [In]; tauto))|]. eapply eq_trans; [|exact Ar26]. apply (R2k 26%nat). unfold AS0DRVP_dpB_notty.KS_dpB_notty. cbn [In]. tauto. }
      assert (Cg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VC 118%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VC 119%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VC 120%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VC 122%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg25 : getr R3 (Z_to_bv 5 (Z.of_nat 25)) = Z_to_bv 64 (VC 125%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg27 : getr R3 (Z_to_bv 5 (Z.of_nat 27)) = Z_to_bv 64 (VC 127%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (HSC : 0 <= VC 2%nat < 2 ^ 64) by (cbn [VC]; unfold SC; clear - Hsp' HS1 HS2; lia).
      assert (HSCr : 140735332552704 <= VC 2%nat <= 140737488355328) by (cbn [VC]; unfold SC; clear - Hsp' HS1 HS2; lia).
      assert (HSCa : AS0DRVP_dpCd.aligned (VC 2%nat) 16).
      { cbn [VC]. unfold AS0DRVP_dpCd.aligned, SC. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      assert (CWR : OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs.L5.writable ASEGS MVc (VC 2%nat - 2016) 2160).
      { cbn [VC]. intros d k Hd Hk. apply (WIN3 (SC - 2016) 2160); unfold SC; clear - Hsp' HS1 HS2 Hd Hk; lia. }
      assert (CDF : OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs.L5.defined MVc (VC 2%nat - 2016) 2160).
      { cbn [VC]. intros i Hi. apply (store_ok_defined sp0); [unfold SC; clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (SC - 2016) 2160); unfold SC; clear - Hsp' HS1 HS2 Hi; lia. }
      assert (Cv1088 : OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs.L5.u64_at ASEGS MVc (VC 2%nat + 1088) (VC 2%nat + 1240)).
      { cbn [VC]. replace (SC + 1240) with (S + 24) by (unfold SC; ring). exact (cellA 1088 128 _ _ Am128 eq_refl). }
      assert (Cv1144 : OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs.L5.u64_at ASEGS MVc (VC 2%nat + 1144) (VC 2%nat + 1240)).
      { cbn [VC]. replace (SC + 1240) with (S + 24) by (unfold SC; ring). exact (cellA 1144 72 _ _ Am72 eq_refl). }
      destruct (AS0DRVP_dpCd.dpCd_conc fx2 R3 MVc VC
           HSC (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Hcan
           (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Cg2 Cg8 Cg9 Cg18 Cg19 Cg20 Cg21 Cg22 Cg23 Cg24 Cg25 Cg26 Cg27 HSCr HSCa CWR CDF IMG3
           (fun d k Hd Hk => FW3 1422992 4 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1423024 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1423032 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1423048 8 ltac:(lia) ltac:(lia) d k Hd Hk) (cellL _ _ _ F6a eq_refl) (cellL _ _ _ F3a eq_refl)
           (cellL _ _ _ CAN1 eq_refl) (cellB 40 72 _ _ Bm72 eq_refl) (cellB 104 8 _ _ Bm8 eq_refl) (cellB 96 16 _ _ Bm16 eq_refl) (cellB 88 24 _ _ Bm24 eq_refl) (cellB 80 32 _ _ Bm32 eq_refl)
           (cellB 72 40 _ _ Bm40 eq_refl) (cellB 64 48 _ _ Bm48 eq_refl) (cellB 56 56 _ _ Bm56 eq_refl) (cellB 48 64 _ _ Bm64 eq_refl) (cellA 120 1096 _ _ Am1096 eq_refl)
           (cellA 136 1080 _ _ Am1080 eq_refl) (cellA 128 1088 _ _ Am1088 eq_refl) ST910489 ST881824 (cellA 200 1016 _ _ Am1016 eq_refl) (cellA 192 1024 _ _ Am1024 eq_refl)
           (cellA 184 1032 _ _ Am1032 eq_refl) (cellA 176 1040 _ _ Am1040 eq_refl) (cellA 168 1048 _ _ Am1048 eq_refl) (cellA 160 1056 _ _ Am1056 eq_refl) (cellA 152 1064 _ _ Am1064 eq_refl)
           (cellA 304 912 _ _ Am912 eq_refl) (cellA 640 576 _ _ Am576 eq_refl) (cellA 744 472 _ _ Am472 eq_refl) (cellA 736 480 _ _ Am480 eq_refl) (cellA 728 488 _ _ Am488 eq_refl)
           (cellA 720 496 _ _ Am496 eq_refl) (cellA 712 504 _ _ Am504 eq_refl) (cellA 704 512 _ _ Am512 eq_refl) (cellA 696 520 _ _ Am520 eq_refl) (cellA 688 528 _ _ Am528 eq_refl)
           (cellA 680 536 _ _ Am536 eq_refl) (cellA 672 544 _ _ Am544 eq_refl) (cellA 664 552 _ _ Am552 eq_refl) (cellA 656 560 _ _ Am560 eq_refl) (cellA 648 568 _ _ Am568 eq_refl)
           (cellL _ _ _ Aa892192 eq_refl) (cellA 1056 160 _ _ Am160 eq_refl) (cellA 1112 104 _ _ Am104 eq_refl) (cellA 1104 112 _ _ Am112 eq_refl) (cellA 1096 120 _ _ Am120 eq_refl) Cv1088
           (cellA 1080 136 _ _ Am136 eq_refl) (cellA 1072 144 _ _ Am144 eq_refl) (cellA 1064 152 _ _ Am152 eq_refl) (cellA 1160 56 _ _ Am56 eq_refl) (cellA 1152 64 _ _ Am64 eq_refl) Cv1144
           (cellA 1136 80 _ _ Am80 eq_refl) (cellA 1208 8 _ _ Am8 eq_refl) (cellA 1200 16 _ _ Am16 eq_refl) (cellA 1192 24 _ _ Am24 eq_refl)) as
(fx3 & R4 & MV4 & CGR & _ & CFRZ & CMS & CKS & Cr1 & Cr2 & Cr8 & Cr9 & Cr10 & Cr11 & Cr12 & Cr13 & Cr14 & Cr15 & Cr18 & Cr19 & Cr20 & Cr21 & Cr22 & Cr23 & Cr24 & Cr25 & Cr26 & Cr27 & Ca892192 & Ca892232 & Ca892248 & Ca892224).
      unfold VC in CFRZ, CMS; cbn beta iota in CFRZ, CMS. cbn [VC] in *.
      set (WC := fun a : Z => SC - 2016 <= a < SC - 2016 + 2160 \/ 1422992 <= a < 1422996 \/ 1423024 <= a < 1423040 \/ 1423048 <= a < 1423056).
      assert (FRC : forall a, 0 <= a < 2 ^ 64 -> ~ WC a -> MV4 (Z_to_bv 64 a) = MVc (Z_to_bv 64 a)).
      { intros a Ha Hn. apply CFRZ; [exact Ha | | | | |]; intros X; apply Hn; unfold WC; clear - X; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M3 model3 fx2 fx3 R3 (Z_to_bv 64 0x13f6b8) R4 (Z_to_bv 64 0xaeec0) MV4 WC _ D3 CMS CGR FRC).
      { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; unfold SC in Ha; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
        exists 0x15b5a0, 0x15b8a0. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha; lia]. }
      intros M4 model4 D4 SBM4 VIS4 FRM4.
      assert (cellL4 : forall a (n : nat) bs, rdn ASEGS MVc (Z_to_bv 64 a) n = Some bs ->
                (0 <=? a) && (a + Z.of_nat n <=? 10000000) && ((a + Z.of_nat n <=? 1422992) || (1423056 <=? a) || ((1422996 <=? a) && (a + Z.of_nat n <=? 1423024)) || ((1423040 <=? a) && (a + Z.of_nat n <=? 1423048))) = true ->
                rdn ASEGS MV4 (Z_to_bv 64 a) n = Some bs).
      { intros a n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
        apply Z.leb_le in Hb1, Hb2. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb3.
        apply (rdn_tr MVc MV4 _ _ _ Hr); [exact Hb1 | lia|].
        intros i Hi. apply FRC; [lia|]. unfold WC, SC. clear - Hsp' HS1 HS2 Hb1 Hb2 Hb3 Hi. lia. }
      apply (KONT fx3 R4 M4 model4 D4).
      + exact (same_but_materialized_trans _ _ _ SBM1 (same_but_materialized_trans _ _ _ SBM2 (same_but_materialized_trans _ _ _ SBM3 SBM4))).
      + (* [comment removed for export] *)
        assert (K34 : forall x, (x = 3 \/ x = 4)%nat -> getr R4 (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))).
        { intros x [-> | ->].
          all: (eapply eq_trans; [apply CKS; unfold AS0DRVP_dpCd.KS_dpCd; cbn [In]; repeat first [left; reflexivity | right]|]).
          all: (eapply eq_trans; [apply R3k; unfold WV_KEEP; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]|]).
          all: (eapply eq_trans; [apply R2k; unfold AS0DRVP_dpB_notty.KS_dpB_notty; cbn [In]; repeat first [left; reflexivity | right]|]).
          all: (apply AKS; unfold AS0DRVP_dpA.KS_dpA; cbn [In]; repeat first [left; reflexivity | right]). }
        intros r Hr. unfold c_kept in Hr. cbn [In] in Hr.
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr2|]; rewrite R2; f_equal; unfold SC; ring|].
        destruct Hr as [<-|Hr]; [exact (K34 3%nat ltac:(left; reflexivity))|].
        destruct Hr as [<-|Hr]; [exact (K34 4%nat ltac:(right; reflexivity))|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr8|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr9|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr18|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr19|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr20|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr21|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr22|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr23|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr24|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr25|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr26|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr27|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr.
      + exact Cr10.
      + (* [comment removed for export] *)
        rewrite VIS4. unfold stdoutA.
        split; [exact Ca892192|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ F3a eq_refl) eq_refl)|].
        split; [exact Ca892224|].
        split; [exact Ca892232|].
        split; [exact Ca892248|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ F1a eq_refl) eq_refl)|].
        split.
        { apply (cellL4 1423136 4%nat); [|reflexivity]. rewrite <- le4_m1.
          apply (rdn_tr MVb MVc _ _ _ Ba892336); [lia | cbn; lia|]. intros i Hi. apply FRV3; [cbn in Hi; lia|]. unfold q. cbn in Hi. clear - Hsp' HS1 HS2 Hi. lia. }
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVc MV4 _ CGR); apply (FW3 a n); assumption|].
        split.
        { intros a n H1 H2 d k Hd Hk. apply (store_ok_mono ASEGS k MVc MV4 _ CGR). apply (store_ok_mono ASEGS k MVb MVc _ GRV3).
          apply (store_ok_mono ASEGS k MVa MVb _ BGR). apply (BW1 a n); assumption. }
        intros i Hi. lia.
      + (* [comment removed for export] *)
        rewrite VIS4. unfold stdoutXA.
        split; [exact (cellL4 _ _ _ (cellL _ _ _ Aa892264 eq_refl) eq_refl)|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ F9a eq_refl) eq_refl)|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ F6a eq_refl) eq_refl)|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ Aa892200 eq_refl) eq_refl) | exact (cellL4 _ _ _ (cellL _ _ _ Aa892208 eq_refl) eq_refl)].
      + (* [comment removed for export] *)
        intros a Ha Hn.
        rewrite FRM4 by (exact Ha || (intros X; apply Hn; unfold Wpf1, WC, SC, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        rewrite FRM3 by (exact Ha || (intros X; apply Hn; unfold Wpf1, q, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        rewrite FRM2 by (exact Ha || (intros X; apply Hn; unfold Wpf1, WB, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        apply FRM1; [exact Ha|]. intros X; apply Hn; unfold Wpf1, WA, SOBUF in *; clear - Hsp' HS1 HS2 X; lia.
      + (* [comment removed for export] *)
        intros a Ha Hn. rewrite VIS4.
        rewrite FRC by (exact Ha || (intros X; apply Hn; unfold Wpf1, WC, SC, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        rewrite FRV3 by (exact Ha || (intros X; apply Hn; unfold Wpf1, q, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        rewrite FRB by (exact Ha || (intros X; apply Hn; unfold Wpf1, WB, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        apply FRA; [exact Ha|]. intros X; apply Hn; unfold Wpf1, WA, SOBUF in *; clear - Hsp' HS1 HS2 X; lia.
      + intros a Ha. rewrite VIS4. apply CGR. apply GRV3. apply BGR. apply AGR. exact Ha.
  Qed.
End Printf1.
End FPX_1.
End NraDrvPrintf1.
Module NraDrvPfKeep.
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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvPiece OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvStdio OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0248.NraDrvPrintfK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvG_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvC_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvD_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvLibL OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvE_defs.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section PfKeep.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  #[local] Notation usp := (bv_unsigned sp0).

  #[using="Hsp"] Lemma regions_pfA : forall vals ebs so j bls,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 -> - 2 ^ 22 <= so <= 0 -> 0 <= j <= 500 ->
    (forall i nb, find_nz i bls = Some nb -> hzA sp0 (bv_unsigned (vals_ev vals i)) nb) ->
    regions_ok ASEGS 0 so 3232 bls [] [] IMG_PF_A IMG_RW_A E (fun a => ~ Wpf (usp + so) j a) (fun a => usp + so - 3232 <= a < usp + so).
  Proof.
    intros vals ebs so j bls E P0 Hso Hj Hbl. pose proof Hsp as Hsp'.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold Wpf, SOBUF. lia.
    - intros z Hz. right. lia.
    - intros i nb Hf. destruct (Hbl i nb Hf) as (Z1 & Z2 & Z3). split; [lia|]. intros z Hz. unfold Wpf, SOBUF. lia.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. unfold IMG_PF_A in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; (split; [lia|]; split; [lia|]; intros a Ha; unfold Wpf, SOBUF; lia)|]). destruct Hin.
    - intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
      intros Mx d m Hd Hm.
      apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x6820d0) (Z_to_bv 64 d) 65536%nat m 0x6820d0 0x6920d0);
        first [exact (wseg_stage) | reflexivity | lia | (rewrite u_small by lia; lia)].
  Qed.
End PfKeep.

End NraDrvPfKeep.
