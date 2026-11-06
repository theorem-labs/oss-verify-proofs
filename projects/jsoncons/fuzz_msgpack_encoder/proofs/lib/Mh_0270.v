(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Mh_0270_blobs1 Mh_0270_blobs2.
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require LeanFeed2. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed. From Stdlib Require ZArith List Lia Bool FunctionalExtensionality Permutation. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0181. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0234. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0270 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InC46Stdlib5Lists4List9incl_applC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI46Stdlib9micromega7EnvRing5PExpr00I46Stdlib9micromega=RingMicromega5Psatz00C56Stdlib5Arith8PeanoNat3Nat3eqbK46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3powK45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P37alignedC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS35own13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7kstr_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3KCAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA6b64lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_ctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS37ocell13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_pfactsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8avis_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u64_at_visC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4valsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG37bvu_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P38qxZ_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02567PmAUarK5PMAUK5WretXC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK47Corelib4Init5Logic2or01C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6frb_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6brb_ofC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6KSKEEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6KCKEEPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5asciiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_finC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z6of_natK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes3nat00c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3IXPC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5B64_HC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5wappWC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6RETIREC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5V2_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3Hh2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5HSPCfC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P36KS_qxZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rbf0e8_bf0ec7W_befa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rbf0e8_bf0ec7F_befa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rbf0e8_bf0ec7D_befa4C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3WPFC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic3iffC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega=RingMicromega5Psatz07C46Stdlib9micromega:ZMicromega=Zeval_formulaC59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7sub_0_rC69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Z2Nat2idc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4FRAMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7src_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P3:qxT12_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR36g_footC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C9FRAM_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4SRCXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3KSXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3KCXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR3>g_callee_entryC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib6ZArith4Zdiv:Z_mod_multK47Corelib4Init5Logic2ex01C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4aobjC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C:byte_of_u8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5aacc3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A;defined_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM8zeros_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01819PnAAdCtor6PQAADC9mset_postC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9ahpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_appbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR37g_afterC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_monoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4SRCCC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA5akeptC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_consC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C=u8_of_definedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P39qxTB_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8aclientwC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4a4_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6FB_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4a4_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4a4_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5TPUSHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01819PnAAdCtor6PQAADC5amsetC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto7eval_bfK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_apart1C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR37g_pieceC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5RA_MSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6TQHEADC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6TAILPCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4MSETC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7o_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3OAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P38KS_qxT12C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P37KS_qxTBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3MSTC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_lC69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P39qxQE_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5QBODYC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P39qxQR_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C9MST_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7A4_keepC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P37KS_qxQEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6RA_PB1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5ADVPCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5QHEADC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7x_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C8nb_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4GMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P37KS_qxQRC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_02349PnAAdB6P18PQAAB6P17alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7ck_reflC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6srcclsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_apprc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C>srccls_aclientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C8src_xferC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4IMGWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01799PnAImgGap6PMAGAP8gapB_visC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib7Mh_02349PnAAdB6P18PQAAB6P19qxB0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6incl_bC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdB6P18PQAAB6P19qxB1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C:FRAM_unvisC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4MAINC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5RA_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdB6P18PQAAB6P17KS_qxB1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4HEADC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4ALPHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7src_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdB6P18PQAAB6P17KS_qxB0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan;L5ADetailHR6L5ADHR;statics_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR39stk_w_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdB6P18PQAAB6P19qxA0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS3;own13_agreeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02567PmAUarK5PMAUK4gctx00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5SETUPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdB6P18PQAAB6P1:qxA16_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR37g_enterC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C2N0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdB6P18PQAAB6P17KS_qxA0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdB6P18PQAAB6P18KS_qxA16C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA4PMEAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8pot_encAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ndestC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;pot_adaptorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_b_linC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA@hl_aligned_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=hl_b_overheadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_K0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_B0C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00849HeapIface;heap_layout01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7pot_aeAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6edepthC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8hdr_contC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP18PQAABAP17alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4aownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA9pot_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ea_valC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA4own8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA6ocell8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC69OSSVerify5KrLib7Mh_01028NemModel3NEM5enc_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5err_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38obj_pf_uC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lvec_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA5xinvAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_ctxC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN4n_oaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP18PQAABAP1;qvaDs2_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout@ne_begin_arr_lenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA4GOCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA4GOWNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_WAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8sink_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ec_stateAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_visitorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lvec_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4EVISC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN6n_memGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5binvNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA6xpieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN>n_callee_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;PermutationHPermutation_app_swap_appC46Stdlib7Sorting;Permutation?Permutation_symC69OSSVerify5KrLib7Mh_02569PnAKRunA16PQAKRA7ri_permC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orC46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA7ly_costC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKObjA16PQAKOABpot_adaptor_nonnegC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA;epot_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC69OSSVerify5KrLib7Mh_02259NemModelA4NEMA;edepth_roomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA@v_begin_arr_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8aargs_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9pre_beginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5W_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5aeownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS:step_beginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8push_lawC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8enc_pushC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK=blk_obj_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA3agAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO=adaptor_keepSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN>kcontent_agreeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<stack_clientC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8vis_packC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38word_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP18PQAABAP1:qvaX1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A3cfgC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9adaptor_WC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9ek_calleeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9dk_calleeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8dk_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC56Stdlib6ZArith6BinInt1Z8le_max_rC69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5zsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA9step_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ>model_rt_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK8ret_exitC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9apiece_roC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN7n_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7enc_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092;PnQStaticsA5PQSTA7err_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ENC_HC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA3IXDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP18PQAABAP19KS_qvaDs2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP18PQAABAP18KS_qvaX1C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00849HeapIface;heap_layout00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA2CRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_KBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5VIS_HC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA7oec_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA5HFR80C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_DVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9AOFF_DESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8AOFF_KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_LVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9eargs_lenC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rb09ac_b09b07W_b0868C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rb09ac_b09b07F_b0868C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rb09ac_b09b07D_b0868C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_kbgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lv_shapeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8lv_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_tC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5lv_eoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN4n_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7alvl_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG>u64_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u32_at_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG38regl_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA6PUSHLVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA3S2VC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA5COMMAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP2;qvaKT0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP2<qvaKT1z_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP2<qvaKT1n_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP18PQAABAP1:qvaDt_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP2;qvaVK2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP2;qvaV1z_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP2;qvaV1n_concC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP18PQAABAP18KS_qvaDtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP29KS_qvaKT0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP2:KS_qvaKT1zC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA3IXAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP2:KS_qvaKT1nC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP29KS_qvaVK2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP29KS_qvaV1zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP29KS_qvaV1nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5wappWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL4OWNEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5own13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5a_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5xinvGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3ESTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP17alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP19qvbQ_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38aobj_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA8xinv_ekFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3phiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL9pot_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3Hh3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3OCEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL5HSPCfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3IXAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL5V2_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP17KS_qvbQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rb4d74_b4d787W_b4c30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rb4d74_b4d787F_b4c30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rb4d74_b4d787D_b4c30C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL7oa_lo96C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP47alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_oaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO7aown_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO8aown_keyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL:mem_eq_frzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL8INS_CALLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7s_pieceC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4<qvbIVSS_concC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indc69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL6div2_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4<qvbIVSL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4<qvbIVLS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4<qvbIVLL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4<qvbIKSS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4<qvbIKSL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4<qvbIKLS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4<qvbIKLL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_kstrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitc69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL2IXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4:KS_qvbIVSSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4:KS_qvbIVSLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4:KS_qvbIVLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4:KS_qvbIVLLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4:KS_qvbIKSSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4:KS_qvbIKSLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4:KS_qvbIKLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP48PQAABLP4:KS_qvbIKLLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP68PQAABLP67alignedC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N7s_oa_shC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4ea_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ea_bsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_strC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8leb_specC69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8view_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA8s_kpieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9u8_at_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7cell_isC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan;L5ADetailHR6L5ADHR:byte_of_u8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02568PnAKRunF6PQAKRF:aacc_localC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL9aacc_joinC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL8aacc_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02566PmAUar6PMAUAR:aobjA_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA:v_key_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA9aargs_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC:ascii_utf8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pre_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8step_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP1:qvbKr_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3ADVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP68PQAABLP6<qvbKdS2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP68PQAABLP6<qvbKdL2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA:fobj_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA8s_xpieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ENC_SLOTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ENC_HSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL7oec_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL8ov_rng56C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL7DU_DPHIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4KCAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP18KS_qvbKrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP68PQAABLP6:KS_qvbKdS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP68PQAABLP6:KS_qvbKdL2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N4kclrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_setC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_restC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N9s_own_neqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL2LQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL2LNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL2LBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3LQNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA8src_okCAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5s_xkwC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N9kclr_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3INGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL4LITRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N9s_lit_srcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_rw_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_canaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_need_locksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_locale_lockC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL<lit_bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ins_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7ins_scCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL6LB_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_SMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL9lit_asciiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL5DISP2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N7s_kclrXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2=qvbKe0S0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2=qvbKe0S1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A<writable_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2=qvbKe0L0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2=qvbKe0L1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2=qvbKe1S0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2=qvbKe1S1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2=qvbKe1L0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2=qvbKe1L1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_xcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N9s_call_sCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;s_own_apartC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5INS_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2;KS_qvbKe0S0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2;KS_qvbKe0S1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2;KS_qvbKe0L0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2;KS_qvbKe0L1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2;KS_qvbKe1S0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2;KS_qvbKe1S1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2;KS_qvbKe1L0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP28PQAABLP2;KS_qvbKe1L1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP19qvbB_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL5DISP1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP17KS_qvbBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK8mach_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP1:qvbA0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL5SETUPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP1;qvbA16_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8s_enterXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL5xinv0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL2CRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL5GOWNEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP18KS_qvbA0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP19KS_qvbA16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP18PQAABOP17alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO9pot_splitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO4own8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO6ocell8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO5xinvAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP18PQAABOP1;qvoDs2_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout@ne_begin_obj_lenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO4GOCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO4GOWNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO6xpieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO;epot_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA@v_begin_obj_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP18PQAABOP1:qvoX1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO3IXDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP18PQAABOP19KS_qvoDs2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP18PQAABOP18KS_qvoX1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO2CRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO7oec_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO5HFR80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb313c_b31407W_b2ff8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb313c_b31407F_b2ff8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb313c_b31407D_b2ff8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP27alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO6PUSHLVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO3S2VC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO5COMMAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP2;qvoKT0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP2<qvoKT1z_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP2<qvoKT1n_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP18PQAABOP1:qvoDt_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP2;qvoVK2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP2;qvoV1z_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP2;qvoV1n_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP18PQAABOP18KS_qvoDtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP29KS_qvoKT0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP2:KS_qvoKT1zC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO3IXAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP2:KS_qvoKT1nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP29KS_qvoVK2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP29KS_qvoV1zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP29KS_qvoV1nC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT4OWNEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3ESTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP17alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP19qvtQ_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT9pot_splitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3IXAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5V2_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3OCEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5HSPCfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP17KS_qvtQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb5b6c_b5b707W_b5a28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb5b6c_b5b707F_b5a28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb5b6c_b5b707D_b5a28C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT7oa_lo96C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP68PQAABTP67alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP78PQAABTP77alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_binC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT2XVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275<PnAKSlotA3bN8PQAKS3BN4s_pvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP68PQAABTP6:qvtDa_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP78PQAABTP7;qvtDb2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3xvFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT9aacc_joinC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK7blk_imgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA7agA_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA:accA_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA?v_bstr_tag_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA:aargs_bstrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT;hdr_bin_le5C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8pre_viewC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9step_viewC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP1:qvtJ1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT:b64len_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3ADVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT2IXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT7oec_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT8ov_rng56C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT6tg_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP68PQAABTP68KS_qvtDaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP78PQAABTP79KS_qvtDb2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT4VOKfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT8DKB_DPHIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP18KS_qvtJ1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT9DKB_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP47alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT:mem_eq_frzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT8INS_CALLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4<qvtIVSS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT6div2_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4<qvtIVSL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4<qvtIVLS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4<qvtIVLL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4<qvtIKSS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4<qvtIKSL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4<qvtIKLS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4<qvtIKLL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3IXBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4:KS_qvtIVSSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4:KS_qvtIVSLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4:KS_qvtIVLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4:KS_qvtIVLLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4:KS_qvtIKSSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4:KS_qvtIKSLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4:KS_qvtIKLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP48PQAABTP4:KS_qvtIKLLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT8aacc_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP1:qvtKr_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP78PQAABTP7<qvtKdS2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP78PQAABTP7<qvtKdL2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP18KS_qvtKrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP78PQAABTP7:KS_qvtKdS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP78PQAABTP7:KS_qvtKdL2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP38PQAABTP37alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5QUOTEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5COMMAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5KDESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP38PQAABTP3;qvtDKz_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP38PQAABTP3;qvtDKn_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP38PQAABTP3;qvtDV2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP38PQAABTP3<qvtDV1z_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP38PQAABTP3<qvtDV1n_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP38PQAABTP39KS_qvtDKzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP38PQAABTP39KS_qvtDKnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP38PQAABTP39KS_qvtDV2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP38PQAABTP3:KS_qvtDV1zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP38PQAABTP3:KS_qvtDV1nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP27alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundc69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT6xv_ptwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275<PnAKSlotA3bN8PQAKS3BN:s_view_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275<PnAKSlotA3bN8PQAKS3BN9b64_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275<PnAKSlotA3bN8PQAKS3BN7b64_scEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5DISP2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP2<qvtKe0S_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP2<qvtKe0L_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP2<qvtKe1S_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP2<qvtKe1L_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275<PnAKSlotA3bN8PQAKS3BN9s_call_sEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT6pv_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP2:KS_qvtKe0SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP2:KS_qvtKe0LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP2:KS_qvtKe1SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP2:KS_qvtKe1LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP19qvtB_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5DISP1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP17KS_qvtBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP1:qvtA0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5xv_ekC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5SETUPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP1;qvtA16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5xinv0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT2CRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5GOWNEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP18KS_qvtA0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP18PQAABTP19KS_qvtA16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3xv0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA4ndigC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP28PQAAFUP27alignedC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List=repeat_lengthC69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ45own12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ47ocell12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02567PmAUarK5PMAUK9vis_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP28PQAAFUP2:qfuQE_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5>writable_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01897PnARel36PNAREL@setshadow_f5_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib?AxSymExec3Sound4AX2S:wbytes_outC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP28PQAAFUP29qfuZ_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC6KSKEEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC6KCKEEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC4valsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3IXPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP28PQAAFUP27KS_qfuZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA6FROM_HC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5wappWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5RA_PBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5V2_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3Hh2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC8nd_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5HSPCfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP28PQAAFUP28KS_qfuQEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01897PnARel36PNAREL4KEPTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb94bc_b94c07W_b9378C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb94bc_b94c07F_b9378C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb94bc_b94c07D_b9378C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP18PQAAFUP17alignedC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib7Mh_02136PnVisA4PQVA6ndig_fC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC:ndig_f_ge1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC9to_bv_modC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuDP8PQAAFUDP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuDP8PQAAFUDP:qfuLk_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC<digit_edenotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallc69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5div10C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z8sub_diagC56Stdlib6ZArith6BinInt1Z7mod_modC46Stdlib6ZArith4Zdiv:Zminus_modc69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC;to_bv_congrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP18PQAAFUP19qfuX_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC9ndig_f_ltC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC9ndig_f_geC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP18PQAAFUP19qfuM_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuDP8PQAAFUDP8KS_qfuLkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC2KDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP18PQAAFUP17KS_qfuMC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3M10C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC4LOOPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC2QBC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop04I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP18PQAAFUP17KS_qfuXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK9base_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP18PQAAFUP19qfuB_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5DLOOPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3WPDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A<zeros_at_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3DGFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3KSXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3KCXC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7le_reflc69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC4PUSHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP18PQAAFUP17KS_qfuBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5RA_SMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC7o_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC7x_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP18PQAAFUP1:qfuA0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ4;own12_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC6DIGITSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP18PQAAFUP1;qfuA16_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP18PQAAFUP18KS_qfuA0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP18PQAAFUP19KS_qfuA16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC2N0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA4svalC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3absc69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI64OWNEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI63ESTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI64valsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8abs_specC69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P17alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P19qviQ_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI69pot_splitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI63OCEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI65HSPCfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI63IXAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI64QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI68sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI65V2_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P17KS_qviQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb22d0_b22d47W_b218cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb22d0_b22d47F_b218cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb22d0_b22d47D_b218cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI67oa_lo96C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P47alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI6:mem_eq_frzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI68INS_CALLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4<qviIVSS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI66div2_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4<qviIVSL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4<qviIVLS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4<qviIVLL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4<qviIKSS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4<qviIKSL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4<qviIKLS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4<qviIKLL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI62IXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4:KS_qviIVSSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4:KS_qviIVSLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4:KS_qviIVLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4:KS_qviIVLLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4:KS_qviIKSSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4:KS_qviIKSLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4:KS_qviIKLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P48PQAAI6P4:KS_qviIKLLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA6ncharsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P68PQAAI6P67alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI6:nchars_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI69aacc_joinC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI68aacc_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P1:qviKr_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI63ADVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P68PQAAI6P6<qviKdS2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P68PQAAI6P6<qviKdL2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI67oec_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI68ov_rng56C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI67DU_DPHIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P18KS_qviKrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P68PQAAI6P6:KS_qviKdS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P68PQAAI6P6:KS_qviKdL2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P28PQAAI6P27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA;from_argsCQC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9from_scCQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI65DISP2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P28PQAAI6P2<qviKe0S_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P28PQAAI6P2<qviKe0L_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P28PQAAI6P2<qviKe1S_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P28PQAAI6P2<qviKe1L_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA:s_call_sCQC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P28PQAAI6P2:KS_qviKe0SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P28PQAAI6P2:KS_qviKe0LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P28PQAAI6P2:KS_qviKe1SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P28PQAAI6P2:KS_qviKe1LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P19qviB_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI65DISP1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P17KS_qviBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P1:qviA0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI65SETUPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P1;qviA16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI65xinv0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI62CRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI65GOWNEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P18KS_qviA0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P19KS_qviA16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP28qiQ_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC6KSKEEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC6KCKEEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC4valsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3IXAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP26KS_qiQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC5HSPCfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC5wappWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC6RETIREC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC5V2_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3Hh2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rb99dc_b99e07W_b9898C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rb99dc_b99e07F_b9898C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rb99dc_b99e07D_b9898C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ47g_footLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3WP5C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3KSFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC6STKSH4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commC69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP2;qiC1S1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3GEKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3KSXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3KCXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC4SRCXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3SBXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3K2AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP2;qiC1S0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3K2BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3PBFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC8src_pushC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3OSAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP2;qiC1L1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP2;qiC1L0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ4;g_piece_lowC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC2IXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0f4_ba0f87W_b9fb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0f4_ba0f87F_b9fb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0f4_ba0f87D_b9fb0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC5CALLPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC7o_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC7x_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5SMMAXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3IXCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP29KS_qiC1S1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP29KS_qiC1S0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP29KS_qiC1L1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP29KS_qiC1L0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP17alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3WPBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP1:qiBS0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC7kc_nil0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP19qiBS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC5CHAINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP1:qiBL0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP19qiBL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP18KS_qiBS0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC5RA_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP17KS_qiBSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP18KS_qiBL0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP17KS_qiBLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3OAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP19qiA0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC5SETUPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP1:qiA16_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP17KS_qiA0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP18PQAAINP18KS_qiA16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC2N0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP28qjQ_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC6KSKEEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC6KCKEEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC4valsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3IXAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP26KS_qjQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC5HSPCfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC5wappWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC6RETIREC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC5V2_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3Hh2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rbe71c_be7207W_be5d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rbe71c_be7207F_be5d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rbe71c_be7207D_be5d8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3WP5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3KSFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC6STKSH4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP2;qjC1S1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3GEKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3KSXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3KCXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC4SRCXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3SBXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3K2AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP2;qjC1S0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3K2BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3PBFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC8src_pushC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3OSAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP2;qjC1L1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP2;qjC1L0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC2IXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC5CALLPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC7o_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC7x_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3IXCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP29KS_qjC1S1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP29KS_qjC1S0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP29KS_qjC1L1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP29KS_qjC1L0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP17alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3WPBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP1:qjBS0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC7kc_nil0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP19qjBS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC5CHAINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP1:qjBL0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP19qjBL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP18KS_qjBS0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC5RA_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP17KS_qjBSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP18KS_qjBL0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP17KS_qjBLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3OAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP19qjA0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC5SETUPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP1:qjA16_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP17KS_qjA0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP18PQAAJNP18KS_qjA16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC2N0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL4OWNEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3ESTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP17alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP19qvnQ_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL9pot_splitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3OCEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL5HSPCfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3IXAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL5V2_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP17KS_qvnQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rb44b8_b44bc7W_b4374C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rb44b8_b44bc7F_b4374C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rb44b8_b44bc7D_b4374C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL7oa_lo96C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP37alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL:mem_eq_frzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL8INS_CALLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3<qvnIVSS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL6div2_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3<qvnIVSL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3<qvnIVLS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3<qvnIVLL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3<qvnIKSS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3<qvnIKSL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3<qvnIKLS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3<qvnIKLL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL2IXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3:KS_qvnIVSSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3:KS_qvnIVSLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3:KS_qvnIVLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3:KS_qvnIVLLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3:KS_qvnIKSSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3:KS_qvnIKSLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3:KS_qvnIKLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP38PQAANLP3:KS_qvnIKLLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP58PQAANLP57alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL9aacc_joinC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL8aacc_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP1:qvnKr_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3ADVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP58PQAANLP5<qvnKdS2_concC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_02029PnAAdNlP58PQAANLP5<qvnKdL2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL7oec_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL8ov_rng56C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL7DU_DPHIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP18KS_qvnKrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP58PQAANLP5:KS_qvnKdS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP58PQAANLP5:KS_qvnKdL2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP27alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL4INS2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL5COMMAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL5KDESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2;qvnDKz_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2;qvnDKn_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2;qvnDV2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2<qvnDV1z_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2<qvnDV1n_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP29KS_qvnDKzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP29KS_qvnDKnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP29KS_qvnDV2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2:KS_qvnDV1zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2:KS_qvnDV1nC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL2LQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL2LNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL2LBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3LQNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3INGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL4LITRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL<lit_bytes_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL6LB_lenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL9lit_asciiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL5DISP2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2<qvnKe0S_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2<qvnKe0L_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2<qvnKe1S_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2<qvnKe1L_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2:KS_qvnKe0SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2:KS_qvnKe0LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2:KS_qvnKe1SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP2:KS_qvnKe1LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP19qvnB_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL5DISP1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP17KS_qvnBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP1:qvnA0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL5SETUPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP1;qvnA16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL5xinv0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL2CRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL5GOWNEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP18KS_qvnA0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP19KS_qvnA16C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP17alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4own7C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS6ocell7C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3advC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addK69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6set_lvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4valsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS9ndest_advC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_pieceC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK8lb_nodupC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK<fst_neq_appAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK9blk_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7blk_outC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN9n_own_neqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN;n_own_apartC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C69OSSVerify5KrLib7Mh_02259NemFrameA5NEMFA9enc_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemFrameA5NEMFA:sink_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemFrameA5NEMFA>ec_state_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN8err_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN6n_advXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP1=qvsAk2e0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP1=qvsAk2e1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP1=qvsAk1e1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3IXAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9TAG_ENANOC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS5QENNxC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4GOWNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS5HFR64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4GOCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS8sp_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP1;KS_qvsAk2e0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP1;KS_qvsAk2e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP1;KS_qvsAk1e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ea_tagC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP48PQAAVSP47alignedC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsDiff_impl_subrelationC47Corelib7Program6Basics4implC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6leb_gtc69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS2XVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4n_pvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA7view_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS:n_view_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP48PQAAVSP4:qvsD2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA16PQAKRA=model_rt_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3xvNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout9ne_stringC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA9aargs_strC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR6rchain00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS:rchain_nilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8pre_vstrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8step_strC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS9AFTERCALLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP48PQAAVSP4;qvsKd2_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout6ne_keyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS;eslotA_famCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS7xpieceIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNF7PQAKENF9ENC_SLOTFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3IXDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP48PQAAVSP48KS_qvsD2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4XNN0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4XGE0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4EST0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4EARGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4VSRAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP48PQAAVSP49KS_qvsKd2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3ENKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3EK0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3DK0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8TAG_NONEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS2CRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3CK0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS6ne8_oaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS9DKB_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS6tg_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS8ov_rng56C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS7oec_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3o_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ;qa_off_vrefC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_parserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA4o_isC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3o_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3o_vC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA6o_sinkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA4o_ecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4acctC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3balC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5p_stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5p_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6unreadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6eboundC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA3ownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA5ocellC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5oacctC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3cplC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8mgrow_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM9nullis_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6p_moreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_tbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_bbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4PgV84PGV85v8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_sbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_skC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7mvec_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6p_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7p_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM=src_fields_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8src_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA4mownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN5binvGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN6m_memGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4REGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8gs_classC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKObjA16PQAKOA7set_fldC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA6minv_dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA6mpush1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA9room_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8pot_runAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNAAgs_class_hdr_contC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA6vfactsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP9qbaC_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA6d_pushC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4GOWNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6acct_dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7oacct_dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8mrun_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ@qa_v_begin_arrayC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;mparser_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8args_ec4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA>oacct_val_roomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8pre_pushC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA;cle_of_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA>pot_aeA_le_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN6m_memRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9mstate_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6ms_idxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7ms_modeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_addC69OSSVerify5KrLib7Mh_01028NemModel3NEM;hdr_cont_leC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC69OSSVerify5KrLib7Mh_02259NemModelA4NEMA=oacct_consumeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA:oacct_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA=ebound_of_balC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA7ck_slotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA5FIN_DC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN<mk_call_slotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKObjA16PQAKOA:set_fld_idC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN9mk_pieceGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:mparser_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6iss_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8mrun_finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA4annAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6mstate00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP7KS_qbaCC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leI69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4mpst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4strm00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lv_rootC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5PSIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8OFF_MAXDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7OFF_SRCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6OFF_TBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6OFF_BBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7OFF_STKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA2H6C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA3HFRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4GOCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4UNR0C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:pot_estackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA7spa_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9pot_textMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_bgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4PgV84PGV86pot_v8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtC69OSSVerify5KrLib7Mh_02136PnRunA4PQRA<mstack_shapeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:acredit_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6mstate01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6ms_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP:qbaB1_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_off_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_off_isC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKObjA16PQAKOA?pot_rest_nonnegC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA=pot_ae_nonnegC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z9pow_add_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6adebitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKObjA16PQAKOA7set_vecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_tgC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4mpst01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9mode_contC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKObjA16PQAKOAAmstack_shape_pushC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA7ck_pushC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4SLOTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN<mk_call_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP8KS_qbaB1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8TSRES_MEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3PSZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA7hv_costC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op206C59OSSVerify5KrLib7Mh_00189PnLayoutQ>qa_begin_arrayC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN9mem_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN6m_memEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP9qbaX_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA:own_of_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4ownvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA7bvu_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP9qbaE_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA8fin_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA:mprog_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02567PnAKRun5PQAKR@credit_keep_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN<mk_call_mkecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN6mk_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP7KS_qbaXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP7KS_qbaEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rc6364_c63687W_d3244C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rc6364_c63687F_d3244C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rc6364_c63687D_d3244C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP9qbaA_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA7gs_typeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA9mprog_lenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA5GSERRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4PUSHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN?mk_call_getsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP7KS_qbaAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS3ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN5m_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS4REGSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS5ocellC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN9mk_pfactsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS7bvu_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP17PQAGSP17alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP17PQAGSP19qgsQ_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA>room_keep_sameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN6mk_finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP17PQAGSP17KS_qgsQC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4PgV84PGV82v800C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS2H5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS5HSPCfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rc6d9c_c6da07W_d3c7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rc6d9c_c6da07F_d3c7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rc6d9c_c6da07D_d3c7cC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3:qgsFm_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3:qgsFa_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3<qgsT212_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3<qgsT213_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3<qgsT214_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3<qgsT215_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3<qgsT216_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN8mk_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP38KS_qgsFmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP38KS_qgsFaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3:KS_qgsT212C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3:KS_qgsT213C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3:KS_qgsT214C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3:KS_qgsT215C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3:KS_qgsT216C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6sr_remC1?~~~~~~~~~~~~~~~I46Stdlib9micromega7EnvRing3Pol00C59OSSVerify5KrLib7Mh_00188PmLayout;pa_src_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP47alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8with_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_qcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP4;qgsR1o_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP4;qgsR1e_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS4ERR1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN<mk_call_mkecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN<mk_call_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP49KS_qgsR1oC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP49KS_qgsR1eC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM5srcst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP4;qgsR2o_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP4;qgsR2e_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS4ERR2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP49KS_qgsR2oC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP49KS_qgsR2eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP4;qgsR4o_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP4;qgsR4e_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS4ERR4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP49KS_qgsR4oC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP49KS_qgsR4eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP37alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS:WALK_CONSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2<qgsT196_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS5READ1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2<qgsT197_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS5READ2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2<qgsT198_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS5READ4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2<qgsT199_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2<qgsT200_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2<qgsT201_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2<qgsT217_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2<qgsT218_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2<qgsT219_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3<qgsT220_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3<qgsT221_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3<qgsT222_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3<qgsT223_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2:KS_qgsT196C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2:KS_qgsT197C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2:KS_qgsT198C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2:KS_qgsT199C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2:KS_qgsT200C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2:KS_qgsT201C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2:KS_qgsT217C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2:KS_qgsT218C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP27PQAGSP2:KS_qgsT219C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3:KS_qgsT220C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3:KS_qgsT221C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3:KS_qgsT222C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0235<PnAGetSizeP37PQAGSP3:KS_qgsT223C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK7stk_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA9frame_okMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP17PQAGSP1:qgsA0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS9own_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS5SETUPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN8mk_enterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP17PQAGSP1;qgsA16_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP17PQAGSP18KS_qgsA0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP17PQAGSP19KS_qgsA16C1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses;subrelationC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9Morphisms5flip2C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_rt_roC1?~~~~~~~~~~~~~~~C47Corelib9RelationsDRelation_Definitions8relationC47Corelib7Classes9Morphisms@subrelation_reflC45stdpp9bitvector;definitions:bv_modulusC47Corelib7Classes9MorphismsBsubrelation_properC69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA:opdel_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA=src_dtor_specC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8mvec_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_deC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA4mownC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS14sub8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z<divide_transC69OSSVerify5KrLib7Mh_02137PnStepA4PMKA=aobj_of_aobjAC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:aobj_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ<aior_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<asan_staticsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8aly_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A=statics_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5ACimg_clear_mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA9wapp_consC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=aclient_casesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8ek_sublbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA>obj_shadow_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02567PnAKRun5PQAKR9zeros_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02567PnAKRun5PQAKR8div8_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP9qrdA_concC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:obj_clientC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8dk_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:astk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA;stksh_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST3depC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnARdDtor6PQARDD7dep_stdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnARdDtor6PQARDD7sro_stdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA:acc_keepA'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS17vis_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnBrObjA5PNBOA3sntC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnBrObjA5PNBOA3snsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnBrObjA5PNBOA4sAGXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnBrObjA5PNBOA4sSHXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO;lvec_keep_xC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_middleC56Stdlib6ZArith6BinInt1Z7mod_addC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8astk_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA?shadow_zero_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ff_capC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ff_rsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAReset16PMARS1Bacc_of_shadow_zeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=defined_growsC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation>Permutation_inC69OSSVerify5KrLib7Mh_02137PnStepA4PMKAAastk_after_ahpresC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnARdDtor6PQARDD4dinvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnARdDtor6PQARDD;stage_factsC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC46Stdlib5Lists4List:in_app_iffC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib4Init5Logic6or_indC69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP9qrdD_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA6S_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO;mvec_keep_xC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnARdDtor6PQARDD=ffroomB_lowerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8dk_sublbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnBrObjA5PNBOA5gspanC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnBrObjA5PNBOA8gspan_geC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnARdDtor6PQARDD7gspan_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4PgV84PGV86v8_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnRunBA4PNRA<lb_remove_v8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP9qrdE_concC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4PgV84PGV82v802C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA7mod16_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnBrObjA5PNBOA9v8_keep_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP9qrdG_concC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?mem_eq_of_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnBrObjA5PNBOA:src_keep_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA@nullis_at_agreeAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA7ffroomAC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP9qrdH_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9even_byteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP:qrdFs_concC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation@Permutation_reflC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF8odd_byteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP:qrdFl_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0244:PnAVu8Dtor6PNAV8D;vu8_dtor_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6apieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAVecDtor5PQAVD;vec_dtor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP:qrdCs_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP:qrdCl_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9mrest_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP:qrdBs_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP:qrdBl_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228<PnAVecDtorLv6PQALVD>vec_dtor_lv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ>qa_reader_dtorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnRunAa5PQRAa@reader_dtor_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7src_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA=base_ok_keepAC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR>aclient_narrowC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9Morphisms;ProperProxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP8KS_qrdFlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP7KS_qrdEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP7KS_qrdDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP8KS_qrdClC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP8KS_qrdBlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP7KS_qrdAC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4PgV84PGV82v801C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA:addrs_wf_AC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP7KS_qrdGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP7KS_qrdHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP8KS_qrdFsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA9OPDEL_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP8KS_qrdCsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnARdDtorP6PQARDP8KS_qrdBsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnRunHA5PQRHA6RDRD_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5CHUNKC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02137PnRunHA5PQRHA5RSIZEC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3LSZC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_ReflexiveC59OSSVerify5KrLib7Mh_0009ENa0_code_rae6c4_ae6c87W_b008cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rae6c4_ae6c87F_b008cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rae6c4_ae6c87D_b008cC1?~~~~~~~~~~~~~~~".
Module PnAAdB6C.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0181. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0234. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKSlotA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKStrA3c OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKStrA3d OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.PnAImgGap OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0181.PnAAdCtor OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0234.PnAAdB6P1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201.PnAAdB6P2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201.PnAAdB6P3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012.Na0_code_rbf0e8_bf0ec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdB6C () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List4inclC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbI45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z3lorC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula09K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic3and01c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7div_rngC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z<eq_decidableI47Corelib4Init5Logic2or00c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4lor6C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z7div_addK46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA6b64lenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rK47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_addK47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib5Lists7ListDef3seqI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes4bool02C46Stdlib5Lists4List2InC69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z6ltb_ltC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C8alph_allC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5B64_HC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR36obj_pfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_02137PnStepA4PMKA9wapp_consC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7o_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5asciiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7kstr_atC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4GMAXC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C:b64len_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C9b64len_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7src_okAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6srcclsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z;div_le_monoC69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA:accA_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C9rdn_agreeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith4Znat5Nat2Z2idC69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA;S_in_shadowC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7ceil_hiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS3:kstr_keepAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3KCAC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN>kcontent_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS35own13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3WPFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_ctxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_consC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=aclient_casesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS37ocell13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_apart1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3Hh2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5wappWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5HSPCfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6frb_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6brb_ofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3GEKC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_applc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6KSKEEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6KCKEEPC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes?RelationClasses>eq_equivalenceC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multC46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrK46Stdlib9micromega=RingMicromega3Op206C46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C>srccls_aclientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C9src_whereC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5V2_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7SRC_WPFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C8src_xferC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8vis_packC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01799PnAImgGap6PMAGAP;img_sh_avisC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat6inj_ltC46Stdlib5Lists4List:length_mapC69OSSVerify5KrLib7Mh_00906L5Core3L5C<rdn_bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9u8_at_visC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A<zeros_at_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C:u8_of_byteC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4FRAMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C8sp_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_pfactsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8avis_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u64_at_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR3>g_callee_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02566PmAUar6PMAUAR:aobjA_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA9pb_specCAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR37g_afterC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA5akeptC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=fframe_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C9FRAM_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4SRCCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4PBPCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3IXPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3OAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK9base_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK8mach_visC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P37alignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02567PmAUarK5PMAUK4gctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7cell_isC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C8FRAM_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01799PnAImgGap6PMAGAP8gapB_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6FB_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4IMGWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7alph_okC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z:div_uniquec69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5land7C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P3:qxTQB_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR36g_footC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4SRCXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3KSXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3KCXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7A4_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6PBCALLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR37g_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6TQHEADC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P38KS_qxTQBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6RA_PB2C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA8cle_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P3:qxTQE_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA8ck_transC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6FRAM24C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3FINC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6TQBODYC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4succC69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P3:qxTQR_concC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6RETIREC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Zc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7x_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C8nb_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P38KS_qxTQEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P38KS_qxTQRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P39qxT0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6TAILPCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P37KS_qxT0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3MSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6incl_bC1?~~~~~~~~~~~~~~~C46Stdlib5Logic>Classical_Prop7classicC69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P39qxQB_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C9MST_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5QHEADC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P38PQAAB6P37KS_qxQBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6RA_PB1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4SRCBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P29qxSZ_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P29qxS1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P29qxS2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P29qxS3_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P29qxS4_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P29qxS5_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P29qxS6_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P29qxS7_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4HEADC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4RBPCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27KS_qxSZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27KS_qxS1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27KS_qxS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27KS_qxS3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27KS_qxS4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27KS_qxS5C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27KS_qxS6C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27KS_qxS7C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:mod_uniqueC69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8aclientwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P29qxL0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P29qxL1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5ADVPCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27KS_qxL0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27KS_qxL1C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>flip_ReflexiveC69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C=u8_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P29qxL2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4a4_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4a4_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4a4_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4a4_3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5QPUSHC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C47Corelib7Classes?RelationClasses>impl_ReflexiveC69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27KS_qxL2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P29qxVE_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C5TAIL0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6TAIL12C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7src_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P27KS_qxVEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P28qxV_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdB6P28PQAAB6P26KS_qxVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C7k3_stepC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decc69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C8ADV_TAILC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6ROUNDAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C6ROUNDGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C4SCHKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C8ADV_NEXTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS36cls_ofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdB6C7PQAAB6C3RUNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCB6PQASCB:b64_specCAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5SMMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.
Local Ltac flia := L5FastLia.plia.
Local Ltac fd := first [assumption | flia].

Module PQAAB6C.
Import L5A L5SAR PQAKG3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation accA := PMSPA.accA.
Abbreviation kstr_at := (PQMA.kstr_at RSEGS accA).
Abbreviation bvu x := (bv_unsigned x).
Abbreviation src_okA := (PQASA.src_okA RSEGS).
Import PQAKZ4.

(* [comment removed for export] *)
Definition N0 : Z := 0xbebe4.
Definition RA_SM : Z := 0xbec60.
Definition HEAD : Z := 0xbed40.
Definition RBPC : Z := 0xbed50.
Definition QHEAD : Z := 0xbedc0.
Definition PBPC : Z := 0xf4640.
Definition RA_PB1 : Z := 0xbede4.
Definition ADVPC : Z := 0xbee08.
Definition TAILPC : Z := 0xbee2c.
Definition MSET : Z := 0x7f058.
Definition RA_MS : Z := 0xbee4c.
Definition TQHEAD : Z := 0xbee98.
Definition RA_PB2 : Z := 0xbeecc.
Definition RETIRE : Z := 0xbef44.
Definition RET : Z := 0xbeff4.
Definition ALPH : Z := 0x26613.

(* [comment removed for export] *)
Lemma to_bv_mod a : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_001 ())). Qed.
Lemma lor6 a b : 0 <= a <= 63 -> 0 <= b <= 63 -> 0 <= Z.lor a b <= 63.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_002 ())). Qed.
(* [comment removed for export] *)
Lemma div_rng a b k : 0 < b -> 0 <= a < b * k -> 0 <= a / b <= k - 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_003 ())). Qed.
Lemma a4_0 b : 0 <= b <= 255 -> 0 <= b / 4 <= 63.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_004 ())). Qed.
Lemma a4_1 b0 b1 : 0 <= b0 <= 255 -> 0 <= b1 <= 255 -> 0 <= Z.lor (b1 / 16) (((4611686018427387904 * b0) mod 2 ^ 64) / 288230376151711744) <= 63.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_005 ())). Qed.
Lemma a4_2 b1 b2 : 0 <= b1 <= 255 -> 0 <= b2 <= 255 -> 0 <= Z.lor (b2 / 64) (((1152921504606846976 * b1) mod 2 ^ 64) / 288230376151711744) <= 63.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_006 ())). Qed.
Lemma a4_3 b : 0 <= b <= 255 -> 0 <= Z.land b 63 <= 63.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_007 ())). Qed.
Lemma land7 x w : 0 <= x -> x mod 8 < w -> 0 <= Z.land x 7 <= w - 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_008 ())). Qed.
(* [comment removed for export] *)
Lemma b64len_eq n : 0 <= n -> PQVA.b64len n = 4 * (n / 3) + (if Z.eqb (n mod 3) 0 then 0 else n mod 3 + 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_009 ())). Qed.
Lemma b64len_rng n : 0 <= n -> 0 <= PQVA.b64len n <= 2 * n + 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_010 ())). Qed.
(* [comment removed for export] *)
Lemma u8_of_defined (Mx : mem) a : 0 <= a -> a + 1 <= 2 ^ 64 -> L5.defined Mx a 1 -> exists b, 0 <= b < 256 /\ L5.u8_at RSEGS Mx a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_011 ())). Qed.
Lemma u8_of_byte (Mx : mem) a v : byte_at Mx a v -> L5.u8_at RSEGS Mx a v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_012 ())). Qed.
Lemma byte_of_u8 (Mx : mem) a v : L5.u8_at RSEGS Mx a v -> Mx (Z_to_bv 64 a) <> None -> byte_at Mx a v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_013 ())). Qed.
(* [comment removed for export] *)
Lemma aacc3 (Mx : mem) F : F mod 32 = 0 -> 0 <= F -> byte_at Mx (F / 8 + 2147450880 + 4) 3 -> aacc Mx (F + 32) 3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_014 ())). Qed.
(* [comment removed for export] *)
Lemma alph_all : forallb (fun k => match rdn RSEGS (fun _ => None) (Z_to_bv 64 (157203 + Z.of_nat k)) 1 with Some [b] => Z.ltb (bv_unsigned b) 128 | _ => false end) (seq 0 65) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_015 ())). Qed.
Lemma alph_ok (Mx : mem) k : L5.img_clear Mx 65536 1409024 -> 0 <= k <= 64 -> exists b, 0 <= b <= 127 /\ L5.u8_at RSEGS Mx (157203 + k) b.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) [] (Mh_0270_blobs1.kr_b_016 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Hypothesis GAP : PMAGAP.rt_img_gap HI.
Hypothesis PBC : PQASCA.pb_specCA RSEGS AD L ar HI 0xf4640.

Lemma Hh2 : 1 <= PQASA.B64_H <= 16.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"] (Mh_0270_blobs1.kr_b_017 ())). Qed.

(* [comment removed for export] *)
Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (V2 cls r o q n SM g : Z) (x : PM.vstr) (kbs : list Z).
Local Notation sp := (V2 + cls).
Local Notation spc := (V2 - 160).
Local Notation W := ([(o, 24)] : list L5.range).
Local Notation BX0 := (PM.vs_own x).
Local Notation NB := (PQVA.b64len n).
Hypothesis Hcls : cls = 0 \/ cls = 16.
Hypothesis V32 : V2 mod 32 = 0.
Hypothesis HH : ri_inv HI (BX0 ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r PQASA.B64_H.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM PQASA.B64_H FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 q.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 (q + n).
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 ALPH.
Hypothesis A13 : getr R (reg 13) = Z_to_bv 64 o.
Hypothesis Hn : 0 <= n < 2 ^ 26.
Hypothesis SRC0 : src_okA L HI M LBX FF q n.
Hypothesis Hqo : q + n <= o \/ o + 24 <= q.
Hypothesis AO : PMSPA.aobjA FF o 24.
Hypothesis O8 : o mod 8 = 0.
Hypothesis KS : kstr_at M o x.
Hypothesis KC : NEM.kcontent RSEGS M o x kbs.
Hypothesis KOK : PQMA.ks_ok SM x g.
Hypothesis SMX : SM <= PQASA.SMMAX.
Hypothesis HSM : PM.vs_size x + NB <= SM.
Hypothesis BASE : PMSTA.base_okA RSEGS AD M.
Hypothesis CR : PMSP.credit_le (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (x' : PM.vstr) (g' : Z) (cr' : credit) (ds : list Z),
    regs_preserved R R' -> kstr_at M' o x' -> NEM.kcontent RSEGS M' o x' (kbs ++ ds) -> NEM.ascii ds -> PQMA.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + NB ->
    L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr PQASA.B64_H) W M M' ->
    PMSP.credit_keep cr cr' (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x' g')) ->
    model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
    ri_inv HI (PM.vs_own x' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Local Notation OWN := (PQAKS3.own13 sp R).
(* [comment removed for export] *)
Definition KCA (My : mem) (y : PM.vstr) (ys : list Z) : Prop := NEM.kcontent RSEGS My o y (kbs ++ ys) /\ NEM.ascii ys.
Local Notation OC := (PQAKS3.ocell13 sp).

(* [comment removed for export] *)
Lemma o_facts : 7036928 <= o /\ o + 24 <= ahl_ceil ar /\ o + 24 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= o \/ o + 24 <= 2147446784).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_018 ())). Qed.
Lemma wappW : PMKA.wapp W.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_019 ())). Qed.
(* [comment removed for export] *)
Local Notation "'GX' f" := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r PQASA.B64_H BX0 W HH AM K0 ENT FRM FRS Hh2 wappW) (at level 10, f at level 9, only parsing).

Lemma sp_facts : 140735332487264 + 16 <= V2 /\ V2 + cls <= 140737488355328 /\ (V2 + cls) mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_020 ())). Qed.
Lemma V2_lo : 140735332487360 <= V2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_021 ())). Qed.
Lemma HSPCf : sp - 2048 <= spc /\ spc mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_022 ())). Qed.
Lemma x_facts : 0 <= PM.vs_size x <= SM /\ 0 <= g.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_023 ())). Qed.
Lemma nb_facts : 0 <= NB <= 2 * n + 1 /\ NB = 4 * (n / 3) + (if Z.eqb (n mod 3) 0 then 0 else n mod 3 + 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_024 ())). Qed.
Lemma ceil_hi : 0x6b6000 <= ahl_ceil ar.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_025 ())). Qed.

(* [comment removed for export] *)
Lemma src_rng : 0 <= q /\ q + n <= 2 ^ 47.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_026 ())). Qed.
(* [comment removed for export] *)
Definition srccls (a : Z) : Prop :=
  in_block LBX a \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a) \/ in_fframe FF a
  \/ (exists f, In f FF /\ in_shadow_of (ff_addr f) (ff_bytes (ff_class f)) a) \/ (exists b, In b LBX /\ in_shadow_of (fst b) (snd b) a).
Lemma srccls_aclient a LB' FFx spx scr : srccls a -> incl LBX LB' -> incl FF FFx -> aclient L ar LB' FFx spx scr a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_027 ())). Qed.
(* [comment removed for export] *)
Lemma src_xfer (M1 M3 : mem) LB' FFx LK1 cr1 Aw1 V3 :
  src_okA L HI M1 LBX FF q n -> incl FF FFx -> ri_inv HI LB' FFx LK1 cr1 Aw1 M3 V3 ->
  (forall a, 0 <= a < 2 ^ 64 -> srccls a -> (q <= a < q + n \/ in_shadow_of q n a) -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  src_okA L HI M3 LBX FF q n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_028 ())). Qed.
(* [comment removed for export] *)
Lemma src_where (M1 : mem) LB' FFx LK1 cr1 Aw1 V1 : src_okA L HI M1 LBX FF q n -> ri_inv HI LB' FFx LK1 cr1 Aw1 M1 V1 -> incl LBX LB' -> incl FF FFx -> 0 < n ->
  forall a, (q <= a < q + n \/ in_shadow_of q n a) ->
  (a < ahl_ceil ar /\ (a < o \/ o + 24 <= a) /\ (a < BIGSHADOW_LO \/ BIGSHADOW_HI <= a)) \/ (BIGSHADOW_LO <= a < BIGSHADOW_HI /\ (a < o \/ o + 24 <= a)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_029 ())). Qed.

(* [comment removed for export] *)
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK Aw sp (PMSPA.pm_scr PQASA.B64_H) spc (sp - 104) sp OC OWN F fl 0 LK2 M2 model2 cr BX0.
Hypothesis APART : forall a n0 sp0 scr0, (forall i, 0 <= i < n0 -> aclient L ar (BX0 ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n0 ->
         (a + n0 <= F \/ F + ff_bytes 0 <= a) /\ (a + n0 <= F / 8 + SB \/ F / 8 + SB + ff_bytes 0 / 8 <= a) /\ (a + n0 <= fl \/ fl + 1 <= a).
Local Notation FF' := ((F, 0, spc + 32) :: FF).
(* [comment removed for export] *)
Local Notation GM := (PQAKR3.g_mem L ar HI M model LBX FF LK Aw sp PQASA.B64_H W spc OWN 0 F).
Local Notation "'GF' f" := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r PQASA.B64_H BX0 W HH AM K0 ENT FRM FRS Hh2 wappW spc (sp - 104) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Definition vals (j : nat) : Z :=
  match j with 2%nat => spc | 3%nat => pa_gp AD | 4%nat => hl_tp L | 8%nat => sp | 9%nat => spc | 19%nat => o | 20%nat => ALPH | 27%nat => 2147450880 | _ => 0 end.
Definition IXP : list nat := [2; 3; 4; 8; 9; 19; 20; 27]%nat.
Local Notation REGSP := (regl IXP vals).
(* [comment removed for export] *)
Definition FRAM (Mx : mem) : Prop :=
  L5.u64_at RSEGS Mx spc 0 /\ L5.u64_at RSEGS Mx (spc + 8) F /\ L5.u64_at RSEGS Mx (spc + 16) F /\ L5.u64_at RSEGS Mx (spc + 24) (F / 8 + 2147450880)
  /\ L5.u8_at RSEGS Mx (F / 8 + 2147450880 + 4) 3 /\ L5.u8_at RSEGS Mx (F / 8 + 2147450880 + 6) 4.

(* [comment removed for export] *)
Ltac pf BIx :=
  destruct ((GF PQAKR3.g_pfacts) _ _ _ _ _ _ BIx) as ((PF1 & PF2 & PF3 & PF4 & _) & (FD & FW & FSW & FLU & FLW) & (PL1 & PL2 & PL3 & PL4) & (SW & OWNV & PS1 & PS2 & PS3 & PS4) & (CSB & CUAR & IMGC) & (AVSH & AVF & AVS));
  change (ff_bytes 0) with 64 in *; change (64 / 8) with 8 in *.

(* [comment removed for export] *)
Lemma KSKEEP LB1 FFx spx scr (M1 M3 : mem) y :
  (forall f, In f FFx -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) -> (forall b, In b LB1 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  L5SAR.ek L ar LB1 FFx spx scr [] M1 M3 -> incl (PM.vs_own y) LB1 -> PMSPA.aobjA FFx o 24 -> kstr_at M1 o y -> kstr_at M3 o y.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_030 ())). Qed.

(* [comment removed for export] *)
Lemma KCKEEP LB1 FFx spx scr (M1 M3 : mem) y ys :
  (forall f, In f FFx -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) -> (forall b, In b LB1 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  L5SAR.ek L ar LB1 FFx spx scr [] M1 M3 -> incl (PM.vs_own y) LB1 -> PMSPA.aobjA FFx o 24 -> kstr_at M1 o y -> KCA M1 y ys -> KCA M3 y ys.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_031 ())). Qed.

(* [comment removed for export] *)
Definition WPF (a : Z) : Prop := (sp - PMSPA.pm_scr PQASA.B64_H <= a < sp) \/ (F <= a < F + 64) \/ (F / 8 + SB <= a < F / 8 + SB + 8).

(* [comment removed for export] *)
Lemma GEK BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) (Wp : Z -> Prop) :
  GM BX1 M1 model1 LK1 Aw1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall a, Wp a -> WPF a) ->
  L5SAR.ek L ar (BX1 ++ LBX) FF sp (PMSPA.pm_scr PQASA.B64_H) [] M1 M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_032 ())). Qed.

(* [comment removed for export] *)
Lemma KSX BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) (Wp : Z -> Prop) y :
  GM BX1 M1 model1 LK1 Aw1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall a, Wp a -> WPF a) ->
  incl (PM.vs_own y) BX1 -> kstr_at M1 o y -> kstr_at M3 o y.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_033 ())). Qed.

Lemma KCX BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) (Wp : Z -> Prop) y ys :
  GM BX1 M1 model1 LK1 Aw1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall a, Wp a -> WPF a) ->
  incl (PM.vs_own y) BX1 -> kstr_at M1 o y -> KCA M1 y ys -> KCA M3 y ys.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_034 ())). Qed.

(* [comment removed for export] *)
Lemma OAP : (o + 24 <= F \/ F + 64 <= o) /\ (o / 8 + SB + 3 <= F / 8 + SB \/ F / 8 + SB + 8 <= o / 8 + SB) /\ (o + 24 <= fl \/ fl + 1 <= o).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_035 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma SRC_WPF BX1 M1 model1 LK1 Aw1 cr1 a : GM BX1 M1 model1 LK1 Aw1 cr1 -> src_okA L HI M1 LBX FF q n -> 0 < n ->
  srccls a -> (q <= a < q + n \/ in_shadow_of q n a) -> ~ WPF a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_036 ())). Qed.
(* [comment removed for export] *)
Lemma SRCX BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) model3 (Wp : Z -> Prop) :
  GM BX1 M1 model1 LK1 Aw1 cr1 -> src_okA L HI M1 LBX FF q n -> 0 < n ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall a, Wp a -> WPF a) ->
  GM BX1 M3 model3 LK1 Aw1 cr1 -> src_okA L HI M3 LBX FF q n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_037 ())). Qed.
(* [comment removed for export] *)
Lemma SRCC BX1 M1 model1 LK1 Aw1 cr1 (M6 : mem) LB6 LK6 cr6 Aw6 V6 scr :
  GM BX1 M1 model1 LK1 Aw1 cr1 -> src_okA L HI M1 LBX FF q n -> 0 < n ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF' spc scr a -> L5.outside W a -> ~ WPF a -> M6 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  0 <= scr -> ahl_ceil ar <= spc - scr ->
  ri_inv HI LB6 FF' LK6 cr6 Aw6 M6 V6 -> src_okA L HI M6 LBX FF q n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_038 ())). Qed.

(* [comment removed for export] *)
Lemma SRCB BX1 M1 model1 LK1 Aw1 cr1 c :
  GM BX1 M1 model1 LK1 Aw1 cr1 -> src_okA L HI M1 LBX FF q n -> q <= c < q + n ->
  let MV := mrestrict (ahid Aw1 model1) M1 in
  (exists b, 0 <= b <= 255 /\ L5.u8_at RSEGS MV c b)
  /\ (L5KA.zeros_at MV (c / 8 + 2147450880) 1 \/ (exists v, 1 <= v <= 7 /\ L5.u8_at RSEGS MV (c / 8 + 2147450880) v /\ c mod 8 < v))
  /\ 0 <= c /\ c + 1 <= 2 ^ 47 /\ (c + 1 <= F \/ F + 64 <= c).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_039 ())). Qed.

(* [comment removed for export] *)
Lemma FRAM_keep (Ma Mb : mem) :
  7036928 <= F -> F + 64 <= 2 ^ 47 ->
  (forall a, spc <= a < spc + 32 -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  (forall a, F / 8 + 2147450880 + 4 <= a < F / 8 + 2147450880 + 7 -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  FRAM Ma -> FRAM Mb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_040 ())). Qed.
(* [comment removed for export] *)
Lemma FRAM_vis BX1 M1 model1 LK1 Aw1 cr1 : GM BX1 M1 model1 LK1 Aw1 cr1 -> FRAM M1 -> FRAM (mrestrict (ahid Aw1 model1) M1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_041 ())). Qed.
(* [comment removed for export] *)
Lemma FRAM_unvis BX1 M3 model3 LK1 Aw1 cr1 (M3v : mem) : GM BX1 M3 model3 LK1 Aw1 cr1 -> mrestrict (ahid Aw1 model3) M3 = M3v -> FRAM M3v -> FRAM M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_042 ())). Qed.
(* [comment removed for export] *)
Lemma FB_vis BX1 M1 model1 LK1 Aw1 cr1 a b : GM BX1 M1 model1 LK1 Aw1 cr1 -> F <= a -> a + 1 <= F + 64 ->
  (L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) a b <-> L5.u8_at RSEGS M1 a b).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_043 ())). Qed.

Lemma FRAM24 (Mx : mem) : FRAM Mx -> L5.u64_at RSEGS Mx (spc + 24) (F / 8 + 2147450880).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_044 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma FIN M6 model6 LK6 Aw6 cr6 (y : PM.vstr) (ys : list Z) (gy : Z) (fx6 : FPState) R6 :
  GM (PM.vs_own y) M6 model6 LK6 Aw6 cr6 -> kstr_at M6 o y -> KCA M6 y ys -> PQMA.ks_ok SM y gy -> PM.vs_size y = PM.vs_size x + NB ->
  PMSP.credit_keep cr cr6 (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) ->
  REGSP R6 -> getr R6 (reg 22) = Z_to_bv 64 F -> getr R6 (reg 23) = Z_to_bv 64 F -> L5.u64_at RSEGS M6 (spc + 24) (F / 8 + 2147450880) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 RETIRE M6 model6) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_045 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma PBCALL My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (c ra : Z) :
  GM (PM.vs_own y) My modely LKy Awy cry -> kstr_at My o y -> KCA My y ys -> PQMA.ks_ok SM y gy -> PM.vs_size y < SM ->
  PMSP.credit_le (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) cry ->
  getr R5 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> REGSP R5 ->
  getr R5 (reg 10) = Z_to_bv 64 o -> getr R5 (reg 11) = Z_to_bv 64 c -> 0 <= c < 128 ->
  FRAM My -> 0 < n -> src_okA L HI My LBX FF q n ->
  (forall (fx6 : FPState) R6 M6 model6 LK6 Aw6 (y' : PM.vstr) (ys' : list Z) (gy' : Z) cr6,
      GM (PM.vs_own y') M6 model6 LK6 Aw6 cr6 -> kstr_at M6 o y' -> KCA M6 y' ys' -> PQMA.ks_ok SM y' gy' -> PM.vs_size y' = PM.vs_size y + 1 ->
      PMSP.credit_keep cry cr6 (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y' gy')) ->
      regs_preserved R5 R6 -> REGSP R6 -> FRAM M6 -> src_okA L HI M6 LBX FF q n ->
      (forall a, F + 32 <= a < F + 56 -> M6 (Z_to_bv 64 a) = My (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 ra M6 model6) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 PBPC My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_046 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma IMGW BX1 M1 model1 LK1 Aw1 cr1 : GM BX1 M1 model1 LK1 Aw1 cr1 -> L5.img_clear (mrestrict (ahid Aw1 model1) M1) 65536 1409024.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_047 ())). Qed.
(* [comment removed for export] *)
Lemma A4_keep (Ma Mb : mem) (hi : Z) : 7036928 <= F -> F + 64 <= 2 ^ 47 ->
  (forall a, F + 48 <= a < F + 52 -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  (forall j', 0 <= j' <= hi -> exists a, 0 <= a <= 63 /\ L5.u8_at RSEGS Ma (F + 48 + j') a) -> hi <= 3 ->
  (forall j', 0 <= j' <= hi -> exists a, 0 <= a <= 63 /\ L5.u8_at RSEGS Mb (F + 48 + j') a).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_048 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma TQBODY My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (j cnt m : Z) :
  GM (PM.vs_own y) My modely LKy Awy cry -> kstr_at My o y -> KCA My y ys -> PQMA.ks_ok SM y gy -> PM.vs_size y < SM ->
  PMSP.credit_le (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) cry ->
  REGSP R5 -> getr R5 (reg 18) = Z_to_bv 64 m -> getr R5 (reg 21) = Z_to_bv 64 cnt -> getr R5 (reg 22) = Z_to_bv 64 (F + 48 + j) -> getr R5 (reg 23) = Z_to_bv 64 (F + 48 + j) ->
  0 <= j <= 2 -> FRAM My -> 0 < n -> src_okA L HI My LBX FF q n ->
  (forall j', 0 <= j' <= 2 -> exists a, 0 <= a <= 63 /\ L5.u8_at RSEGS My (F + 48 + j') a) ->
  (forall (fx8 : FPState) R8 M8 model8 LK8 Aw8 (y' : PM.vstr) (ys' : list Z) (gy' : Z) cr8,
      GM (PM.vs_own y') M8 model8 LK8 Aw8 cr8 -> kstr_at M8 o y' -> KCA M8 y' ys' -> PQMA.ks_ok SM y' gy' -> PM.vs_size y' = PM.vs_size y + 1 ->
      PMSP.credit_keep cry cr8 (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y' gy')) ->
      REGSP R8 -> getr R8 (reg 18) = Z_to_bv 64 m -> getr R8 (reg 21) = Z_to_bv 64 cnt -> getr R8 (reg 22) = Z_to_bv 64 (F + 48 + j) -> getr R8 (reg 23) = Z_to_bv 64 (F + 48 + j) ->
      FRAM M8 -> src_okA L HI M8 LBX FF q n -> (forall j', 0 <= j' <= 2 -> exists a, 0 <= a <= 63 /\ L5.u8_at RSEGS M8 (F + 48 + j') a) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx8 R8 RA_PB2 M8 model8) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 TQHEAD My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_049 ())). Qed.

(* [comment removed for export] *)
Lemma TPUSH (mn : nat) : forall My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (j cnt : Z),
  GM (PM.vs_own y) My modely LKy Awy cry -> kstr_at My o y -> KCA My y ys -> PQMA.ks_ok SM y gy -> PM.vs_size y + Z.of_nat mn + 1 = PM.vs_size x + NB ->
  PMSP.credit_keep cr cry (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) ->
  REGSP R5 -> getr R5 (reg 18) = Z_to_bv 64 (Z.of_nat mn + 1) -> getr R5 (reg 21) = Z_to_bv 64 cnt -> 0 <= cnt -> cnt + Z.of_nat mn + 1 <= 2 ^ 40 ->
  getr R5 (reg 22) = Z_to_bv 64 (F + 48 + j) -> getr R5 (reg 23) = Z_to_bv 64 (F + 48 + j) -> 0 <= j -> j + Z.of_nat mn <= 2 ->
  FRAM My -> 0 < n -> src_okA L HI My LBX FF q n ->
  (forall j', 0 <= j' <= 2 -> exists a, 0 <= a <= 63 /\ L5.u8_at RSEGS My (F + 48 + j') a) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 TQHEAD My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_050 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma TAIL0 My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (cnt : Z) :
  GM (PM.vs_own y) My modely LKy Awy cry -> kstr_at My o y -> KCA My y ys -> PQMA.ks_ok SM y gy -> PM.vs_size y = PM.vs_size x + NB ->
  PMSP.credit_keep cr cry (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) ->
  REGSP R5 -> getr R5 (reg 21) = Z_to_bv 64 cnt -> 0 <= cnt < 2 ^ 64 -> getr R5 (reg 22) = Z_to_bv 64 (F + 32) -> getr R5 (reg 23) = Z_to_bv 64 (F + 48) -> getr R5 (reg 26) = Z_to_bv 64 0 ->
  FRAM My -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 TAILPC My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_051 ())). Qed.

(* [comment removed for export] *)
Lemma TAIL12 My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (i cnt : Z) :
  GM (PM.vs_own y) My modely LKy Awy cry -> kstr_at My o y -> KCA My y ys -> PQMA.ks_ok SM y gy -> PM.vs_size y + i + 1 = PM.vs_size x + NB ->
  PMSP.credit_keep cr cry (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) ->
  REGSP R5 -> getr R5 (reg 21) = Z_to_bv 64 cnt -> 0 <= cnt -> cnt + 3 <= 2 ^ 40 -> getr R5 (reg 22) = Z_to_bv 64 (F + 32) -> getr R5 (reg 23) = Z_to_bv 64 (F + 48) ->
  getr R5 (reg 26) = Z_to_bv 64 i -> 1 <= i <= 2 ->
  FRAM My -> 0 < n -> src_okA L HI My LBX FF q n ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 TAILPC My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_052 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MST (My : mem) (modely : Model) (LKy : list fframe) (Awy : list (Z * Z)) (cry : credit) (y : PM.vstr) (ys : list Z) (gy : Z) (Ry : bvmap 5 word) (c cnt sz : Z) : Prop :=
  GM (PM.vs_own y) My modely LKy Awy cry /\ kstr_at My o y /\ KCA My y ys /\ PQMA.ks_ok SM y gy /\ PM.vs_size y = PM.vs_size x + sz
  /\ PMSP.credit_keep cr cry (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy))
  /\ REGSP Ry /\ getr Ry (reg 18) = Z_to_bv 64 (q + n) /\ getr Ry (reg 21) = Z_to_bv 64 cnt /\ getr Ry (reg 22) = Z_to_bv 64 (F + 32) /\ getr Ry (reg 23) = Z_to_bv 64 (F + 48)
  /\ getr Ry (reg 24) = Z_to_bv 64 c /\ FRAM My /\ src_okA L HI My LBX FF q n /\ 0 <= cnt <= sz.

(* [comment removed for export] *)
Lemma MST_piece My modely LKy Awy cry y ys gy Ry c cnt sz (M3 : mem) model3 (R3 : bvmap 5 word) (Wp : Z -> Prop) (KSl : list nat) (c3 : Z) :
  MST My modely LKy Awy cry y ys gy Ry c cnt sz -> 0 < n ->
  GM (PM.vs_own y) M3 model3 LKy Awy cry ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = My (Z_to_bv 64 a)) -> (forall a, Wp a -> WPF a) ->
  (forall a, Wp a -> ~ (spc <= a < spc + 32) /\ ~ (F / 8 + SB + 4 <= a < F / 8 + SB + 7)) ->
  (forall k, In k KSl -> getr R3 (reg k) = getr Ry (reg k)) -> subl IXP KSl = true -> subl [18; 21; 22; 23]%nat KSl = true -> getr R3 (reg 24) = Z_to_bv 64 c3 ->
  MST M3 model3 LKy Awy cry y ys gy R3 c3 cnt sz.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_053 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma QBODY My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (c cnt sz j m : Z) :
  MST My modely LKy Awy cry y ys gy R5 c cnt sz -> PM.vs_size y < SM -> 0 < n ->
  getr R5 (reg 25) = Z_to_bv 64 (F + 48 + j) -> getr R5 (reg 26) = Z_to_bv 64 m -> 0 <= j <= 3 ->
  (forall j', 0 <= j' <= 3 -> exists a, 0 <= a <= 63 /\ L5.u8_at RSEGS My (F + 48 + j') a) ->
  (forall (fx8 : FPState) R8 M8 model8 LK8 Aw8 (y' : PM.vstr) (ys' : list Z) (gy' : Z) cr8,
      MST M8 model8 LK8 Aw8 cr8 y' ys' gy' R8 c cnt (sz + 1) ->
      getr R8 (reg 25) = Z_to_bv 64 (F + 48 + j) -> getr R8 (reg 26) = Z_to_bv 64 m ->
      (forall j', 0 <= j' <= 3 -> exists a, 0 <= a <= 63 /\ L5.u8_at RSEGS M8 (F + 48 + j') a) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx8 R8 RA_PB1 M8 model8) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 QHEAD My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_054 ())). Qed.

(* [comment removed for export] *)
Lemma QPUSH (mn : nat) : forall My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (c cnt j : Z),
  MST My modely LKy Awy cry y ys gy R5 c cnt (cnt + j) -> 0 < n -> cnt + 4 <= NB ->
  getr R5 (reg 25) = Z_to_bv 64 (F + 48 + j) -> getr R5 (reg 26) = Z_to_bv 64 (Z.of_nat mn + 1) -> 0 <= j -> j + Z.of_nat mn = 3 ->
  (forall j', 0 <= j' <= 3 -> exists a, 0 <= a <= 63 /\ L5.u8_at RSEGS My (F + 48 + j') a) ->
  (forall (fx9 : FPState) R9 M9 model9 LK9 Aw9 (y' : PM.vstr) (ys' : list Z) (gy' : Z) cr9,
      MST M9 model9 LK9 Aw9 cr9 y' ys' gy' R9 c (cnt + 4) (cnt + 4) -> getr R9 (reg 26) = Z_to_bv 64 0 -> getr R9 (reg 14) = Z_to_bv 64 3 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 ADVPC M9 model9) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 QHEAD My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_055 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma SCHK My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (c cnt sz i : Z) :
  MST My modely LKy Awy cry y ys gy R5 c cnt sz -> 0 < n -> q <= c < q + n -> getr R5 (reg 26) = Z_to_bv 64 i -> getr R5 (reg 14) = Z_to_bv 64 3 ->
  (forall (fx6 : FPState) R6 M6 model6,
      MST M6 model6 LKy Awy cry y ys gy R6 c cnt sz -> getr R6 (reg 26) = Z_to_bv 64 i -> getr R6 (reg 14) = Z_to_bv 64 3 ->
      (forall a, F <= a < F + 64 -> M6 (Z_to_bv 64 a) = My (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 RBPC M6 model6) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 HEAD My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_056 ())). Qed.

(* [comment removed for export] *)
Lemma k3_step k : 0 <= k ->
  (k mod 3 <= 1 -> (k + 1) / 3 = k / 3 /\ (k + 1) mod 3 = k mod 3 + 1) /\ (k mod 3 = 2 -> (k + 1) / 3 = k / 3 + 1 /\ (k + 1) mod 3 = 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_057 ())). Qed.

(* [comment removed for export] *)
Lemma ROUNDA My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (c cnt i : Z) :
  MST My modely LKy Awy cry y ys gy R5 c cnt cnt -> 0 < n -> q <= c < q + n -> getr R5 (reg 26) = Z_to_bv 64 i -> getr R5 (reg 14) = Z_to_bv 64 3 -> 0 <= i <= 1 ->
  (forall (fx6 : FPState) R6 M6 model6,
      MST M6 model6 LKy Awy cry y ys gy R6 c cnt cnt -> getr R6 (reg 26) = Z_to_bv 64 (i + 1) -> getr R6 (reg 14) = Z_to_bv 64 3 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 ADVPC M6 model6) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 RBPC My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_058 ())). Qed.

(* [comment removed for export] *)
Lemma ROUNDG My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (c cnt : Z) :
  MST My modely LKy Awy cry y ys gy R5 c cnt cnt -> 0 < n -> q <= c < q + n -> getr R5 (reg 26) = Z_to_bv 64 2 -> getr R5 (reg 14) = Z_to_bv 64 3 -> cnt + 4 <= NB ->
  (forall (fx9 : FPState) R9 M9 model9 LK9 Aw9 (y' : PM.vstr) (ys' : list Z) (gy' : Z) cr9,
      MST M9 model9 LK9 Aw9 cr9 y' ys' gy' R9 c (cnt + 4) (cnt + 4) -> getr R9 (reg 26) = Z_to_bv 64 0 -> getr R9 (reg 14) = Z_to_bv 64 3 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 ADVPC M9 model9) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 RBPC My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_059 ())). Qed.

(* [comment removed for export] *)
Lemma ADV_TAIL My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (c cnt : Z) :
  MST My modely LKy Awy cry y ys gy R5 c cnt cnt -> 0 < n -> c + 1 = q + n -> cnt = 4 * (n / 3) ->
  getr R5 (reg 26) = Z_to_bv 64 (n mod 3) -> getr R5 (reg 14) = Z_to_bv 64 3 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 ADVPC My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_060 ())). Qed.

(* [comment removed for export] *)
Lemma ADV_NEXT My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (c cnt i : Z) :
  MST My modely LKy Awy cry y ys gy R5 c cnt cnt -> 0 < n -> q <= c -> c + 2 <= q + n ->
  getr R5 (reg 26) = Z_to_bv 64 i -> getr R5 (reg 14) = Z_to_bv 64 3 ->
  (forall (fx6 : FPState) R6 M6 model6,
      MST M6 model6 LKy Awy cry y ys gy R6 (c + 1) cnt cnt -> getr R6 (reg 26) = Z_to_bv 64 i -> getr R6 (reg 14) = Z_to_bv 64 3 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 HEAD M6 model6) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 ADVPC My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_061 ())). Qed.

(* [comment removed for export] *)
Lemma MAIN (dn : nat) : forall My modely LKy Awy cry (y : PM.vstr) (ys : list Z) (gy : Z) (fx5 : FPState) R5 (k : Z),
  MST My modely LKy Awy cry y ys gy R5 (q + k) (4 * (k / 3)) (4 * (k / 3)) -> 0 <= k -> k + 1 + Z.of_nat dn = n ->
  getr R5 (reg 26) = Z_to_bv 64 (k mod 3) -> getr R5 (reg 14) = Z_to_bv 64 3 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 HEAD My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_062 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma SETUP (fx1 : FPState) R2 :
  GM BX0 M2 model2 LK2 Aw cr -> L5SAR.ek L ar (BX0 ++ LBX) FF sp (PMSPA.pm_scr PQASA.B64_H) [] M M2 ->
  getr R2 (reg 2) = Z_to_bv 64 spc -> getr R2 (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R2 (reg 8) = Z_to_bv 64 sp ->
  getr R2 (reg 9) = Z_to_bv 64 spc -> getr R2 (reg 10) = Z_to_bv 64 F -> getr R2 (reg 18) = Z_to_bv 64 (q + n) -> getr R2 (reg 19) = Z_to_bv 64 o ->
  getr R2 (reg 20) = Z_to_bv 64 ALPH -> getr R2 (reg 24) = Z_to_bv 64 q -> getr R2 (reg 27) = Z_to_bv 64 2147450880 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R2 RA_SM M2 model2) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_063 ())). Qed.
End Frame.

(* [comment removed for export] *)
Ltac zl HV HS HC := clear - HV HS HC; Lia.lia.
Ltac enter_tac Aconc fxv MVv HRgp HRtp HV HS HC :=
  pose proof (LF2CBN( Aconc fxv R MVv (fun j : nat => match j with 2%nat => V2 | 34%nat => o | 39%nat => n | 40%nat => q | _ => 0 end) )) as P;
  L5SAR.feed P ltac:(fd);
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T18 & T19 & T20 & T24 & T27 & C27 & C26 & C25 & C24 & C23 & C22 & C21 & C20 & C19 & C18 & C9 & C8 & C1 & C0);
  apply ((GX PQAKR3.g_enter) spc (sp - 104) sp OC OWN 0 fxv fx1 R1 781204 781328 M1v);
  [ left; reflexivity | zl HV HS HC | exact (proj2 HSPCf) | zl HV HS HC | zl HV HS HC | zl HV HS HC | intros a Ha; unfold PQAKS3.ocell13 in Ha; clear - HV HS HC Ha; Lia.lia
  | intros Ma Mb OW AG; apply (PQAKS3.own13_agree sp R Ma Mb ltac:(zl HV HS HC) ltac:(zl HV HS HC) OW AG)
  | exact MS1 | exact MG1 | intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; clear - HV HS HC X; Lia.lia]
  | intros M1 VIS1 AV; unfold PQAKS3.own13;
    repeat match goal with |- _ /\ _ => split end;
    (match goal with |- L5.u64_at _ _ ?a0 ?v0 => apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a0 v0 (AV a0 8 ltac:(zl HV HS HC) ltac:(zl HV HS HC)) ltac:(zl HV HS HC) ltac:(zl HV HS HC))) end; rewrite VIS1;
     match goal with |- L5.u64_at _ _ ?a _ => first [ replace a with (V2 + 8) by (zl HV HS HC); assumption
        | replace a with V2 by (zl HV HS HC); assumption
        | replace a with (V2 - 8) by (zl HV HS HC); assumption
        | replace a with (V2 - 16) by (zl HV HS HC); assumption
        | replace a with (V2 - 24) by (zl HV HS HC); assumption
        | replace a with (V2 - 32) by (zl HV HS HC); assumption
        | replace a with (V2 - 40) by (zl HV HS HC); assumption
        | replace a with (V2 - 48) by (zl HV HS HC); assumption
        | replace a with (V2 - 56) by (zl HV HS HC); assumption
        | replace a with (V2 - 64) by (zl HV HS HC); assumption
        | replace a with (V2 - 72) by (zl HV HS HC); assumption
        | replace a with (V2 - 80) by (zl HV HS HC); assumption
        | replace a with (V2 - 88) by (zl HV HS HC); assumption
        | replace a with (V2 - 96) by (zl HV HS HC); assumption
        | replace a with (V2 - 104) by (zl HV HS HC); assumption ] end)
  | exact T2 | apply KS1; inl | exact T1 | reflexivity | zl HV HS HC |];
  intros R2 M2 model2 F fl LK2 G APART LM2 EK2 G10 RP2 _;
  apply (SETUP F fl LK2 M2 model2 G APART fx1 R2 LM2 EK2);
  [ rewrite (L5SAR.cs_of_preserved _ _ 2%nat RP2 ltac:(inl)); exact T2
  | rewrite (L5SAR.cs_of_preserved _ _ 3%nat RP2 ltac:(inl)); rewrite (KS1 3%nat) by inl; exact HRgp
  | rewrite (L5SAR.cs_of_preserved _ _ 4%nat RP2 ltac:(inl)); rewrite (KS1 4%nat) by inl; exact HRtp
  | rewrite (L5SAR.cs_of_preserved _ _ 8%nat RP2 ltac:(inl)); rewrite T8; f_equal; zl HV HS HC
  | rewrite (L5SAR.cs_of_preserved _ _ 9%nat RP2 ltac:(inl)); exact T9
  | exact G10
  | rewrite (L5SAR.cs_of_preserved _ _ 18%nat RP2 ltac:(inl)); rewrite T18; f_equal; clear; Lia.lia
  | rewrite (L5SAR.cs_of_preserved _ _ 19%nat RP2 ltac:(inl)); exact T19
  | rewrite (L5SAR.cs_of_preserved _ _ 20%nat RP2 ltac:(inl)); exact T20
  | rewrite (L5SAR.cs_of_preserved _ _ 24%nat RP2 ltac:(inl)); exact T24
  | rewrite (L5SAR.cs_of_preserved _ _ 27%nat RP2 ltac:(inl)); exact T27 ].

Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R N0 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_064 ())). Qed.
End Run.

(* [comment removed for export] *)
Theorem b64_ok : PQASCB.b64_specCA RSEGS AD L ar HI 0xbebe4 0x26613.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdB6C ()) ["WithHeap"] (Mh_0270_blobs1.kr_b_065 ())). Qed.

End WithHeap.
End PQAAB6C.

End PnAAdB6C.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0009. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require UbjRef.
Module PnAAdBa.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0009. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObjA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAHarnessKit5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemFrameA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKSlotA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKCallA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKSlotNA3bN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201.PnAAdBaP1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201.PnAAdBaP2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0009.Na0_code_rb09ac_b09b0.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdBa () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2lec69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA4own8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA6ocell8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z6of_natC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;pot_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA4PMEAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8pot_encAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA7ly_costC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_b_linC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=hl_b_overheadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8sink_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA7PMEA_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA@sink_potA_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA7spa_potC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA7hv_costC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7enc_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA;epot_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7pot_aeAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA9pot_splitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA2CRC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5VIS_HC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA:own8_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA8sp_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ec_stateAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092;PnQStaticsA5PQSTA7err_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_KBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_ctxC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA5HFR80C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA4GOCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA4GOWNC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA5akeptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_appbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN6n_memGC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5binvNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4EVISC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_WAC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6frb_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6brb_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_visitorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lvec_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN>kcontent_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7blk_outC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemFrameA5NEMFA9enc_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemFrameA5NEMFA:sink_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemFrameA5NEMFA>ec_state_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN8err_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA5xinvAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lvec_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA5oa_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_DVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9AOFF_DESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8AOFF_KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_LVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_ncwC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA7xinv_ekC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_offC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3s_gC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_permC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_setC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8s_set_idC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib7Sorting;PermutationDPermutation_app_tailC69OSSVerify5KrLib7Mh_02569PnAKRunA16PQAKRA7ri_permC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK=blk_obj_apartC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_app_asciiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_restC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA<aobjA_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8hdr_contC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8le_max_lC56Stdlib6ZArith6BinInt1Z3maxC69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5zsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6edepthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA9step_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5aeownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ndestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP18PQAABAP17alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38word_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG37bvu_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP18PQAABAP1:qvaX0_concC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA6xpieceC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC47Corelib4Init5Logic6eq_symC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARBpreserved_by_indexC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA4KFINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN7n_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA4valsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_retC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA3IXAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP18PQAABAP18KS_qvaX0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rb09ac_b09b07W_b0868C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rb09ac_b09b07F_b0868C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rb09ac_b09b07D_b0868C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N8pb_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N6pb_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA5xcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN9n_call_sCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN4n_oaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP2:qvaVq_concC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP2:qvaKq_concC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA3FINC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA5NPUSHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP28KS_qvaVqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP28KS_qvaKqC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orC69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38aobj_subC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC69OSSVerify5KrLib7Mh_0213:PnSpecsAXl6PQSAXL6lvl_eoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_kbgC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA3xlvC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Nat2Z7inj_addC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_tC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ndest_appC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rc69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA6OPENCHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA3ENCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN=n_call_lvpushC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA3IXDC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Zc69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA3S2VC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP2:qvaVp_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP2:qvaKp_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u32_at_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA6PUSHLVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA7oec_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP28KS_qvaVpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP28PQAABAP28KS_qvaKpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN7n_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN6n_memEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP18PQAABAP19qvaA_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u64_at_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA5DISP1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBaP18PQAABAP17KS_qvaAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA5xinv0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8args_ec4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8pre_pushC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation@Permutation_reflC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;evis_of_encC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBa6PQAABA3RUNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ@qa_v_begin_arrayC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVABv_begin_array_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAABA.
Import L5A L5SAR PQAKS3N PQAKC3N PQAKG3 PQAKSNN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac flia := solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ].
Ltac fd := first [assumption | flia].
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AQ := PnLayoutQA.QADDR_A.
Abbreviation AE := NemLayoutA.NEADDR_A.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation adaptor_at := (PQMA.adaptor_at RSEGS AD accA annA (qa_vp_adaptor AQ)).
Abbreviation bvu x := (bv_unsigned x).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) [] (Mh_0270_blobs1.kr_b_066 ())). Qed.

(* [comment removed for export] *)
Definition own8 (sp : Z) (R : bvmap 5 word) (M : mem) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (bvu (getr R (reg 1))) /\ L5.u64_at RSEGS M (sp - 16) (bvu (getr R (reg 8))) /\ L5.u64_at RSEGS M (sp - 24) (bvu (getr R (reg 9)))
  /\ L5.u64_at RSEGS M (sp - 32) (bvu (getr R (reg 18))) /\ L5.u64_at RSEGS M (sp - 40) (bvu (getr R (reg 19))) /\ L5.u64_at RSEGS M (sp - 48) (bvu (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (sp - 56) (bvu (getr R (reg 21))) /\ L5.u64_at RSEGS M (sp - 64) (bvu (getr R (reg 22))).
Definition ocell8 (sp : Z) (a : Z) : Prop := sp - 64 <= a < sp.
Lemma own8_agree sp R M1 M1' : 0 <= sp - 64 -> sp <= 2 ^ 64 ->
  own8 sp R M1 -> (forall a, ocell8 sp a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own8 sp R M1'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) [] (Mh_0270_blobs1.kr_b_067 ())). Qed.
Lemma HFR80 : 16 <= 80 <= 2048 /\ 80 mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) [] (Mh_0270_blobs1.kr_b_068 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
(* [comment removed for export] *)
Hypothesis PBC : PQASCA.pb_specCA RSEGS AD L ar HI 0xf4640.
Hypothesis LVP : PQSAXL.lvpush_spec RSEGS AD L ar HI 0xb84e8.
Hypothesis VBE : NECSA.v_begin_arr_spec RSEGS AD AQ AAD AE L ar HI (NESKA.PMEA L).

Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX0 : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (sp r oa ov osk oec cat len tg ctx : Z) (sa : PQMA.ast) (kbb : list Z) (en : NEM.enc) (k : NESK.sink) (b e : bool).
Local Notation spc := (sp - 80).
(* [comment removed for export] *)
Local Notation ESO := (NEM.enc_own en ++ NESK.sink_own k).
Local Notation LBX := (ESO ++ LBX0).
Local Notation ST0 := (NEMA.AEST sa kbb en k).
Hypothesis SP16 : sp mod 16 = 0.
Hypothesis HH : ri_inv HI ((PQMA.aown sa ++ ESO) ++ LBX0) FF LK cr Aw M (vml_of model).   (* [comment removed for export] *)
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r PNVA.VIS_H.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM PNVA.VIS_H FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 oa.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 len.
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 tg.
Hypothesis A13 : getr R (reg 13) = Z_to_bv 64 ctx.
Hypothesis A14 : getr R (reg 14) = Z_to_bv 64 oec.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis Htg : 0 <= tg < 2 ^ 64.
Hypothesis Hctx : 0 <= ctx < 2 ^ 64.
Hypothesis AO : PMSPA.aobjA FF oa PQMA.ASIZE.
Hypothesis O8 : oa mod 8 = 0.
Hypothesis AOV : PMSPA.aobjA FF ov 56.
Hypothesis OV8 : ov mod 8 = 0.
Hypothesis AOSK : PMSPA.aobjA FF osk 24.
Hypothesis OK8 : osk mod 8 = 0.
Hypothesis AOEC : PMSPA.aobjA FF oec 16.
Hypothesis OE8 : oec mod 8 = 0.
Hypothesis APT : oa + PQMA.ASIZE <= ov \/ ov + 56 <= oa.
Hypothesis APT2 : oa + PQMA.ASIZE <= osk \/ osk + 24 <= oa.
Hypothesis APT3 : oa + PQMA.ASIZE <= oec \/ oec + 16 <= oa.
Hypothesis APT4 : ov + 56 <= osk \/ osk + 24 <= ov.
Hypothesis APT5 : oec + 16 <= ov \/ ov + 56 <= oec.
Hypothesis APT6 : oec + 16 <= osk \/ osk + 24 <= oec.
Hypothesis AA : adaptor_at M oa ov sa.
Hypothesis OACC : accA M oa PQMA.ASIZE.
Hypothesis AOK : PQMA.adaptor_ok sa.
Hypothesis VIS : EVIS M ov.
Hypothesis BASE : PMSTA.base_okA RSEGS AD M.
(* [comment removed for export] *)
Hypothesis KC : NEM.kcontent RSEGS M (oa + PQMA.AOFF_KB) (PQMA.a_kb sa) kbb.
Hypothesis U8 : utf8_valid kbb = true.
Hypothesis EDEP : NEM.en_depth en = NEMA.ndest (PQMA.a_lv sa).
Hypothesis ENA : NEMA.enc_atA RSEGS AE L ar M ov osk en.
Hypothesis SKA : NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) M osk k.
Hypothesis ECS : NEMA.ec_stateA RSEGS AD M oec b cat.
Hypothesis ERR : PQSTA.err_okA RSEGS AD AAD AQ M e.
Hypothesis PRE : PQMA.nlv sa <= PQMA.MAX_DEPTH /\ PQMA.kbsize sa + 2 <= PQMA.SMB /\ NESK.sk_z k + 5 <= NESK.SMZ /\ NEM.en_n en <= NEM.MAX_DEPTH.
Hypothesis CRF : PMSP.credit_le (NEMA.pot_aeA L ar ST0) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (st' : NEMA.aest) (b' e' : bool) (cr' : credit),
      regs_preserved R R' ->
      NEMA.ae_atA RSEGS AD AE L ar (qa_vp_adaptor AQ) M' oa ov osk st' -> NEMA.ae_ok st' -> NEMA.ec_stateA RSEGS AD M' oec b' cat -> PMSTA.base_okA RSEGS AD M' -> PQSTA.err_okA RSEGS AD AAD AQ M' e' ->
      (b = true -> b' = true) -> (e = true -> e' = true) -> PNVA.step_push R ST0 st' b b' ->
      L5CA.ahpres L ar LBX0 FF sp (PMSPA.pm_scr PNVA.VIS_H) (NEMA.ae_WA AD oa ov osk oec) M M' ->
      PMSP.credit_keep cr cr' (NEMA.pot_aeA L ar ST0) (NEMA.pot_aeA L ar st') ->
      model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (NEMA.aeown st' ++ LBX0) FF LK' cr' Aw' M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Local Notation POT := (fun x => PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) x)).
Local Notation EPOT := (NECSA.pot_encA L ar (NESKA.PMEA L)).
Local Notation QE0 := (NECSA.pot_encA L ar (NESKA.PMEA L) en k).
Lemma pot_split x kb1 e1 k1 : NEMA.pot_aeA L ar (NEMA.AEST x kb1 e1 k1) = PM.credit_add (POT x) (EPOT e1 k1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_069 ())). Qed.
Lemma hv_cost : HeapIface.hl_k_per_malloc (PMSPA.HV L ar) = 8 /\ HeapIface.hl_b_overhead (PMSPA.HV L ar) = 2 ^ 21.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_070 ())). Qed.
Lemma epot_nonneg e1 k1 Mx : NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) Mx osk k1 -> 0 <= NEM.en_k e1 <= NEM.EKMAX -> 0 <= fst (EPOT e1 k1) /\ 0 <= snd (EPOT e1 k1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_071 ())). Qed.
Lemma QENN : 0 <= fst QE0 /\ 0 <= snd QE0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_072 ())). Qed.
Lemma CR : PMSP.credit_le (PM.credit_add (POT sa) QE0) cr.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_073 ())). Qed.
Lemma CRa : PMSP.credit_le (POT sa) cr.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_074 ())). Qed.

Local Notation OWN := (own8 sp R).
Local Notation OC := (ocell8 sp).
Lemma GOCR : forall a, OC a -> sp - 80 <= a < sp.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_075 ())). Qed.
Lemma sp_facts : 140735332487168 + 28672 <= sp /\ sp <= 140737488355328 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_076 ())). Qed.
Lemma GOWN : forall M1 M1' : mem, OWN M1 -> (forall a, OC a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> OWN M1'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_077 ())). Qed.

Local Notation NMG := (PQAKSNN.n_memG L ar HI M model LBX0 FF LK Aw cr sp oa ov osk oec sa QE0).
Local Notation NM := (PQAKSNN.n_mem L ar HI M model LBX0 FF LK Aw cr sp oa ov osk oec sa QE0 OWN).
Local Notation "'SX' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX0 FF LK Aw cr sp r oa ov osk oec sa ESO QE0 HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE) (at level 10, f at level 9, only parsing).
Local Notation "'SN' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX0 FF LK Aw cr sp r oa ov osk oec sa ESO QE0 HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE CR 80 OC OWN HFR80 GOCR GOWN) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Definition vals (j : nat) : Z :=
  match j with 2%nat => spc | 3%nat => pa_gp AD | 4%nat => hl_tp L | 8%nat => oa | 9%nat => oa + 72 | 18%nat => oec | 19%nat => ctx | 20%nat => tg | 21%nat => len
             | 22%nat => 2147450880 | 23%nat => bvu (getr R (reg 23)) | 24%nat => bvu (getr R (reg 24)) | 25%nat => bvu (getr R (reg 25)) | 26%nat => bvu (getr R (reg 26))
             | 27%nat => bvu (getr R (reg 27)) | _ => 0 end.
(* [comment removed for export] *)
Definition IXA : list nat := [2; 3; 4; 22; 23; 24; 25; 26; 27]%nat.
Definition IXD : list nat := (8 :: 18 :: 19 :: 20 :: 21 :: IXA)%nat.
Local Notation REGSA := (regl IXA vals).
Local Notation REGSD := (regl IXD vals).
(* [comment removed for export] *)
Ltac cvis SVIS C a := apply (PQAKR3.word_vis _ _ _ a _ (SVIS a 8 ltac:(unfold PMSPA.pm_scr, PNVA.VIS_H, PNV.VIS_H; Lia.lia) ltac:(Lia.lia)) ltac:(Lia.lia) ltac:(Lia.lia)) in C.

(* [comment removed for export] *)
Definition xinvA (M1 : mem) (kb1 : PM.vstr) (kbb1 : list Z) : Prop :=
  NEM.kcontent RSEGS M1 (oa + PQMA.AOFF_KB) kb1 kbb1 /\ utf8_valid kbb1 = true
  /\ NEMA.enc_atA RSEGS AE L ar M1 ov osk en /\ NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) M1 osk k
  /\ NEMA.ec_stateA RSEGS AD M1 oec b cat /\ PQSTA.err_okA RSEGS AD AAD AQ M1 e.
Lemma xinv0 : xinvA M (PQMA.a_kb sa) kbb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_078 ())). Qed.

(* [comment removed for export] *)
Lemma oa_lo : 7036928 <= oa /\ oa + 96 <= 2 ^ 47.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_079 ())). Qed.

(* [comment removed for export] *)
Lemma ahpres_appb BX LB FFx spx scr W M1 M2 : L5CA.ahpres L ar (BX ++ LB) FFx spx scr W M1 M2 -> L5CA.ahpres L ar LB FFx spx scr W M1 M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_080 ())). Qed.

(* [comment removed for export] *)
Lemma xinv_ek own' M1 model1 LK1 Aw1 st1 cr1 (M3 : mem) kbb1 :
  NMG own' M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> xinvA M1 (PQMA.a_kb st1) kbb1 ->
  L5SAR.ek L ar ((PQMA.aown st1 ++ ESO) ++ LBX0) FF sp (PMSPA.pm_scr PNVA.VIS_H) [] M1 M3 -> mem_grows M1 M3 ->
  xinvA M3 (PQMA.a_kb st1) kbb1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_081 ())). Qed.

(* [comment removed for export] *)
Lemma xpiece own' M1 model1 LK1 Aw1 st1 cr1 (M3 : mem) kbb1 (Wp : Z -> Prop) :
  NMG own' M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> xinvA M1 (PQMA.a_kb st1) kbb1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall a, Wp a -> sp - PMSPA.pm_scr PNVA.VIS_H <= a < sp) -> mem_grows M1 M3 ->
  xinvA M3 (PQMA.a_kb st1) kbb1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_082 ())). Qed.

(* [comment removed for export] *)
Lemma xcall M1 model1 LK1 Aw1 st1 cr1 (M4 : mem) x' kbb1 c hc :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> xinvA M1 (PQMA.a_kb st1) kbb1 -> 0 <= c < 128 -> 0 <= hc ->
  L5CA.ahpres L ar ((s_rest false st1 ++ ESO) ++ LBX0) FF spc (PMSPA.pm_scr hc) [(oa + s_off false, 24)] M1 M4 ->
  NEM.kcontent RSEGS M4 (oa + s_off false) x' (kbb1 ++ [c]) -> xinvA M4 x' (kbb1 ++ [c]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_083 ())). Qed.

(* [comment removed for export] *)
Lemma oec_rng : 0 <= oec /\ oec + 16 <= 2 ^ 47.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_084 ())). Qed.
Lemma KFIN (fx5 : FPState) R5 M5 model6 LK5 Aw5 st5 cr5 kbb5 :
  regs_preserved R R5 -> adaptor_at M5 oa ov st5 -> PQMA.adaptor_ok st5 -> PMSTA.base_okA RSEGS AD M5 -> xinvA M5 (PQMA.a_kb st5) kbb5 ->
  NEMA.ndest (PQMA.a_lv st5) = NEMA.ndest (PQMA.a_lv sa) -> PQMA.nlv st5 = PQMA.nlv sa + 1 -> PQMA.kbsize st5 <= PQMA.kbsize sa + 2 ->
  L5CA.ahpres L ar LBX0 FF sp (PMSPA.pm_scr PNVA.VIS_H) (NEMA.ae_WA AD oa ov osk oec) M M5 ->
  PMSP.credit_keep cr cr5 (PM.credit_add (POT sa) QE0) (PM.credit_add (POT st5) QE0) -> model_rt model model6 -> incl LK5 LK -> incl Aw Aw5 -> L5CA.amodel_ok Aw5 model6 ->
  ri_inv HI ((PQMA.aown st5 ++ ESO) ++ LBX0) FF LK5 cr5 Aw5 M5 (vml_of model6) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 r M5 model6) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_085 ())). Qed.

(* [comment removed for export] *)
Lemma FIN M5 model5 LK5 Aw5 st5 cr5 kbb5 (fx5 : FPState) R5 :
  NM M5 model5 LK5 Aw5 st5 ESO QE0 cr5 -> REGSA R5 -> xinvA M5 (PQMA.a_kb st5) kbb5 ->
  NEMA.ndest (PQMA.a_lv st5) = NEMA.ndest (PQMA.a_lv sa) -> PQMA.nlv st5 = PQMA.nlv sa + 1 -> PQMA.kbsize st5 <= PQMA.kbsize sa + 2 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb081c M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_086 ())). Qed.

(* [comment removed for export] *)
Lemma NPUSH M1 model1 LK1 Aw1 st1 cr1 kbb1 (fx1 fx2 : FPState) R1 R2 (pc0 ra ch : Z) (M2v : mem) (KS : list nat) :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSA R1 -> xinvA M1 (PQMA.a_kb st1) kbb1 ->
  msteps RSEGS (st fx1 R1 pc0 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 0xf4640 M2v) -> mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall i, 0 <= i < 2 ^ 64 -> M2v (Z_to_bv 64 i) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 i)) ->
  (forall x, In x KS -> getr R2 (reg x) = getr R1 (reg x)) -> subl IXA KS = true ->
  getr R2 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R2 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R2 (reg 11) = Z_to_bv 64 ch -> 0 <= ch < 128 ->
  PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + 2 ->
  (forall (fx6 : FPState) R6 (M6 : mem) model6 LK6 Aw6 x' g' cr6,
      NM M6 model6 LK6 Aw6 (s_set false st1 x' g') ESO QE0 cr6 -> PM.vs_size x' = PQMA.kbsize st1 + 1 -> REGSA R6 -> regs_preserved R2 R6 -> xinvA M6 x' (kbb1 ++ [ch]) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 ra M6 model6) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_087 ())). Qed.

(* [comment removed for export] *)
Lemma OPENCH (arm : bool) M1 model1 LK1 Aw1 st1 cr1 kbb1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSA R1 -> xinvA M1 (PQMA.a_kb st1) kbb1 -> getr R1 (reg 8) = Z_to_bv 64 (if arm then oa + 48 else oa) ->
  NEMA.ndest (PQMA.a_lv st1) = NEMA.ndest (PQMA.a_lv sa) -> PQMA.nlv st1 = PQMA.nlv sa + 1 -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + 2 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if arm then 0xb07bc else 0xb0810) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_088 ())). Qed.

(* [comment removed for export] *)
Lemma ENC M1 model1 LK1 Aw1 st1 cr1 kbb1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSD R1 -> xinvA M1 (PQMA.a_kb st1) kbb1 ->
  NEMA.ndest (PQMA.a_lv st1) = NEMA.ndest (PQMA.a_lv sa) + 1 -> PQMA.nlv st1 = PQMA.nlv sa + 1 -> PQMA.kbsize st1 = PQMA.kbsize sa ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb0838 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_089 ())). Qed.

(* [comment removed for export] *)
Lemma xlv M1 model1 LK1 Aw1 st1 cr1 (M3 : mem) kbb1 :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> xinvA M1 (PQMA.a_kb st1) kbb1 ->
  L5CA.ahpres L ar (((PM.vs_own (PQMA.a_key st1) ++ PM.vs_own (PQMA.a_kb st1)) ++ ESO) ++ LBX0) FF spc (PMSPA.pm_scr 0) [(oa + 72, 24)] M1 M3 ->
  xinvA M3 (PQMA.a_kb st1) kbb1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_090 ())). Qed.

(* [comment removed for export] *)
Lemma PUSHLV M1 model1 LK1 Aw1 st1 cr1 kbb1 (fx1 : FPState) R1 (ra t : Z) :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSA R1 -> xinvA M1 (PQMA.a_kb st1) kbb1 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> getr R1 (reg 10) = Z_to_bv 64 (oa + 72) -> getr R1 (reg 11) = Z_to_bv 64 (spc + 12) -> getr R1 (reg 12) = Z_to_bv 64 (spc + 8) ->
  L5.u32_at RSEGS M1 (spc + 12) t -> L5.u32_at RSEGS M1 (spc + 8) 1 ->
  ((ra = 0xb07bc /\ t = 1 /\ getr R1 (reg 8) = Z_to_bv 64 (oa + 48)) \/ (ra = 0xb0810 /\ t = 1 /\ getr R1 (reg 8) = Z_to_bv 64 oa) \/ (ra = 0xb0838 /\ t = 0 /\ getr R1 (reg 8) = Z_to_bv 64 oa /\ PQMA.kbsize st1 = PQMA.kbsize sa /\ REGSD R1)) ->
  PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + 2 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb84e8 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_091 ())). Qed.

(* [comment removed for export] *)
Definition S2V (arm : bool) : Z := if arm then oec else 1.
Lemma COMMA (arm : bool) M1 model1 LK1 Aw1 cr1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 sa ESO QE0 cr1 -> REGSA R1 -> xinvA M1 (PQMA.a_kb sa) kbb ->
  getr R1 (reg 1) = Z_to_bv 64 (if arm then 0xb07a0 else 0xb07f8) -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 44 ->
  getr R1 (reg 8) = Z_to_bv 64 (if arm then oa + 48 else oa) -> getr R1 (reg 9) = Z_to_bv 64 (oa + 72) -> getr R1 (reg 18) = Z_to_bv 64 (S2V arm) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xf4640 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_092 ())). Qed.

(* [comment removed for export] *)
Lemma DISP1 M1 model1 LK1 Aw1 cr1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 sa ESO QE0 cr1 -> REGSD R1 -> xinvA M1 (PQMA.a_kb sa) kbb -> getr R1 (reg 10) = Z_to_bv 64 (oa + 80) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb0710 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_093 ())). Qed.
(* [comment removed for export] *)
Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb06b8 M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_094 ())). Qed.

End Run.


Theorem begin_array_ok : PNVA.v_begin_array_spec RSEGS AD AQ AAD AE L ar HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBa ()) ["WithHeap"] (Mh_0270_blobs1.kr_b_095 ())). Qed.

End WithHeap.
End PQAABA.


End PnAAdBa.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdStrCK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0243. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0235. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180.
Module PnAAdBl.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdStrCK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0243. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0235. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObjA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAdStrCK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKSlotA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKCallA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKStepA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKFromA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKEncNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemFrameA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0243.PnAAdBlP1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0243.PnAAdBlP2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0235.PnAAdBlP3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0243.PnAAdBlP4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201.PnAAdBlP5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0243.PnAAdBlP6 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012.Na0_code_rb4d74_b4d78 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180.Na0DiagKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdBl () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_02136PnVisA4PQVA6ndig_fC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z6ltb_geC69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF3:ndig_f_rngC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z7pow_1_rK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL9ndig_f_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA4ndigC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z6leb_gtK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL7ndig_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5w_u64C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF39ndig_f_ltC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_symK46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib7Numbers7BinNums1N01C69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF38ndig_rngC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specC69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_strC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityc69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL2LQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL2LNC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC56Stdlib6ZArith6BinInt1Z;le_preorderc69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL2LBC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL7lit_rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_01028NemModel3NEM5asciiC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib7Mh_00188PmLayout8pa_rw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3LQNC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK7rdn_imgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL6LB_lenC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib9PnAdStrCK6PQASCK?bytes_at_of_rdnC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG37bvu_rngC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7enc_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA4PMEAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8pot_encAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA;epot_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;pot_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7pot_aeAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL9pot_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8sink_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ec_stateAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092;PnQStaticsA5PQSTA7err_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_KBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5VIS_HC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib6ZArith4Zdiv:Z_mod_multI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38obj_pf_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK47Corelib4Init5Logic2or01C59OSSVerify5KrLib7Mh_0089:IcptIfaceA;icl_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA<aicl_globalsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2or02c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL4OWNEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5own13C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3OCEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7ocell13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;own13_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL5V2_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List6filterC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_tC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5lv_eoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl01C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List:filter_appC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3advC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ndestC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_applC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5a_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5xinvGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3ESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6kbsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_oaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7alvl_okC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBlP58PQAABLP57alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6set_lvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL9ndest_advC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprK46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5s_xlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6s_advXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBlP58PQAABLP5=qvbAk2e0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBlP58PQAABLP5=qvbAk2e1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBlP58PQAABLP5=qvbAk1e1_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3IXAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL5HSPCfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3LSZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBlP58PQAABLP5;KS_qvbAk2e0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBlP58PQAABLP5;KS_qvbAk2e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBlP58PQAABLP5;KS_qvbAk1e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_WAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4EVISC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5wappWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP68PQAABLP67alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP68PQAABLP6:qvbD2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL:mem_eq_frzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA;v_bool_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8aargs_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5pre_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6step_wC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP1:qvbJ1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG38regl_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3ADVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_pfactsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7s_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ENC_SLOTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3Hh3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL2IXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ENC_HC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL7oec_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL8ov_rng56C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP68PQAABLP68KS_qvbD2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL5Hbv64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS:eargs_boolC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP18KS_qvbJ1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP1:qvbJ2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL7DU_DPHIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02439PnAAdBlP18PQAABLP18KS_qvbJ2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL4EST0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP39qvbC_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N8pb_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N6pb_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_restC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_setC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_app_asciiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_xcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N9s_call_sCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP37KS_qvbCC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multK46Stdlib9micromega=RingMicromega3Op206C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N9s_key_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7src_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ins_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7ins_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA8src_okCAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL7AFTER_VC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL7AFTER_KC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5INS_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8AOFF_KEYC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbc69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL4INS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_kcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP37alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG>u64_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL5COMMAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL5KDESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP3;qvbDKz_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP3;qvbDKn_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP3;qvbDV2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP3<qvbDV1z_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP3<qvbDV1n_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP39KS_qvbDKzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP39KS_qvbDKnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP39KS_qvbDV2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP3:KS_qvbDV1zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02359PnAAdBlP38PQAABLP3:KS_qvbDV1nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lv_shapeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_kbgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8lv_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N:lv_last_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL6KEYLITC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL6PATH_DC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lv_rootC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5aeownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA9args_boolC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6cls_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;evis_of_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6edepthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBl6PQAABL3RUNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ9qa_v_boolC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA;v_bool_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA7pre_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8step_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3phiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA6d_boolC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAABL.
Import L5A L5SAR PQAKS3N PQAKC3N PQAKT3N PQAKG3 PQAKENA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
(* [comment removed for export] *)
Ltac flia := solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ].
Ltac fd := first [assumption | flia].
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AQ := PnLayoutQA.QADDR_A.
Abbreviation AE := NemLayoutA.NEADDR_A.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation adaptor_at := (PQMA.adaptor_at RSEGS AD accA annA (qa_vp_adaptor AQ)).
Abbreviation kcontent := (NEM.kcontent RSEGS).
Abbreviation bvu x := (bv_unsigned x).

(* [comment removed for export] *)
Lemma ndig_f_lb f : forall v k, 10 ^ k <= v -> k <= Z.of_nat f -> 0 <= k -> k + 1 <= PQVA.ndig_f f v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_096 ())). Qed.
Lemma ndig_lb v k : 0 <= k <= 19 -> 10 ^ k <= v -> k + 1 <= PQVA.ndig v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_097 ())). Qed.
Lemma w_u64_ndig v : 0 <= v -> NEM.w_u64 v <= PQVA.ndig v + 2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_098 ())). Qed.
Lemma ndig_u32 v : 0 <= v < 2 ^ 32 -> PQVA.ndig v <= 10.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_099 ())). Qed.
Lemma hdr_str_ndig v : 0 <= v < 2 ^ 64 -> NEM.hdr_str (PQVA.ndig v) = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_100 ())). Qed.

(* [comment removed for export] *)
Definition LQ (t : bool) : Z := if t then 157056 else 157088.
Definition LN (t : bool) : Z := if t then 4 else 5.
Definition LB (t : bool) : list Z := if t then [116; 114; 117; 101] else [102; 97; 108; 115; 101].
Lemma LQN t : 65536 <= LQ t /\ LQ t + LN t <= 1409024 /\ LQ t mod 8 = 0 /\ 4 <= LN t <= 5.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_101 ())). Qed.
Lemma LB_len t : Z.of_nat (length (LB t)) = LN t.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_102 ())). Qed.
Lemma lit_rdn t : rdn RSEGS (fun _ => None) (Z_to_bv 64 (LQ t)) (Z.to_nat (LN t)) = Some (map (Z_to_bv 8) (LB t)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_103 ())). Qed.
Lemma LITR t : exists bs, length bs = Z.to_nat (LN t) /\ rdn RSEGS (fun _ => None) (Z_to_bv 64 (LQ t)) (length bs) = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_104 ())). Qed.
Lemma lit_ascii t : NEM.ascii (LB t).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_105 ())). Qed.
(* [comment removed for export] *)
Lemma lit_bytes_at (Mx : mem) t : L5.img_clear Mx 65536 (pa_rw_lo AD) -> L5.bytes_at RSEGS Mx (LQ t) (LB t) /\ NEM.bytes_ok (LB t).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_106 ())). Qed.

(* [comment removed for export] *)
Lemma aacc_join (Mx : mem) p n m : aacc Mx p n -> aacc Mx (p + n) m -> 0 <= n -> aacc Mx p (n + m).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_107 ())). Qed.
Lemma aacc_sub (Mx : mem) a0 n0 a1 n1 : aacc Mx a0 n0 -> a0 <= a1 -> a1 + n1 <= a0 + n0 -> aacc Mx a1 n1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_108 ())). Qed.

(* [comment removed for export] *)
Lemma mem_eq_frz (Ma Mb : mem) : (forall a, 0 <= a < 2 ^ 64 -> ~ False -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> Mb = Ma.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) [] (Mh_0270_blobs1.kr_b_109 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
(* [comment removed for export] *)
Hypothesis PB : PQASCA.pb_specCA RSEGS AD L ar HI 0xf4640.
Hypothesis INSJ : PQASCA.ins_specCA RSEGS AD L ar HI 0xbe330.
Hypothesis INSI : PQASCA.ins_specCA RSEGS AD L ar HI 0xb95f0.
Hypothesis VBE : NECSA.v_bool_spec RSEGS AD AQ AAD AE L ar HI (NESKA.PMEA L).
Hypothesis VKE : NECSA.v_key_spec RSEGS AD AQ AAD AE L ar HI (NESKA.PMEA L).

(* [comment removed for export] *)
Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (V2 cls r oa ov osk oec cat bv tg : Z) (sa : PQMA.ast) (kbb : list Z) (en : NEM.enc) (k : NESK.sink) (bf ef : bool).
Local Notation sp := (V2 + cls).
Local Notation spc := (V2 - 160).
Local Notation EPOT := (NECSA.pot_encA L ar (NESKA.PMEA L)).
(* [comment removed for export] *)
Local Notation ESO := (NECS.eown en k).
Local Notation QE := (NECSA.pot_encA L ar (NESKA.PMEA L) en k).
Local Notation ST0 := (NEMA.AEST sa kbb en k).
(* [comment removed for export] *)
Local Notation ND := 5.
Local Notation DU := 7.
Local Notation DPHI := 7.
Hypothesis Hcls : cls = 0 \/ cls = 16.
Hypothesis V32 : V2 mod 32 = 0.
Hypothesis HH : ri_inv HI ((PQMA.aown sa ++ ESO) ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r PNVA.VIS_H.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM PNVA.VIS_H FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 oa.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 bv.
Hypothesis Hbv : bv = 0 \/ bv = 1.
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 tg.
Hypothesis Htg : 0 <= tg < 2 ^ 64.
Hypothesis A14 : getr R (reg 14) = Z_to_bv 64 oec.
Hypothesis AO : PMSPA.aobjA FF oa PQMA.ASIZE.
Hypothesis O8 : oa mod 8 = 0.
Hypothesis AOV : PMSPA.aobjA FF ov 56.
Hypothesis OV8 : ov mod 8 = 0.
Hypothesis AOSK : PMSPA.aobjA FF osk 24.
Hypothesis OK8 : osk mod 8 = 0.
Hypothesis AOEC : PMSPA.aobjA FF oec 16.
Hypothesis OE8 : oec mod 8 = 0.
Hypothesis APT : oa + PQMA.ASIZE <= ov \/ ov + 56 <= oa.
Hypothesis APT2 : oa + PQMA.ASIZE <= osk \/ osk + 24 <= oa.
Hypothesis APT3 : oa + PQMA.ASIZE <= oec \/ oec + 16 <= oa.
Hypothesis APT4 : ov + 56 <= osk \/ osk + 24 <= ov.
Hypothesis APT5 : oec + 16 <= ov \/ ov + 56 <= oec.
Hypothesis APT6 : oec + 16 <= osk \/ osk + 24 <= oec.
Hypothesis AA : adaptor_at M oa ov sa.
Hypothesis OACC : accA M oa PQMA.ASIZE.
Hypothesis AOK : PQMA.adaptor_ok sa.
Hypothesis VIS : EVIS M ov.
Hypothesis BASE : PMSTA.base_okA RSEGS AD M.
(* [comment removed for export] *)
Hypothesis KC : kcontent M (oa + PQMA.AOFF_KB) (PQMA.a_kb sa) kbb.
Hypothesis U8 : utf8_valid kbb = true.
Hypothesis EDEP : NEM.en_depth en = NEMA.ndest (PQMA.a_lv sa).
Hypothesis ENA : NEMA.enc_atA RSEGS AE L ar M ov osk en.
Hypothesis SKA : NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) M osk k.
Hypothesis ECS : NEMA.ec_stateA RSEGS AD M oec bf cat.
Hypothesis ERR : PQSTA.err_okA RSEGS AD AAD AQ M ef.
Hypothesis PRE : PQMA.kbsize sa + DU <= PQMA.SMB /\ NESK.sk_z k + DPHI <= NESK.SMZ.
Hypothesis CRF : PMSP.credit_le (NEMA.pot_aeA L ar ST0) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (st' : NEMA.aest) (b' e' : bool) (cr' : credit),
      regs_preserved R R' ->
      NEMA.ae_atA RSEGS AD AE L ar (qa_vp_adaptor AQ) M' oa ov osk st' -> NEMA.ae_ok st' -> NEMA.ec_stateA RSEGS AD M' oec b' cat -> PMSTA.base_okA RSEGS AD M' -> PQSTA.err_okA RSEGS AD AAD AQ M' e' ->
      (bf = true -> b' = true) -> (ef = true -> e' = true) ->
      (NEMA.nlv st' = NEMA.nlv ST0 /\ NEMA.kbsize st' <= NEMA.kbsize ST0 + DU /\ NEMA.phi st' <= NEMA.phi ST0 + DPHI /\ NEMA.esize st' = NEMA.esize ST0
       /\ NEMA.edepth st' = NEMA.edepth ST0 /\ (b' = bf \/ False)) ->
      L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr PNVA.VIS_H) (NEMA.ae_WA AD oa ov osk oec) M M' ->
      PMSP.credit_keep cr cr' (NEMA.pot_aeA L ar ST0) (NEMA.pot_aeA L ar st') ->
      model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (NEMA.aeown st' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition OWNE (Mx : mem) : Prop := own13 sp R Mx /\ L5.u64_at RSEGS Mx (V2 - 136) oec.
Definition OCE (a : Z) : Prop := ocell13 sp a \/ (V2 - 136 <= a < V2 - 128).
Local Notation OWN := OWNE.
Local Notation OC := OCE.
(* [comment removed for export] *)
Lemma QENN : 0 <= fst QE /\ 0 <= snd QE.
Proof using LY ENA SKA.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_110 ())). Qed.
Local Notation "'SX' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Lemma pot_split x kb1 e1 k1 : NEMA.pot_aeA L ar (NEMA.AEST x kb1 e1 k1) = PM.credit_add (PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) x)) (EPOT e1 k1).
Proof using L ar.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_111 ())). Qed.
Lemma CR : PMSP.credit_le (PM.credit_add (PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) sa)) QE) cr.
Proof using CRF.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_112 ())). Qed.
Lemma xinv0 : PQAKENA.xinvG L ar oa ov osk oec cat M (PQMA.a_kb sa) kbb en k bf ef.
Proof using KC U8 ENA SKA ECS ERR.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_113 ())). Qed.

Lemma sp_facts : 140735332487264 + 16 <= V2 /\ V2 + cls <= 140737488355328 /\ (V2 + cls) mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof using ENT Hcls.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_114 ())). Qed.
Lemma V2_lo : 140735332487328 <= V2.
Proof using ENT Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_115 ())). Qed.
Lemma HSPCf : sp - 2048 <= spc /\ spc mod 16 = 0.
Proof using Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_116 ())). Qed.
Lemma oec_rng : 7036928 <= oec /\ oec + 16 <= 2 ^ 47.
Proof using LY HIok HH AOEC.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_117 ())). Qed.
Lemma oa_lo96 : 7036928 <= oa /\ oa + 96 <= 2 ^ 47.
Proof using LY HIok HH AO.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_118 ())). Qed.
Lemma ov_rng56 : 7036928 <= ov /\ ov + 56 <= ahl_ceil ar /\ ov + 56 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784).
Proof using LY HIok HH AOV.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_119 ())). Qed.
Lemma tg_rng : 0 <= tg < 2 ^ 64.
Proof using Htg.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_120 ())). Qed.
Lemma Hbv64 : 0 <= bv < 2 ^ 64.
Proof using Hbv.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_121 ())). Qed.
(* [comment removed for export] *)
Lemma ING t : In (LQ t, LN t + 1) (icl_globals IL).
Proof using ILY.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_122 ())). Qed.
Lemma GOWNE : forall Ma Mb, OWN Ma -> (forall a, OC a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> OWN Mb.
Proof using ENT Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_123 ())). Qed.

(* [comment removed for export] *)
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK Aw sp (PMSPA.pm_scr PNVA.VIS_H) spc (V2 - 136) sp OC OWN F fl 0 LK2 M2 model2 cr (PQMA.aown sa ++ ESO).
Hypothesis APART : forall a n0 sp0 scr0, (forall i, 0 <= i < n0 -> aclient L ar ((PQMA.aown sa ++ ESO) ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n0 ->
         (a + n0 <= F \/ F + ff_bytes 0 <= a) /\ (a + n0 <= F / 8 + SB \/ F / 8 + SB + ff_bytes 0 / 8 <= a) /\ (a + n0 <= fl \/ fl + 1 <= a).
Local Notation FF' := ((F, 0, spc + 32) :: FF).
Local Notation AMF := (PQAKS3N.a_mem L ar HI M model LBX FF LK Aw cr sp oa ov osk oec sa QE spc OWN 0 F).
Local Notation xinv := (PQAKENA.xinvG L ar oa ov osk oec cat).
Local Notation "'SF' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE spc (V2 - 136) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).
Local Notation "'SE' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE cat OV8 OK8 OE8 APT2 APT3 APT4 APT5 APT6 spc (V2 - 136) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).
Local Notation "'SY' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE cat APT2 APT3 spc (V2 - 136) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).
Local Notation "'GF' f" := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r PNVA.VIS_H (PQMA.aown sa ++ ESO) (NEMA.ae_WA AD oa ov osk oec) HH AM K0 ENT FRM FRS PQAKS3N.Hh3 (SX PQAKS3N.wappW) spc (V2 - 136) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Definition vals (j : nat) : Z :=
  match j with 2%nat => spc | 3%nat => pa_gp AD | 4%nat => hl_tp L | 8%nat => sp | 18%nat => F | 19%nat => oa + 80 | 20%nat => oa | 22%nat => (oa + 80) / 8 + 2147450880 | 23%nat => tg | 24%nat => bv
             | 25%nat => F | 26%nat => 2147450880 | 27%nat => F / 8 + 2147450880 | 9%nat => spc | _ => 0 end.
Definition IXA : list nat := [2; 3; 4; 8; 18; 19; 22; 23; 25; 26; 27]%nat.
Definition IX : list nat := (9 :: 20 :: 24 :: IXA)%nat.
Local Notation REGSA := (regl IXA vals).
Local Notation REGS := (regl IX vals).

(* [comment removed for export] *)
Ltac pf LM :=
  let BIx := fresh "BIx" in pose proof (proj1 LM) as BIx;
  destruct ((GF PQAKR3.g_pfacts) _ _ _ _ _ _ BIx) as ((PF1 & PF2 & PF3 & PF4 & _) & (FD & FW & FSW & FLU & FLW) & (PL1 & PL2 & PL3 & PL4) & (SW & OWNV & PS1 & PS2 & PS3 & PS4) & (CSB & CUAR & _) & (AVSH & AVF & AVS));
  change (ff_bytes 0) with 64 in *; change (64 / 8) with 8 in *.

(* [comment removed for export] *)
Definition EST (en1 : NEM.enc) (k1 : NESK.sink) (b1 e1 : bool) : Prop :=
  NEM.en_n en1 = NEM.en_n en /\ NEM.en_depth en1 = NEM.en_depth en /\ NESK.sk_z k <= NESK.sk_z k1
  /\ (bf = true -> b1 = true) /\ (ef = true -> e1 = true) /\ (b1 = bf \/ False).
Lemma EST0 : EST en k bf ef.
Proof using Hbv.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_124 ())). Qed.
Lemma DU_DPHI : DU <= DPHI /\ ND + 1 <= DPHI /\ ND + 2 <= DU.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_125 ())). Qed.
(* [comment removed for export] *)
Lemma ndest_adv lv0 c : NEMA.ndest (lv0 ++ [PQAKS3N.adv c]) = NEMA.ndest (lv0 ++ [c]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_126 ())). Qed.

(* [comment removed for export] *)
Lemma FIN M5 model5 LK5 Aw5 st5 cr5 kbb5 en5 k5 (b5 e5 : bool) (fx5 : FPState) R5 :
  AMF M5 model5 LK5 Aw5 st5 (NECS.eown en5 k5) (EPOT en5 k5) cr5 -> REGSA R5 -> xinv M5 (PQMA.a_kb st5) kbb5 en5 k5 b5 e5 -> EST en5 k5 b5 e5 ->
  PQMA.nlv st5 = PQMA.nlv sa -> PQMA.kbsize st5 <= PQMA.kbsize sa + DU -> PQMA.kbsize st5 + NESK.sk_z k5 <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st5) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb4be0 M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_127 ())). Qed.


(* [comment removed for export] *)
Lemma ADV M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 en1 k1 (b1 e1 : bool) (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 (NECS.eown en1 k1) (EPOT en1 k1) cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en1 k1 b1 e1 -> EST en1 k1 b1 e1 ->
  PQMA.a_lv st1 = lv0 ++ [c] ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 <= PQMA.kbsize sa + DU -> PQMA.kbsize st1 + NESK.sk_z k1 <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st1) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb4b68 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_128 ())). Qed.


(* [comment removed for export] *)
Ltac of LM ELV :=
  destruct ((SF PQAKS3N.s_oa) _ _ _ _ _ _ _ _ LM) as ((OA1 & OA2 & OA3 & OA4 & OA5) & OAZ & O16 & (OV1 & OV2 & OV3 & OV4 & OVZ & OVW) & IMG & VTZ & (OAF & OVF & OASF & OVSF) & (OAV & OAW));
  destruct ((SF PQAKS3N.s_lv) _ _ _ _ _ _ _ _ _ _ LM ELV) as (E80 & (E1 & E2 & E8 & E4 & E5) & (Z24 & Z20 & Z16 & Z8) & (CT & CK & CEO) & (CD & CW & CVIS) & (EO1 & EF1 & EV1) & ((CTR & CKR & CER & CKE) & CT1) & INL & EHI).

(* [comment removed for export] *)
Lemma PATH_D M1 model1 LK1 Aw1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> PQMA.a_lv sa = lv0 ++ [c] -> PQMA.lv_t c = 0 -> PQMA.lv_eo c = 1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb468c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_129 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AFTER_V M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb4a38 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_130 ())). Qed.
(* [comment removed for export] *)
Lemma AFTER_K M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48) -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb4b5c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_131 ())). Qed.


(* [comment removed for export] *)
Lemma div2_2 n : (2 * n) / 2 = n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_132 ())). Qed.
(* [comment removed for export] *)
Lemma INS_CALL (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 (ra v11 v12 v13 v14 : Z) :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = false -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  ra = (if arm then 0xb4a38 else 0xb4b5c) ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 v11 -> getr R1 (reg 12) = Z_to_bv 64 v12 ->
  getr R1 (reg 13) = Z_to_bv 64 v13 -> getr R1 (reg 14) = Z_to_bv 64 v14 ->
  v11 = PM.vs_data (oa + 48) (PQMA.a_kb st1) + PM.vs_size (PQMA.a_kb st1) -> v12 = PM.vs_data (oa + 24) (PQMA.a_key st1) ->
  v13 = v12 + v14 -> v14 = PM.vs_size (PQMA.a_key st1) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + v14 + (if arm then 0 else 1) <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb95f0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_133 ())). Qed.

Lemma INS2 (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = true -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + PM.vs_size (PQMA.a_key st1) + (if arm then 0 else 1) <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if arm then 0xb4870 else 0xb48c8) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_134 ())). Qed.

(* [comment removed for export] *)
Lemma KDEST M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.lv_t c = 0 -> PQMA.lv_eo c = 0 ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 = PQMA.kbsize sa -> PM.vs_size (PQMA.a_key st1) <= ND ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb47dc M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_135 ())). Qed.

(* [comment removed for export] *)
Lemma COMMA (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = true -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  getr R1 (reg 1) = Z_to_bv 64 (if arm then 0xb4870 else 0xb48c8) -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 44 ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + 1 + PM.vs_size (PQMA.a_key st1) + (if arm then 0 else 1) <= PQMA.kbsize sa + DU -> 0 <= PM.vs_size (PQMA.a_key st1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xf4640 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_136 ())). Qed.

(* [comment removed for export] *)
Lemma DISP2 M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> (PQMA.lv_eo c = 0 \/ PQMA.lv_t c = 1) ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 = PQMA.kbsize sa -> 0 <= PM.vs_size (PQMA.a_key st1) <= ND ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb47dc M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_137 ())). Qed.

(* [comment removed for export] *)
Lemma KEYLIT M1 model1 LK1 Aw1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> PQMA.a_lv sa = lv0 ++ [c] -> (PQMA.lv_eo c = 0 \/ PQMA.lv_t c = 1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb468c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_138 ())). Qed.

(* [comment removed for export] *)
Lemma DISP1 M1 model1 LK1 Aw1 cr1 kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb468c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_139 ())). Qed.

(* [comment removed for export] *)
Lemma SETUP Mx modelx LKx Awx (fx2 : FPState) R2 :
  AMF Mx modelx LKx Awx sa ESO QE cr -> xinv Mx (PQMA.a_kb sa) kbb en k bf ef ->
  getr R2 (reg 2) = Z_to_bv 64 spc -> getr R2 (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R2 (reg 8) = Z_to_bv 64 sp ->
  getr R2 (reg 9) = Z_to_bv 64 spc -> getr R2 (reg 10) = Z_to_bv 64 F -> getr R2 (reg 20) = Z_to_bv 64 oa -> getr R2 (reg 23) = Z_to_bv 64 tg -> getr R2 (reg 24) = Z_to_bv 64 bv ->
  getr R2 (reg 26) = Z_to_bv 64 2147450880 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0xb45ec Mx modelx) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_140 ())). Qed.

End Frame.

(* [comment removed for export] *)
Ltac enter_tac Aconc fxv MVv HRgp HRtp :=
  pose proof (LF2CBN( Aconc fxv R MVv (fun j : nat => match j with 2%nat => V2 | _ => 0 end) )) as P;
  L5SAR.feed P ltac:(fd);
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T20 & T21 & T23 & T24 & T26 & CEC & C27 & C26 & C25 & C24 & C23 & C22 & C21 & C20 & C19 & C18 & C9 & C8 & C1 & C0);
  apply ((SX PQAKS3N.s_enterX) spc (V2 - 136) sp OC OWN 0 fxv fx1 R1 0xb451c 738716 M1v CR);
  [ left; reflexivity | flia | exact (proj2 HSPCf) | flia | flia | flia | intros a Ha; unfold OCE, ocell13 in Ha; destruct Ha as [Ha|Ha]; flia
  | exact GOWNE
  | exact MS1 | exact MG1 | intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; flia]
  | intros M1 VIS1 AV; unfold OWNE, own13; split;
    [ repeat match goal with |- _ /\ _ => split end;
      (match goal with |- L5.u64_at _ _ ?a0 ?v0 => apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a0 v0 (AV a0 8 ltac:(flia) ltac:(flia)) ltac:(flia) ltac:(flia))) end; rewrite VIS1;
       match goal with |- L5.u64_at _ _ ?a _ => first [ replace a with (V2 + 8) by flia; assumption
          | replace a with V2 by flia; assumption
          | replace a with (V2 - 8) by flia; assumption
          | replace a with (V2 - 16) by flia; assumption
          | replace a with (V2 - 24) by flia; assumption
          | replace a with (V2 - 32) by flia; assumption
          | replace a with (V2 - 40) by flia; assumption
          | replace a with (V2 - 48) by flia; assumption
          | replace a with (V2 - 56) by flia; assumption
          | replace a with (V2 - 64) by flia; assumption
          | replace a with (V2 - 72) by flia; assumption
          | replace a with (V2 - 80) by flia; assumption
          | replace a with (V2 - 88) by flia; assumption
          | replace a with (V2 - 96) by flia; assumption
          | replace a with (V2 - 104) by flia; assumption ] end)
    | apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 (V2 - 136) oec (AV (V2 - 136) 8 ltac:(flia) ltac:(flia)) ltac:(flia) ltac:(flia))); rewrite VIS1;
      rewrite A14 in CEC; rewrite (L5.unsigned_lit oec) in CEC by flia; exact CEC ]
  | exact T2 | apply KS1; inl | exact T1 | reflexivity | flia |];
  intros R2 M2 model2 F fl LK2 G APART LM2 EK2 G10 RP2 _;
  apply (SETUP F fl LK2 M2 model2 G APART M2 model2 LK2 Aw fx1 R2 LM2);
  [ apply (PQAKENA.xinv_ekF L ar C HI LY HIok oa ov osk oec cat (proj1 oa_lo96) _ FF sp (PMSPA.pm_scr PNVA.VIS_H) M M2 sa kbb en k bf ef
             (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) AO AOV AOSK AOEC AA
             ltac:(apply incl_appl; apply incl_appl; apply incl_refl) ltac:(apply incl_appl; apply incl_appr; unfold NECS.eown; apply incl_appl; apply incl_refl)
             ltac:(apply incl_appl; apply incl_appr; unfold NECS.eown; apply incl_appr; apply incl_refl) EK2 xinv0)
  | rewrite (L5SAR.cs_of_preserved _ _ 2%nat RP2 ltac:(inl)); exact T2
  | rewrite (L5SAR.cs_of_preserved _ _ 3%nat RP2 ltac:(inl)); rewrite (KS1 3%nat) by inl; exact HRgp
  | rewrite (L5SAR.cs_of_preserved _ _ 4%nat RP2 ltac:(inl)); rewrite (KS1 4%nat) by inl; exact HRtp
  | rewrite (L5SAR.cs_of_preserved _ _ 8%nat RP2 ltac:(inl)); rewrite T8; f_equal; flia
  | rewrite (L5SAR.cs_of_preserved _ _ 9%nat RP2 ltac:(inl)); exact T9
  | exact G10
  | rewrite (L5SAR.cs_of_preserved _ _ 20%nat RP2 ltac:(inl)); rewrite T20; exact A10
  | rewrite (L5SAR.cs_of_preserved _ _ 23%nat RP2 ltac:(inl)); rewrite T23; exact A12
  | rewrite (L5SAR.cs_of_preserved _ _ 24%nat RP2 ltac:(inl)); rewrite T24; exact A11
  | rewrite (L5SAR.cs_of_preserved _ _ 26%nat RP2 ltac:(inl)); exact T26 ].

Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb456c M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_141 ())). Qed.

End Run.

(* [comment removed for export] *)
Theorem bool_ok : PNVA.v_bool_spec RSEGS AD AQ AAD AE L ar HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBl ()) ["WithHeap"] (Mh_0270_blobs1.kr_b_142 ())). Qed.

End WithHeap.
End PQAABL.


End PnAAdBl.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016.
Module PnAAdBo.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObjA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAHarnessKit5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemFrameA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKSlotA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKCallA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKSlotNA3bN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdBoP1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdBoP2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016.Na0_code_rb313c_b3140.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdBo () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2lec69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO4own8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO6ocell8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z6of_natC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;pot_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA4PMEAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8pot_encAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA7ly_costC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_b_linC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=hl_b_overheadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8sink_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA7PMEA_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA@sink_potA_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA7spa_potC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO7hv_costC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7enc_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO;epot_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7pot_aeAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO9pot_splitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO2CRC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5VIS_HC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO:own8_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO8sp_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ec_stateAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092;PnQStaticsA5PQSTA7err_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_KBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_ctxC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO5HFR80C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO4GOCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO4GOWNC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA5akeptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_appbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN6n_memGC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5binvNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4EVISC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_WAC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6frb_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6brb_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_visitorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lvec_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN>kcontent_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7blk_outC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemFrameA5NEMFA9enc_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemFrameA5NEMFA:sink_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemFrameA5NEMFA>ec_state_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN8err_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO5xinvAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lvec_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO5oa_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_DVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9AOFF_DESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8AOFF_KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_LVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_ncwC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO7xinv_ekC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_offC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3s_gC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_permC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_setC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8s_set_idC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib7Sorting;PermutationDPermutation_app_tailC69OSSVerify5KrLib7Mh_02569PnAKRunA16PQAKRA7ri_permC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK=blk_obj_apartC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_app_asciiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_restC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA<aobjA_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8hdr_contC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8le_max_lC56Stdlib6ZArith6BinInt1Z3maxC69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5zsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6edepthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA9step_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5aeownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ndestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP18PQAABOP17alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38word_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG37bvu_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP18PQAABOP1:qvoX0_concC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO6xpieceC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC47Corelib4Init5Logic6eq_symC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARBpreserved_by_indexC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO4KFINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN7n_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO4valsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_retC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO3IXAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP18PQAABOP18KS_qvoX0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb313c_b31407W_b2ff8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb313c_b31407F_b2ff8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb313c_b31407D_b2ff8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N8pb_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N6pb_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO5xcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN9n_call_sCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN4n_oaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP2:qvoVq_concC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP2:qvoKq_concC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO3FINC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO5NPUSHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP28KS_qvoVqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP28KS_qvoKqC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orC69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38aobj_subC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC69OSSVerify5KrLib7Mh_0213:PnSpecsAXl6PQSAXL6lvl_eoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_kbgC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO3xlvC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Nat2Z7inj_addC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_tC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ndest_appC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rc69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO6OPENCHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO3ENCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN=n_call_lvpushC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO3IXDC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Zc69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO3S2VC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP2:qvoVp_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP2:qvoKp_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u32_at_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO6PUSHLVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO7oec_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP28KS_qvoVpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP28PQAABOP28KS_qvoKpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN7n_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN6n_memEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP18PQAABOP19qvoA_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u64_at_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO5DISP1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdBoP18PQAABOP17KS_qvoAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO5xinv0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8args_ec4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8pre_pushC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation@Permutation_reflC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;evis_of_encC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBo6PQAABO3RUNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQAqa_v_begin_objectC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVACv_begin_object_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAABO.
Import L5A L5SAR PQAKS3N PQAKC3N PQAKG3 PQAKSNN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac flia := solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ].
Ltac fd := first [assumption | flia].
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AQ := PnLayoutQA.QADDR_A.
Abbreviation AE := NemLayoutA.NEADDR_A.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation adaptor_at := (PQMA.adaptor_at RSEGS AD accA annA (qa_vp_adaptor AQ)).
Abbreviation bvu x := (bv_unsigned x).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) [] (Mh_0270_blobs1.kr_b_143 ())). Qed.

(* [comment removed for export] *)
Definition own8 (sp : Z) (R : bvmap 5 word) (M : mem) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (bvu (getr R (reg 1))) /\ L5.u64_at RSEGS M (sp - 16) (bvu (getr R (reg 8))) /\ L5.u64_at RSEGS M (sp - 24) (bvu (getr R (reg 9)))
  /\ L5.u64_at RSEGS M (sp - 32) (bvu (getr R (reg 18))) /\ L5.u64_at RSEGS M (sp - 40) (bvu (getr R (reg 19))) /\ L5.u64_at RSEGS M (sp - 48) (bvu (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (sp - 56) (bvu (getr R (reg 21))) /\ L5.u64_at RSEGS M (sp - 64) (bvu (getr R (reg 22))).
Definition ocell8 (sp : Z) (a : Z) : Prop := sp - 64 <= a < sp.
Lemma own8_agree sp R M1 M1' : 0 <= sp - 64 -> sp <= 2 ^ 64 ->
  own8 sp R M1 -> (forall a, ocell8 sp a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own8 sp R M1'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) [] (Mh_0270_blobs1.kr_b_144 ())). Qed.
Lemma HFR80 : 16 <= 80 <= 2048 /\ 80 mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) [] (Mh_0270_blobs1.kr_b_145 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
(* [comment removed for export] *)
Hypothesis PBC : PQASCA.pb_specCA RSEGS AD L ar HI 0xf4640.
Hypothesis LVP : PQSAXL.lvpush_spec RSEGS AD L ar HI 0xb84e8.
Hypothesis VBE : NECSA.v_begin_obj_spec RSEGS AD AQ AAD AE L ar HI (NESKA.PMEA L).

Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX0 : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (sp r oa ov osk oec cat len tg ctx : Z) (sa : PQMA.ast) (kbb : list Z) (en : NEM.enc) (k : NESK.sink) (b e : bool).
Local Notation spc := (sp - 80).
(* [comment removed for export] *)
Local Notation ESO := (NEM.enc_own en ++ NESK.sink_own k).
Local Notation LBX := (ESO ++ LBX0).
Local Notation ST0 := (NEMA.AEST sa kbb en k).
Hypothesis SP16 : sp mod 16 = 0.
Hypothesis HH : ri_inv HI ((PQMA.aown sa ++ ESO) ++ LBX0) FF LK cr Aw M (vml_of model).   (* [comment removed for export] *)
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r PNVA.VIS_H.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM PNVA.VIS_H FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 oa.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 len.
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 tg.
Hypothesis A13 : getr R (reg 13) = Z_to_bv 64 ctx.
Hypothesis A14 : getr R (reg 14) = Z_to_bv 64 oec.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis Htg : 0 <= tg < 2 ^ 64.
Hypothesis Hctx : 0 <= ctx < 2 ^ 64.
Hypothesis AO : PMSPA.aobjA FF oa PQMA.ASIZE.
Hypothesis O8 : oa mod 8 = 0.
Hypothesis AOV : PMSPA.aobjA FF ov 56.
Hypothesis OV8 : ov mod 8 = 0.
Hypothesis AOSK : PMSPA.aobjA FF osk 24.
Hypothesis OK8 : osk mod 8 = 0.
Hypothesis AOEC : PMSPA.aobjA FF oec 16.
Hypothesis OE8 : oec mod 8 = 0.
Hypothesis APT : oa + PQMA.ASIZE <= ov \/ ov + 56 <= oa.
Hypothesis APT2 : oa + PQMA.ASIZE <= osk \/ osk + 24 <= oa.
Hypothesis APT3 : oa + PQMA.ASIZE <= oec \/ oec + 16 <= oa.
Hypothesis APT4 : ov + 56 <= osk \/ osk + 24 <= ov.
Hypothesis APT5 : oec + 16 <= ov \/ ov + 56 <= oec.
Hypothesis APT6 : oec + 16 <= osk \/ osk + 24 <= oec.
Hypothesis AA : adaptor_at M oa ov sa.
Hypothesis OACC : accA M oa PQMA.ASIZE.
Hypothesis AOK : PQMA.adaptor_ok sa.
Hypothesis VIS : EVIS M ov.
Hypothesis BASE : PMSTA.base_okA RSEGS AD M.
(* [comment removed for export] *)
Hypothesis KC : NEM.kcontent RSEGS M (oa + PQMA.AOFF_KB) (PQMA.a_kb sa) kbb.
Hypothesis U8 : utf8_valid kbb = true.
Hypothesis EDEP : NEM.en_depth en = NEMA.ndest (PQMA.a_lv sa).
Hypothesis ENA : NEMA.enc_atA RSEGS AE L ar M ov osk en.
Hypothesis SKA : NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) M osk k.
Hypothesis ECS : NEMA.ec_stateA RSEGS AD M oec b cat.
Hypothesis ERR : PQSTA.err_okA RSEGS AD AAD AQ M e.
Hypothesis PRE : PQMA.nlv sa <= PQMA.MAX_DEPTH /\ PQMA.kbsize sa + 2 <= PQMA.SMB /\ NESK.sk_z k + 5 <= NESK.SMZ /\ NEM.en_n en <= NEM.MAX_DEPTH.
Hypothesis CRF : PMSP.credit_le (NEMA.pot_aeA L ar ST0) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (st' : NEMA.aest) (b' e' : bool) (cr' : credit),
      regs_preserved R R' ->
      NEMA.ae_atA RSEGS AD AE L ar (qa_vp_adaptor AQ) M' oa ov osk st' -> NEMA.ae_ok st' -> NEMA.ec_stateA RSEGS AD M' oec b' cat -> PMSTA.base_okA RSEGS AD M' -> PQSTA.err_okA RSEGS AD AAD AQ M' e' ->
      (b = true -> b' = true) -> (e = true -> e' = true) -> PNVA.step_push R ST0 st' b b' ->
      L5CA.ahpres L ar LBX0 FF sp (PMSPA.pm_scr PNVA.VIS_H) (NEMA.ae_WA AD oa ov osk oec) M M' ->
      PMSP.credit_keep cr cr' (NEMA.pot_aeA L ar ST0) (NEMA.pot_aeA L ar st') ->
      model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (NEMA.aeown st' ++ LBX0) FF LK' cr' Aw' M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Local Notation POT := (fun x => PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) x)).
Local Notation EPOT := (NECSA.pot_encA L ar (NESKA.PMEA L)).
Local Notation QE0 := (NECSA.pot_encA L ar (NESKA.PMEA L) en k).
Lemma pot_split x kb1 e1 k1 : NEMA.pot_aeA L ar (NEMA.AEST x kb1 e1 k1) = PM.credit_add (POT x) (EPOT e1 k1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_146 ())). Qed.
Lemma hv_cost : HeapIface.hl_k_per_malloc (PMSPA.HV L ar) = 8 /\ HeapIface.hl_b_overhead (PMSPA.HV L ar) = 2 ^ 21.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_147 ())). Qed.
Lemma epot_nonneg e1 k1 Mx : NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) Mx osk k1 -> 0 <= NEM.en_k e1 <= NEM.EKMAX -> 0 <= fst (EPOT e1 k1) /\ 0 <= snd (EPOT e1 k1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_148 ())). Qed.
Lemma QENN : 0 <= fst QE0 /\ 0 <= snd QE0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_149 ())). Qed.
Lemma CR : PMSP.credit_le (PM.credit_add (POT sa) QE0) cr.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_150 ())). Qed.
Lemma CRa : PMSP.credit_le (POT sa) cr.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_151 ())). Qed.

Local Notation OWN := (own8 sp R).
Local Notation OC := (ocell8 sp).
Lemma GOCR : forall a, OC a -> sp - 80 <= a < sp.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_152 ())). Qed.
Lemma sp_facts : 140735332487168 + 28672 <= sp /\ sp <= 140737488355328 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_153 ())). Qed.
Lemma GOWN : forall M1 M1' : mem, OWN M1 -> (forall a, OC a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> OWN M1'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_154 ())). Qed.

Local Notation NMG := (PQAKSNN.n_memG L ar HI M model LBX0 FF LK Aw cr sp oa ov osk oec sa QE0).
Local Notation NM := (PQAKSNN.n_mem L ar HI M model LBX0 FF LK Aw cr sp oa ov osk oec sa QE0 OWN).
Local Notation "'SX' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX0 FF LK Aw cr sp r oa ov osk oec sa ESO QE0 HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE) (at level 10, f at level 9, only parsing).
Local Notation "'SN' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX0 FF LK Aw cr sp r oa ov osk oec sa ESO QE0 HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE CR 80 OC OWN HFR80 GOCR GOWN) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Definition vals (j : nat) : Z :=
  match j with 2%nat => spc | 3%nat => pa_gp AD | 4%nat => hl_tp L | 8%nat => oa | 9%nat => oa + 72 | 18%nat => oec | 19%nat => ctx | 20%nat => tg | 21%nat => len
             | 22%nat => 2147450880 | 23%nat => bvu (getr R (reg 23)) | 24%nat => bvu (getr R (reg 24)) | 25%nat => bvu (getr R (reg 25)) | 26%nat => bvu (getr R (reg 26))
             | 27%nat => bvu (getr R (reg 27)) | _ => 0 end.
(* [comment removed for export] *)
Definition IXA : list nat := [2; 3; 4; 22; 23; 24; 25; 26; 27]%nat.
Definition IXD : list nat := (8 :: 18 :: 19 :: 20 :: 21 :: IXA)%nat.
Local Notation REGSA := (regl IXA vals).
Local Notation REGSD := (regl IXD vals).
(* [comment removed for export] *)
Ltac cvis SVIS C a := apply (PQAKR3.word_vis _ _ _ a _ (SVIS a 8 ltac:(unfold PMSPA.pm_scr, PNVA.VIS_H, PNV.VIS_H; Lia.lia) ltac:(Lia.lia)) ltac:(Lia.lia) ltac:(Lia.lia)) in C.

(* [comment removed for export] *)
Definition xinvA (M1 : mem) (kb1 : PM.vstr) (kbb1 : list Z) : Prop :=
  NEM.kcontent RSEGS M1 (oa + PQMA.AOFF_KB) kb1 kbb1 /\ utf8_valid kbb1 = true
  /\ NEMA.enc_atA RSEGS AE L ar M1 ov osk en /\ NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) M1 osk k
  /\ NEMA.ec_stateA RSEGS AD M1 oec b cat /\ PQSTA.err_okA RSEGS AD AAD AQ M1 e.
Lemma xinv0 : xinvA M (PQMA.a_kb sa) kbb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_155 ())). Qed.

(* [comment removed for export] *)
Lemma oa_lo : 7036928 <= oa /\ oa + 96 <= 2 ^ 47.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_156 ())). Qed.

(* [comment removed for export] *)
Lemma ahpres_appb BX LB FFx spx scr W M1 M2 : L5CA.ahpres L ar (BX ++ LB) FFx spx scr W M1 M2 -> L5CA.ahpres L ar LB FFx spx scr W M1 M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_157 ())). Qed.

(* [comment removed for export] *)
Lemma xinv_ek own' M1 model1 LK1 Aw1 st1 cr1 (M3 : mem) kbb1 :
  NMG own' M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> xinvA M1 (PQMA.a_kb st1) kbb1 ->
  L5SAR.ek L ar ((PQMA.aown st1 ++ ESO) ++ LBX0) FF sp (PMSPA.pm_scr PNVA.VIS_H) [] M1 M3 -> mem_grows M1 M3 ->
  xinvA M3 (PQMA.a_kb st1) kbb1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_158 ())). Qed.

(* [comment removed for export] *)
Lemma xpiece own' M1 model1 LK1 Aw1 st1 cr1 (M3 : mem) kbb1 (Wp : Z -> Prop) :
  NMG own' M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> xinvA M1 (PQMA.a_kb st1) kbb1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall a, Wp a -> sp - PMSPA.pm_scr PNVA.VIS_H <= a < sp) -> mem_grows M1 M3 ->
  xinvA M3 (PQMA.a_kb st1) kbb1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_159 ())). Qed.

(* [comment removed for export] *)
Lemma xcall M1 model1 LK1 Aw1 st1 cr1 (M4 : mem) x' kbb1 c hc :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> xinvA M1 (PQMA.a_kb st1) kbb1 -> 0 <= c < 128 -> 0 <= hc ->
  L5CA.ahpres L ar ((s_rest false st1 ++ ESO) ++ LBX0) FF spc (PMSPA.pm_scr hc) [(oa + s_off false, 24)] M1 M4 ->
  NEM.kcontent RSEGS M4 (oa + s_off false) x' (kbb1 ++ [c]) -> xinvA M4 x' (kbb1 ++ [c]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_160 ())). Qed.

(* [comment removed for export] *)
Lemma oec_rng : 0 <= oec /\ oec + 16 <= 2 ^ 47.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_161 ())). Qed.
Lemma KFIN (fx5 : FPState) R5 M5 model6 LK5 Aw5 st5 cr5 kbb5 :
  regs_preserved R R5 -> adaptor_at M5 oa ov st5 -> PQMA.adaptor_ok st5 -> PMSTA.base_okA RSEGS AD M5 -> xinvA M5 (PQMA.a_kb st5) kbb5 ->
  NEMA.ndest (PQMA.a_lv st5) = NEMA.ndest (PQMA.a_lv sa) -> PQMA.nlv st5 = PQMA.nlv sa + 1 -> PQMA.kbsize st5 <= PQMA.kbsize sa + 2 ->
  L5CA.ahpres L ar LBX0 FF sp (PMSPA.pm_scr PNVA.VIS_H) (NEMA.ae_WA AD oa ov osk oec) M M5 ->
  PMSP.credit_keep cr cr5 (PM.credit_add (POT sa) QE0) (PM.credit_add (POT st5) QE0) -> model_rt model model6 -> incl LK5 LK -> incl Aw Aw5 -> L5CA.amodel_ok Aw5 model6 ->
  ri_inv HI ((PQMA.aown st5 ++ ESO) ++ LBX0) FF LK5 cr5 Aw5 M5 (vml_of model6) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 r M5 model6) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_162 ())). Qed.

(* [comment removed for export] *)
Lemma FIN M5 model5 LK5 Aw5 st5 cr5 kbb5 (fx5 : FPState) R5 :
  NM M5 model5 LK5 Aw5 st5 ESO QE0 cr5 -> REGSA R5 -> xinvA M5 (PQMA.a_kb st5) kbb5 ->
  NEMA.ndest (PQMA.a_lv st5) = NEMA.ndest (PQMA.a_lv sa) -> PQMA.nlv st5 = PQMA.nlv sa + 1 -> PQMA.kbsize st5 <= PQMA.kbsize sa + 2 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb2fa8 M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_163 ())). Qed.

(* [comment removed for export] *)
Lemma NPUSH M1 model1 LK1 Aw1 st1 cr1 kbb1 (fx1 fx2 : FPState) R1 R2 (pc0 ra ch : Z) (M2v : mem) (KS : list nat) :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSA R1 -> xinvA M1 (PQMA.a_kb st1) kbb1 ->
  msteps RSEGS (st fx1 R1 pc0 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 0xf4640 M2v) -> mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall i, 0 <= i < 2 ^ 64 -> M2v (Z_to_bv 64 i) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 i)) ->
  (forall x, In x KS -> getr R2 (reg x) = getr R1 (reg x)) -> subl IXA KS = true ->
  getr R2 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R2 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R2 (reg 11) = Z_to_bv 64 ch -> 0 <= ch < 128 ->
  PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + 2 ->
  (forall (fx6 : FPState) R6 (M6 : mem) model6 LK6 Aw6 x' g' cr6,
      NM M6 model6 LK6 Aw6 (s_set false st1 x' g') ESO QE0 cr6 -> PM.vs_size x' = PQMA.kbsize st1 + 1 -> REGSA R6 -> regs_preserved R2 R6 -> xinvA M6 x' (kbb1 ++ [ch]) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 ra M6 model6) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_164 ())). Qed.

(* [comment removed for export] *)
Lemma OPENCH (arm : bool) M1 model1 LK1 Aw1 st1 cr1 kbb1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSA R1 -> xinvA M1 (PQMA.a_kb st1) kbb1 -> getr R1 (reg 8) = Z_to_bv 64 (if arm then oa + 48 else oa) ->
  NEMA.ndest (PQMA.a_lv st1) = NEMA.ndest (PQMA.a_lv sa) -> PQMA.nlv st1 = PQMA.nlv sa + 1 -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + 2 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if arm then 0xb2f44 else 0xb2f9c) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_165 ())). Qed.

(* [comment removed for export] *)
Lemma ENC M1 model1 LK1 Aw1 st1 cr1 kbb1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSD R1 -> xinvA M1 (PQMA.a_kb st1) kbb1 ->
  NEMA.ndest (PQMA.a_lv st1) = NEMA.ndest (PQMA.a_lv sa) + 1 -> PQMA.nlv st1 = PQMA.nlv sa + 1 -> PQMA.kbsize st1 = PQMA.kbsize sa ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb2fc8 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_166 ())). Qed.

(* [comment removed for export] *)
Lemma xlv M1 model1 LK1 Aw1 st1 cr1 (M3 : mem) kbb1 :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> xinvA M1 (PQMA.a_kb st1) kbb1 ->
  L5CA.ahpres L ar (((PM.vs_own (PQMA.a_key st1) ++ PM.vs_own (PQMA.a_kb st1)) ++ ESO) ++ LBX0) FF spc (PMSPA.pm_scr 0) [(oa + 72, 24)] M1 M3 ->
  xinvA M3 (PQMA.a_kb st1) kbb1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_167 ())). Qed.

(* [comment removed for export] *)
Lemma PUSHLV M1 model1 LK1 Aw1 st1 cr1 kbb1 (fx1 : FPState) R1 (ra t : Z) :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSA R1 -> xinvA M1 (PQMA.a_kb st1) kbb1 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> getr R1 (reg 10) = Z_to_bv 64 (oa + 72) -> getr R1 (reg 11) = Z_to_bv 64 (spc + 12) -> getr R1 (reg 12) = Z_to_bv 64 (spc + 8) ->
  L5.u32_at RSEGS M1 (spc + 12) t -> L5.u32_at RSEGS M1 (spc + 8) 2 ->
  ((ra = 0xb2f44 /\ t = 1 /\ getr R1 (reg 8) = Z_to_bv 64 (oa + 48)) \/ (ra = 0xb2f9c /\ t = 1 /\ getr R1 (reg 8) = Z_to_bv 64 oa) \/ (ra = 0xb2fc8 /\ t = 0 /\ getr R1 (reg 8) = Z_to_bv 64 oa /\ PQMA.kbsize st1 = PQMA.kbsize sa /\ REGSD R1)) ->
  PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + 2 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb84e8 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_168 ())). Qed.

(* [comment removed for export] *)
Definition S2V (arm : bool) : Z := if arm then 2 else 1.
Lemma COMMA (arm : bool) M1 model1 LK1 Aw1 cr1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 sa ESO QE0 cr1 -> REGSA R1 -> xinvA M1 (PQMA.a_kb sa) kbb ->
  getr R1 (reg 1) = Z_to_bv 64 (if arm then 0xb2f28 else 0xb2f80) -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 44 ->
  getr R1 (reg 8) = Z_to_bv 64 (if arm then oa + 48 else oa) -> getr R1 (reg 9) = Z_to_bv 64 (oa + 72) -> getr R1 (reg 18) = Z_to_bv 64 (S2V arm) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xf4640 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_169 ())). Qed.

(* [comment removed for export] *)
Lemma DISP1 M1 model1 LK1 Aw1 cr1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 sa ESO QE0 cr1 -> REGSD R1 -> xinvA M1 (PQMA.a_kb sa) kbb -> getr R1 (reg 10) = Z_to_bv 64 (oa + 80) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb2e98 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_170 ())). Qed.
(* [comment removed for export] *)
Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb2e40 M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_171 ())). Qed.

End Run.


Theorem begin_object_ok : PNVA.v_begin_object_spec RSEGS AD AQ AAD AE L ar HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBo ()) ["WithHeap"] (Mh_0270_blobs1.kr_b_172 ())). Qed.

End WithHeap.
End PQAABO.


End PnAAdBo.
Module PnAAdBt.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdStrCK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0234. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObjA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAdStrCK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKSlotA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKCallA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKStepA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKFromA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKEncNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKSlotA3bN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemFrameA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0234.PnAAdBtP1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0234.PnAAdBtP2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201.PnAAdBtP3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201.PnAAdBtP4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201.PnAAdBtP5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201.PnAAdBtP6 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201.PnAAdBtP7 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016.Na0_code_rb5b6c_b5b70.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdBt () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA6b64lenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lebC69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_binC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA3agAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2or00K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG37bvu_rngC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityI47Corelib4Init5Logic5False00C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7enc_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA4PMEAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8pot_encAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA;epot_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;pot_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7pot_aeAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT9pot_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8sink_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ec_stateAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092;PnQStaticsA5PQSTA7err_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_KBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5VIS_HC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib6ZArith4Zdiv:Z_mod_multI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38obj_pf_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT:b64len_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA7view_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT4OWNEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5own13C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3OCEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7ocell13C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;own13_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5V2_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxc69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT;hdr_str_le5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT;hdr_bin_le5C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT9DKB_factsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List6filterC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_tC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5lv_eoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl01C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List:filter_appC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3advC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ndestC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT8agA_reflC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT2XVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6frb_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_objC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT9agA_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5a_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_WAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4EVISC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5xv_ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5HSPCfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAadd_nonneg_nonnegC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT6pv_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT4VOKfC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_applC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5xinvGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3ESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6kbsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_oaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7alvl_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP58PQAABTP57alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6set_lvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT9ndest_advC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5s_xlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6s_advXC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC69OSSVerify5KrLib7Mh_02019PnAAdBtP58PQAABTP5=qvtAk2e0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP58PQAABTP5=qvtAk2e1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP58PQAABTP5=qvtAk1e1_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3IXAC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3LSZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP58PQAABTP5;KS_qvtAk2e0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP58PQAABTP5;KS_qvtAk2e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02019PnAAdBtP58PQAABTP5;KS_qvtAk1e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_setC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT:mem_eq_frzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N8pb_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N6pb_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_restC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_app_asciiC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7s_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_xcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_kcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N9s_call_sCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3IXBC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8AOFF_KEYC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP2;qvtCqV_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG38regl_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3ADVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5PUSHQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT8DKB_DPHIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP29KS_qvtCqVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT4EST0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP29qvtC_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP27KS_qvtCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP2;qvtCqK_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5COLONC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP29KS_qvtCqKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multK46Stdlib9micromega=RingMicromega3Op206C69OSSVerify5KrLib7Mh_01028NemModel3NEM5asciiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N9s_key_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7src_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ins_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7ins_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA8src_okCAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3CQVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3CQKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5INS_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lv_shapeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_kbgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP2:qvtQV_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT4INS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP2:qvtQK_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4GMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP28KS_qvtQVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02349PnAAdBtP28PQAABTP28KS_qvtQKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT5QUOTEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8lv_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N:lv_last_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT6KEYB64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT6PATH_DC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lv_rootC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT2IXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5aeownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA=args_bstr_tagC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8pre_bstrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA9args_viewC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA6b64lenC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lc69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT:u64_at_injC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6cls_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;evis_of_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3phiC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6edepthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdBt6PQAABT3RUNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_v_bstr_tagC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA?v_bstr_tag_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA9step_bstrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00". Local Ltac lia := L5FastLia.plia.

Module PQAABT.
Import L5A L5SAR PQAKS3N PQAKC3N PQAKT3N PQAKG3 PQAKENA PQAKS3BN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
(* [comment removed for export] *)
Ltac flia := solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ].
Ltac fd := first [assumption | flia].
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AQ := PnLayoutQA.QADDR_A.
Abbreviation AE := NemLayoutA.NEADDR_A.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation adaptor_at := (PQMA.adaptor_at RSEGS AD accA annA (qa_vp_adaptor AQ)).
Abbreviation kcontent := (NEM.kcontent RSEGS).
Abbreviation bvu x := (bv_unsigned x).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u64_at_inj (M0 : mem) a v w : L5.u64_at RSEGS M0 a v -> L5.u64_at RSEGS M0 a w -> 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> v = w.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) [] (Mh_0270_blobs1.kr_b_173 ())). Qed.
Lemma b64len_rng n : 0 <= n -> 0 <= PQVA.b64len n <= 2 * n + 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) [] (Mh_0270_blobs1.kr_b_174 ())). Qed.
(* [comment removed for export] *)
Lemma hdr_str_le5 m : NEM.hdr_str m <= 5.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) [] (Mh_0270_blobs1.kr_b_175 ())). Qed.
Lemma hdr_bin_le5 m : NEM.hdr_bin m <= 5.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) [] (Mh_0270_blobs1.kr_b_176 ())). Qed.
(* [comment removed for export] *)
Lemma agA_trans (M0 M1 M2 : mem) a n : PMFA.agA M0 M1 a n -> PMFA.agA M1 M2 a n -> PMFA.agA M0 M2 a n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) [] (Mh_0270_blobs1.kr_b_177 ())). Qed.

(* [comment removed for export] *)
Lemma aacc_join (Mx : mem) p n m : aacc Mx p n -> aacc Mx (p + n) m -> 0 <= n -> aacc Mx p (n + m).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) [] (Mh_0270_blobs1.kr_b_178 ())). Qed.
Lemma aacc_sub (Mx : mem) a0 n0 a1 n1 : aacc Mx a0 n0 -> a0 <= a1 -> a1 + n1 <= a0 + n0 -> aacc Mx a1 n1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) [] (Mh_0270_blobs1.kr_b_179 ())). Qed.

(* [comment removed for export] *)
Lemma mem_eq_frz (Ma Mb : mem) : (forall a, 0 <= a < 2 ^ 64 -> ~ False -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> Mb = Ma.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) [] (Mh_0270_blobs1.kr_b_180 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
(* [comment removed for export] *)
Hypothesis PB : PQASCA.pb_specCA RSEGS AD L ar HI 0xf4640.
Hypothesis B64C : PQASCB.b64_specCA RSEGS AD L ar HI 0xbebe4 0x26613.
Hypothesis INSI : PQASCA.ins_specCA RSEGS AD L ar HI 0xb95f0.
Hypothesis VBE : NECSA.v_bstr_tag_spec RSEGS AD AQ AAD AE L ar HI (NESKA.PMEA L).
Hypothesis VKE : NECSA.v_key_spec RSEGS AD AQ AAD AE L ar HI (NESKA.PMEA L).

(* [comment removed for export] *)
Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (V2 cls r oa ov osk oec cat tg ctx pv d n : Z) (sa : PQMA.ast) (kbb : list Z) (en : NEM.enc) (k : NESK.sink) (bf ef : bool).
Local Notation sp := (V2 + cls).
Local Notation spc := (V2 - 160).
Local Notation EPOT := (NECSA.pot_encA L ar (NESKA.PMEA L)).
(* [comment removed for export] *)
Local Notation ESO := (NECS.eown en k).
Local Notation QE := (NECSA.pot_encA L ar (NESKA.PMEA L) en k).
Local Notation ST0 := (NEMA.AEST sa kbb en k).
(* [comment removed for export] *)
Local Notation NB := (PQVA.b64len n).
Local Notation DKB := (PQVA.b64len n + 4).
Local Notation DPHI := (Z.max (PQVA.b64len n + 5) (n + 6)).
Hypothesis Hcls : cls = 0 \/ cls = 16.
Hypothesis V32 : V2 mod 32 = 0.
Hypothesis HH : ri_inv HI ((PQMA.aown sa ++ ESO) ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r PNVA.VIS_H.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM PNVA.VIS_H FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 oa.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 pv.
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 tg.
Hypothesis TG0 : tg = 0.
Hypothesis A13 : getr R (reg 13) = Z_to_bv 64 ctx.
Hypothesis Hctx : 0 <= ctx < 2 ^ 64.
Hypothesis A14 : getr R (reg 14) = Z_to_bv 64 oec.
Hypothesis APV : PMSPA.aobjA FF pv 16.
Hypothesis VOK : PNVA.view_ok RSEGS M FF LBX oa ov osk pv d n.
Hypothesis Hn26 : 0 <= n < 2 ^ 26.   (* [comment removed for export] *)
Hypothesis AO : PMSPA.aobjA FF oa PQMA.ASIZE.
Hypothesis O8 : oa mod 8 = 0.
Hypothesis AOV : PMSPA.aobjA FF ov 56.
Hypothesis OV8 : ov mod 8 = 0.
Hypothesis AOSK : PMSPA.aobjA FF osk 24.
Hypothesis OK8 : osk mod 8 = 0.
Hypothesis AOEC : PMSPA.aobjA FF oec 16.
Hypothesis OE8 : oec mod 8 = 0.
Hypothesis APT : oa + PQMA.ASIZE <= ov \/ ov + 56 <= oa.
Hypothesis APT2 : oa + PQMA.ASIZE <= osk \/ osk + 24 <= oa.
Hypothesis APT3 : oa + PQMA.ASIZE <= oec \/ oec + 16 <= oa.
Hypothesis APT4 : ov + 56 <= osk \/ osk + 24 <= ov.
Hypothesis APT5 : oec + 16 <= ov \/ ov + 56 <= oec.
Hypothesis APT6 : oec + 16 <= osk \/ osk + 24 <= oec.
Hypothesis AA : adaptor_at M oa ov sa.
Hypothesis OACC : accA M oa PQMA.ASIZE.
Hypothesis AOK : PQMA.adaptor_ok sa.
Hypothesis VIS : EVIS M ov.
Hypothesis BASE : PMSTA.base_okA RSEGS AD M.
(* [comment removed for export] *)
Hypothesis KC : kcontent M (oa + PQMA.AOFF_KB) (PQMA.a_kb sa) kbb.
Hypothesis U8 : utf8_valid kbb = true.
Hypothesis EDEP : NEM.en_depth en = NEMA.ndest (PQMA.a_lv sa).
Hypothesis ENA : NEMA.enc_atA RSEGS AE L ar M ov osk en.
Hypothesis SKA : NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) M osk k.
Hypothesis ECS : NEMA.ec_stateA RSEGS AD M oec bf cat.
Hypothesis ERR : PQSTA.err_okA RSEGS AD AAD AQ M ef.
Hypothesis PRE : PQMA.kbsize sa + DKB <= PQMA.SMB /\ DKB <= PQMA.SMK /\ NESK.sk_z k + DPHI <= NESK.SMZ.
Hypothesis CRF : PMSP.credit_le (NEMA.pot_aeA L ar ST0) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (st' : NEMA.aest) (b' e' : bool) (cr' : credit),
      regs_preserved R R' ->
      NEMA.ae_atA RSEGS AD AE L ar (qa_vp_adaptor AQ) M' oa ov osk st' -> NEMA.ae_ok st' -> NEMA.ec_stateA RSEGS AD M' oec b' cat -> PMSTA.base_okA RSEGS AD M' -> PQSTA.err_okA RSEGS AD AAD AQ M' e' ->
      (bf = true -> b' = true) -> (ef = true -> e' = true) ->
      (NEMA.nlv st' = NEMA.nlv ST0 /\ NEMA.kbsize st' <= NEMA.kbsize ST0 + DKB /\ NEMA.phi st' <= NEMA.phi ST0 + DPHI /\ NEMA.esize st' = NEMA.esize ST0
       /\ NEMA.edepth st' = NEMA.edepth ST0 /\ (b' = bf \/ False)) ->
      L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr PNVA.VIS_H) (NEMA.ae_WA AD oa ov osk oec) M M' ->
      PMSP.credit_keep cr cr' (NEMA.pot_aeA L ar ST0) (NEMA.pot_aeA L ar st') ->
      model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (NEMA.aeown st' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition OWNE (Mx : mem) : Prop := own13 sp R Mx /\ L5.u64_at RSEGS Mx (V2 - 136) oec.
Definition OCE (a : Z) : Prop := ocell13 sp a \/ (V2 - 136 <= a < V2 - 128).
Local Notation OWN := OWNE.
Local Notation OC := OCE.
(* [comment removed for export] *)
Lemma QENN : 0 <= fst QE /\ 0 <= snd QE.
Proof using LY ENA SKA.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_181 ())). Qed.
Local Notation "'SX' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Lemma pot_split x kb1 e1 k1 : NEMA.pot_aeA L ar (NEMA.AEST x kb1 e1 k1) = PM.credit_add (PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) x)) (EPOT e1 k1).
Proof using L ar.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_182 ())). Qed.
Lemma CR : PMSP.credit_le (PM.credit_add (PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) sa)) QE) cr.
Proof using CRF.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_183 ())). Qed.
Lemma xinv0 : PQAKENA.xinvG L ar oa ov osk oec cat M (PQMA.a_kb sa) kbb en k bf ef.
Proof using KC U8 ENA SKA ECS ERR.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_184 ())). Qed.

Lemma sp_facts : 140735332487264 + 16 <= V2 /\ V2 + cls <= 140737488355328 /\ (V2 + cls) mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof using ENT Hcls.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_185 ())). Qed.
Lemma V2_lo : 140735332487328 <= V2.
Proof using ENT Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_186 ())). Qed.
Lemma HSPCf : sp - 2048 <= spc /\ spc mod 16 = 0.
Proof using Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_187 ())). Qed.
Lemma oec_rng : 7036928 <= oec /\ oec + 16 <= 2 ^ 47.
Proof using LY HIok HH AOEC.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_188 ())). Qed.
Lemma oa_lo96 : 7036928 <= oa /\ oa + 96 <= 2 ^ 47.
Proof using LY HIok HH AO.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_189 ())). Qed.
Lemma ov_rng56 : 7036928 <= ov /\ ov + 56 <= ahl_ceil ar /\ ov + 56 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784).
Proof using LY HIok HH AOV.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_190 ())). Qed.
Lemma tg_rng : 0 <= tg < 2 ^ 64.
Proof using TG0.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_191 ())). Qed.
(* [comment removed for export] *)
Lemma DKB_facts : 0 <= NB /\ 0 <= n < 2 ^ 26 /\ NB <= 2 * n + 1.
Proof using Hn26.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_192 ())). Qed.
(* [comment removed for export] *)
Lemma VOKf : L5.u64_at RSEGS M pv d /\ L5.u64_at RSEGS M (pv + 8) n /\ L5.defined M d n /\ accA M pv 16 /\ accA M d n
  /\ (n = 0 \/ PGS.in_blk LBX d n \/ PMSPA.aobjA FF d n) /\ (pv + 16 <= oa \/ oa + PQMA.ASIZE <= pv) /\ (d + n <= oa \/ oa + PQMA.ASIZE <= d)
  /\ (pv + 16 <= ov \/ ov + 56 <= pv) /\ (d + n <= ov \/ ov + 56 <= d) /\ (pv + 16 <= osk \/ osk + 24 <= pv) /\ (d + n <= osk \/ osk + 24 <= d) /\ 0 <= d /\ d + n <= 2 ^ 47.
Proof using VOK.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_193 ())). Qed.
Lemma pv_rng : 7036928 <= pv /\ pv + 16 <= 2 ^ 47.
Proof using LY HIok HH APV.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_194 ())). Qed.
Lemma GOWNE : forall Ma Mb, OWN Ma -> (forall a, OC a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> OWN Mb.
Proof using ENT Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_195 ())). Qed.

(* [comment removed for export] *)
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK Aw sp (PMSPA.pm_scr PNVA.VIS_H) spc (V2 - 136) sp OC OWN F fl 1 LK2 M2 model2 cr (PQMA.aown sa ++ ESO).
Hypothesis APART : forall a n0 sp0 scr0, (forall i, 0 <= i < n0 -> aclient L ar ((PQMA.aown sa ++ ESO) ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n0 ->
         (a + n0 <= F \/ F + ff_bytes 1 <= a) /\ (a + n0 <= F / 8 + SB \/ F / 8 + SB + ff_bytes 1 / 8 <= a) /\ (a + n0 <= fl \/ fl + 1 <= a).
Local Notation FF' := ((F, 1, spc + 32) :: FF).
Local Notation AMF := (PQAKS3N.a_mem L ar HI M model LBX FF LK Aw cr sp oa ov osk oec sa QE spc OWN 1 F).
Local Notation xinv := (PQAKENA.xinvG L ar oa ov osk oec cat).
Local Notation "'SF' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE spc (V2 - 136) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).
Local Notation "'SE' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE cat OV8 OK8 OE8 APT2 APT3 APT4 APT5 APT6 spc (V2 - 136) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).
Local Notation "'SY' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE cat APT2 APT3 spc (V2 - 136) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).
Local Notation "'SV' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE spc (V2 - 136) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf pv d n APV VOK) (at level 10, f at level 9, only parsing).
Local Notation "'GF' f" := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r PNVA.VIS_H (PQMA.aown sa ++ ESO) (NEMA.ae_WA AD oa ov osk oec) HH AM K0 ENT FRM FRS PQAKS3N.Hh3 (SX PQAKS3N.wappW) spc (V2 - 136) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Definition vals (j : nat) : Z :=
  match j with 2%nat => spc | 3%nat => pa_gp AD | 4%nat => hl_tp L | 8%nat => sp | 9%nat => spc | 18%nat => F | 19%nat => oa + 80 | 20%nat => oa | 21%nat => ctx
             | 22%nat => (oa + 80) / 8 + 2147450880 | 23%nat => tg | 24%nat => pv | 25%nat => F / 8 + 2147450880 | 26%nat => F | 27%nat => 2147450880 | _ => 0 end.
Definition IXA : list nat := [2; 3; 4; 8; 9; 18; 19; 22; 25; 26; 27]%nat.
Definition IX : list nat := (20 :: 21 :: 23 :: 24 :: IXA)%nat.
Definition IXB : list nat := (20 :: IXA)%nat.
Local Notation REGSA := (regl IXA vals).
Local Notation REGS := (regl IX vals).
Local Notation REGSB := (regl IXB vals).

(* [comment removed for export] *)
Ltac pf LM :=
  let BIx := fresh "BIx" in pose proof (proj1 LM) as BIx;
  destruct ((GF PQAKR3.g_pfacts) _ _ _ _ _ _ BIx) as ((PF1 & PF2 & PF3 & PF4 & _) & (FD & FW & FSW & FLU & FLW) & (PL1 & PL2 & PL3 & PL4) & (SW & OWNV & PS1 & PS2 & PS3 & PS4) & (CSB & CUAR & _) & (AVSH & AVF & AVS));
  change (ff_bytes 1) with 128 in *; change (128 / 8) with 16 in *.

(* [comment removed for export] *)
Definition EST (en1 : NEM.enc) (k1 : NESK.sink) (b1 e1 : bool) : Prop :=
  NEM.en_n en1 = NEM.en_n en /\ NEM.en_depth en1 = NEM.en_depth en /\ NESK.sk_z k <= NESK.sk_z k1
  /\ (bf = true -> b1 = true) /\ (ef = true -> e1 = true) /\ (b1 = bf \/ False).
Lemma EST0 : EST en k bf ef.
Proof using TG0.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_196 ())). Qed.
Lemma DKB_DPHI : DKB + 1 <= DPHI /\ NEM.hdr_str NB + NB <= DPHI /\ NEM.hdr_bin n + n <= DPHI.
Proof using Hn26.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_197 ())). Qed.
(* [comment removed for export] *)
Lemma ndest_adv lv0 c : NEMA.ndest (lv0 ++ [PQAKS3N.adv c]) = NEMA.ndest (lv0 ++ [c]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_198 ())). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition XV (Mx : mem) : Prop := PMFA.agA M Mx pv 16 /\ (PMSPA.aobjA FF d n -> PMFA.agA M Mx d n).
Lemma agA_refl (Mx : mem) a m : PMFA.agA Mx Mx a m.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_199 ())). Qed.
Lemma xv0 : XV M.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_200 ())). Qed.
(* [comment removed for export] *)
Ltac vf LM XVM :=
  destruct ((SV PQAKS3BN.s_pv) _ _ _ _ _ _ _ _ LM (proj1 XVM)) as ((PV1 & PV2 & PV3 & PV4 & PV5) & (PW0 & PW8) & (PZ0 & PZ8) & (Hd1 & Hd2 & Hn1) & PVO & (PVF & PSF0 & PSF8));
  change (ff_bytes 1) with 128 in PVF; change (ff_bytes 1 / 8) with 16 in PSF0, PSF8.

(* [comment removed for export] *)
Lemma xv_ek LB1 spx scr W (M1 M3 : mem) :
  L5SAR.ek L ar LB1 FF spx scr W M1 M3 -> PMKA.wapp W ->
  (forall i, pv <= i < pv + 16 -> L5.outside W i) -> (PMSPA.aobjA FF d n -> forall i, d <= i < d + n -> L5.outside W i) -> XV M1 -> XV M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_201 ())). Qed.
(* [comment removed for export] *)
Lemma xvF M1 model1 LK1 Aw1 st1 eso1 qe1 cr1 (M3 : mem) (Wp : Z -> Prop) :
  AMF M1 model1 LK1 Aw1 st1 eso1 qe1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (spc <= a < sp) \/ (F <= a < F + ff_bytes 1) \/ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 1 / 8)) ->
  XV M1 -> XV M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_202 ())). Qed.
(* [comment removed for export] *)
Lemma xv_ptw (M1 M3 : mem) (Wx : Z -> Prop) :
  (forall i, 0 <= i < 2 ^ 64 -> ~ Wx i -> M3 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) ->
  (forall i, pv <= i < pv + 16 -> ~ Wx i /\ ~ Wx (HeapIfaceA.S i)) ->
  (PMSPA.aobjA FF d n -> forall i, d <= i < d + n -> ~ Wx i /\ ~ Wx (HeapIfaceA.S i)) ->
  XV M1 -> XV M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_203 ())). Qed.

(* [comment removed for export] *)
Lemma FIN M5 model5 LK5 Aw5 st5 cr5 kbb5 en5 k5 (b5 e5 : bool) (fx5 : FPState) R5 :
  AMF M5 model5 LK5 Aw5 st5 (NECS.eown en5 k5) (EPOT en5 k5) cr5 -> REGSA R5 -> xinv M5 (PQMA.a_kb st5) kbb5 en5 k5 b5 e5 -> EST en5 k5 b5 e5 ->
  PQMA.nlv st5 = PQMA.nlv sa -> PQMA.kbsize st5 <= PQMA.kbsize sa + DKB -> PQMA.kbsize st5 + NESK.sk_z k5 <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st5) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb59a8 M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_204 ())). Qed.


(* [comment removed for export] *)
Lemma ADV M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 en1 k1 (b1 e1 : bool) (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 (NECS.eown en1 k1) (EPOT en1 k1) cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en1 k1 b1 e1 -> EST en1 k1 b1 e1 ->
  PQMA.a_lv st1 = lv0 ++ [c] ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 <= PQMA.kbsize sa + DKB -> PQMA.kbsize st1 + NESK.sk_z k1 <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st1) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5930 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_205 ())). Qed.


(* [comment removed for export] *)
Ltac of LM ELV :=
  destruct ((SF PQAKS3N.s_oa) _ _ _ _ _ _ _ _ LM) as ((OA1 & OA2 & OA3 & OA4 & OA5) & OAZ & O16 & (OV1 & OV2 & OV3 & OV4 & OVZ & OVW) & IMG & VTZ & (OAF & OVF & OASF & OVSF) & (OAV & OAW));
  destruct ((SF PQAKS3N.s_lv) _ _ _ _ _ _ _ _ _ _ LM ELV) as (E80 & (E1 & E2 & E8 & E4 & E5) & (Z24 & Z20 & Z16 & Z8) & (CT & CK & CEO) & (CD & CW & CVIS) & (EO1 & EF1 & EV1) & ((CTR & CKR & CER & CKE) & CT1) & INL & EHI);
  change (ff_bytes 1) with 128 in OAF, OVF; change (ff_bytes 1 / 8) with 16 in OASF, OVSF.

(* [comment removed for export] *)
Lemma PATH_D M1 model1 LK1 Aw1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> XV M1 -> PQMA.a_lv sa = lv0 ++ [c] -> PQMA.lv_t c = 0 -> PQMA.lv_eo c = 1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5404 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_206 ())). Qed.

(* [comment removed for export] *)
Lemma PUSHQ M1 model1 LK1 Aw1 st1 cr1 kbb1 kcs (fx1 fx2 : FPState) R1 R2 (pc0 ra ch : Z) (M2v : mem) (KS : list nat) :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs ->
  msteps RSEGS (st fx1 R1 pc0 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 0xf4640 M2v) -> mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall i, 0 <= i < 2 ^ 64 -> M2v (Z_to_bv 64 i) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 i)) ->
  (forall x, In x KS -> getr R2 (reg x) = getr R1 (reg x)) -> subl IXB KS = true ->
  getr R2 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R2 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R2 (reg 11) = Z_to_bv 64 ch -> 0 <= ch < 128 ->
  getr R2 (reg 21) = Z_to_bv 64 (oa + 48) ->
  PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + DKB ->
  (forall (fx6 : FPState) R6 (M6 : mem) model6 LK6 Aw6 x' g' cr6,
      AMF M6 model6 LK6 Aw6 (s_set false st1 x' g') ESO QE cr6 -> PM.vs_size x' = PQMA.kbsize st1 + 1 -> REGSB R6 -> getr R6 (reg 21) = Z_to_bv 64 (oa + 48) ->
      xinv M6 x' (kbb1 ++ [ch]) en k bf ef -> kcontent M6 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 ra M6 model6) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_207 ())). Qed.

(* [comment removed for export] *)
Lemma CQV M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs ->
  getr R1 (reg 21) = Z_to_bv 64 (oa + 48) -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + DKB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb57f0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_208 ())). Qed.
(* [comment removed for export] *)
Lemma COLON M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs ->
  getr R1 (reg 21) = Z_to_bv 64 (oa + 48) -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + DKB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5924 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_209 ())). Qed.
(* [comment removed for export] *)
Lemma CQK M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs ->
  getr R1 (reg 21) = Z_to_bv 64 (oa + 48) -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 2 <= PQMA.kbsize sa + DKB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5918 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_210 ())). Qed.

(* [comment removed for export] *)
Lemma div2_2 m : (2 * m) / 2 = m.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_211 ())). Qed.
(* [comment removed for export] *)
Lemma INS_CALL (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 (ra v11 v12 v13 v14 : Z) :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48) ->
  ra = (if arm then 0xb57f0 else 0xb5918) ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 v11 -> getr R1 (reg 12) = Z_to_bv 64 v12 ->
  getr R1 (reg 13) = Z_to_bv 64 v13 -> getr R1 (reg 14) = Z_to_bv 64 v14 ->
  v11 = PM.vs_data (oa + 48) (PQMA.a_kb st1) + PM.vs_size (PQMA.a_kb st1) -> v12 = PM.vs_data (oa + 24) (PQMA.a_key st1) ->
  v13 = v12 + v14 -> v14 = PM.vs_size (PQMA.a_key st1) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + v14 + (if arm then 1 else 2) <= PQMA.kbsize sa + DKB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb95f0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_212 ())). Qed.

Lemma INS2 (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + PM.vs_size (PQMA.a_key st1) + (if arm then 1 else 2) <= PQMA.kbsize sa + DKB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if arm then 0xb55d4 else 0xb563c) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_213 ())). Qed.

(* [comment removed for export] *)
Lemma KDEST M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.lv_t c = 0 -> PQMA.lv_eo c = 0 ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 = PQMA.kbsize sa -> PM.vs_size (PQMA.a_key st1) = NB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5534 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_214 ())). Qed.

(* [comment removed for export] *)
Lemma QUOTE (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = true -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + 1 + PM.vs_size (PQMA.a_key st1) + (if arm then 1 else 2) <= PQMA.kbsize sa + DKB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if arm then 0xb55c8 else 0xb562c) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_215 ())). Qed.

(* [comment removed for export] *)
Lemma COMMA (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = true -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  getr R1 (reg 1) = Z_to_bv 64 (if arm then 0xb55c8 else 0xb562c) -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 44 ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + 2 + PM.vs_size (PQMA.a_key st1) + (if arm then 1 else 2) <= PQMA.kbsize sa + DKB -> 0 <= PM.vs_size (PQMA.a_key st1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xf4640 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_216 ())). Qed.

(* [comment removed for export] *)
Lemma DISP2 M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> (PQMA.lv_eo c = 0 \/ PQMA.lv_t c = 1) ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 = PQMA.kbsize sa -> PM.vs_size (PQMA.a_key st1) = NB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5534 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_217 ())). Qed.

(* [comment removed for export] *)
Lemma KEYB64 M1 model1 LK1 Aw1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> XV M1 -> PQMA.a_lv sa = lv0 ++ [c] -> (PQMA.lv_eo c = 0 \/ PQMA.lv_t c = 1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5404 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_218 ())). Qed.

(* [comment removed for export] *)
Lemma DISP1 M1 model1 LK1 Aw1 cr1 kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> XV M1 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5404 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_219 ())). Qed.

(* [comment removed for export] *)
Lemma SETUP Mx modelx LKx Awx (fx2 : FPState) R2 :
  AMF Mx modelx LKx Awx sa ESO QE cr -> xinv Mx (PQMA.a_kb sa) kbb en k bf ef -> XV Mx ->
  getr R2 (reg 2) = Z_to_bv 64 spc -> getr R2 (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R2 (reg 8) = Z_to_bv 64 sp ->
  getr R2 (reg 9) = Z_to_bv 64 spc -> getr R2 (reg 10) = Z_to_bv 64 F -> getr R2 (reg 20) = Z_to_bv 64 oa -> getr R2 (reg 21) = Z_to_bv 64 ctx -> getr R2 (reg 23) = Z_to_bv 64 tg -> getr R2 (reg 24) = Z_to_bv 64 pv ->
  getr R2 (reg 27) = Z_to_bv 64 2147450880 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0xb5350 Mx modelx) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_220 ())). Qed.


End Frame.

(* [comment removed for export] *)
Ltac enter_tac Aconc fxv MVv HRgp HRtp :=
  pose proof (LF2CBN( Aconc fxv R MVv (fun j : nat => match j with 2%nat => V2 | _ => 0 end) )) as P;
  L5SAR.feed P ltac:(fd);
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T20 & T21 & T23 & T24 & T27 & CEC & C27 & C26 & C25 & C24 & C23 & C22 & C21 & C20 & C19 & C18 & C9 & C8 & C1 & C0);
  apply ((SX PQAKS3N.s_enterX) spc (V2 - 136) sp OC OWN 1 fxv fx1 R1 0xb5280 742144 M1v CR);
  [ right; left; reflexivity | flia | exact (proj2 HSPCf) | flia | flia | flia | intros a Ha; unfold OCE, ocell13 in Ha; destruct Ha as [Ha|Ha]; flia
  | exact GOWNE
  | exact MS1 | exact MG1 | intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; flia]
  | intros M1 VIS1 AV; unfold OWNE, own13; split;
    [ repeat match goal with |- _ /\ _ => split end;
      (match goal with |- L5.u64_at _ _ ?a0 ?v0 => apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a0 v0 (AV a0 8 ltac:(flia) ltac:(flia)) ltac:(flia) ltac:(flia))) end; rewrite VIS1;
       match goal with |- L5.u64_at _ _ ?a _ => first [ replace a with (V2 + 8) by flia; assumption
          | replace a with V2 by flia; assumption
          | replace a with (V2 - 8) by flia; assumption
          | replace a with (V2 - 16) by flia; assumption
          | replace a with (V2 - 24) by flia; assumption
          | replace a with (V2 - 32) by flia; assumption
          | replace a with (V2 - 40) by flia; assumption
          | replace a with (V2 - 48) by flia; assumption
          | replace a with (V2 - 56) by flia; assumption
          | replace a with (V2 - 64) by flia; assumption
          | replace a with (V2 - 72) by flia; assumption
          | replace a with (V2 - 80) by flia; assumption
          | replace a with (V2 - 88) by flia; assumption
          | replace a with (V2 - 96) by flia; assumption
          | replace a with (V2 - 104) by flia; assumption ] end)
    | apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 (V2 - 136) oec (AV (V2 - 136) 8 ltac:(flia) ltac:(flia)) ltac:(flia) ltac:(flia))); rewrite VIS1;
      rewrite A14 in CEC; rewrite (L5.unsigned_lit oec) in CEC by flia; exact CEC ]
  | exact T2 | apply KS1; inl | exact T1 | reflexivity | flia |];
  intros R2 M2 model2 F fl LK2 G APART LM2 EK2 G10 RP2 _;
  apply (SETUP F fl LK2 M2 model2 G APART M2 model2 LK2 Aw fx1 R2 LM2);
  [ apply (PQAKENA.xinv_ekF L ar C HI LY HIok oa ov osk oec cat (proj1 oa_lo96) _ FF sp (PMSPA.pm_scr PNVA.VIS_H) M M2 sa kbb en k bf ef
             (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) AO AOV AOSK AOEC AA
             ltac:(apply incl_appl; apply incl_appl; apply incl_refl) ltac:(apply incl_appl; apply incl_appr; unfold NECS.eown; apply incl_appl; apply incl_refl)
             ltac:(apply incl_appl; apply incl_appr; unfold NECS.eown; apply incl_appr; apply incl_refl) EK2 xinv0)
  | exact (xv_ek _ sp (PMSPA.pm_scr PNVA.VIS_H) [] M M2 EK2 PMKA.wapp_nil ltac:(intros i _ rr []) ltac:(intros _ i _ rr []) xv0)
  | rewrite (L5SAR.cs_of_preserved _ _ 2%nat RP2 ltac:(inl)); exact T2
  | rewrite (L5SAR.cs_of_preserved _ _ 3%nat RP2 ltac:(inl)); rewrite (KS1 3%nat) by inl; exact HRgp
  | rewrite (L5SAR.cs_of_preserved _ _ 4%nat RP2 ltac:(inl)); rewrite (KS1 4%nat) by inl; exact HRtp
  | rewrite (L5SAR.cs_of_preserved _ _ 8%nat RP2 ltac:(inl)); rewrite T8; f_equal; flia
  | rewrite (L5SAR.cs_of_preserved _ _ 9%nat RP2 ltac:(inl)); exact T9
  | exact G10
  | rewrite (L5SAR.cs_of_preserved _ _ 20%nat RP2 ltac:(inl)); rewrite T20; exact A10
  | rewrite (L5SAR.cs_of_preserved _ _ 21%nat RP2 ltac:(inl)); rewrite T21; exact A13
  | rewrite (L5SAR.cs_of_preserved _ _ 23%nat RP2 ltac:(inl)); rewrite T23; exact A12
  | rewrite (L5SAR.cs_of_preserved _ _ 24%nat RP2 ltac:(inl)); rewrite T24; exact A11
  | rewrite (L5SAR.cs_of_preserved _ _ 27%nat RP2 ltac:(inl)); exact T27 ].

Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb52d0 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_221 ())). Qed.

End Run.

(* [comment removed for export] *)
Theorem bstr_tag_ok : PNVA.v_bstr_tag_spec RSEGS AD AQ AAD AE L ar HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBt ()) ["WithHeap"] (Mh_0270_blobs1.kr_b_222 ())). Qed.

End WithHeap.
End PQAABT.


End PnAAdBt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0189. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase.
Module PnAAdFuC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0189. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdStrCK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKSlotA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKStrA3c OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKStrA3d OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKFromA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0189.PnARel3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228.PnAAdFuP1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228.PnAAdFuP2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016.Na0_code_rb94bc_b94c0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAdStrCK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228.PnAAdFuDP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdFuC () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z>div_unique_posC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7div_divK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3M10C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA6ndig_fC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z4landC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL7inrangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC4ELinuxProcessSemantics5Riscv3Sem5alu64I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib;BigLinkBase2BL3zmdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9zmd_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zaluC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL:zalu_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5div10C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL6MM_valC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop04c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC7digit_qC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z9mod_smallC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions:bv_extractC45stdpp9bitvector;definitions6bv_subC45stdpp9bitvector;definitions9bv_signedC46Stdlib6ZArith4Zdiv:Zminus_modC45stdpp9bitvector;definitionsEbv_extract_0_unsignedC45stdpp9bitvector;definitions?bv_sub_unsignedC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions>bv_sign_extendC45stdpp9bitvector;definitionsGbv_sign_extend_unsignedc69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC8land_m49C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA6FROM_HC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR36obj_pfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_02137PnStepA4PMKA9wapp_consC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC7o_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5asciiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA4ndigC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7kstr_atC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4GMAXC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF38ndig_rngC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS3:kstr_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ45own12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_ctxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_consC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=aclient_casesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ47ocell12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_apart1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_pieceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3Hh2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5wappWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5HSPCfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6frb_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6brb_ofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3GEKC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_applc69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC6KSKEEPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4KCAPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC6KCKEEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3DGFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC8nd_factsC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z;div_le_monoC47Corelib7Classes?RelationClasses>eq_equivalenceC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multC46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrK46Stdlib9micromega=RingMicromega3Op206C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR3>g_callee_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02566PmAUar6PMAUAR:aobjA_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_pfactsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA9pb_specCAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR37g_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA5akeptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5RA_PBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC4PBPCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3IXPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5V2_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3OAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC69OSSVerify5KrLib7Mh_02289PnAAdFuP28PQAAFUP27alignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02567PmAUarK5PMAUK4gctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7cell_isC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8avis_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9u8_at_visC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C46Stdlib6ZArith4ZdivAZ_div_plus_full_lC56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC69OSSVerify5KrLib7Mh_01797L5DefsA3L5A<zeros_at_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR39zeros_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP28PQAAFUP2:qfuQB_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR36g_footC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflc69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3KSXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3KCXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC8DG_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC6PBCALLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR37g_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC2QBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02289PnAAdFuP28PQAAFUP28KS_qfuQBC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA8cle_keepC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib9PnAdStrCK6PQASCK9ascii_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA8ck_transC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3FINC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC5PBODYC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith6BinInt1Z4succC69OSSVerify5KrLib7Mh_02289PnAAdFuP28PQAAFUP2:qfuQR_concC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelc69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC7x_factsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib7Mh_02289PnAAdFuP28PQAAFUP28KS_qfuQRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS36cls_ofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdFuC7PQAAFUC3RUNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAdStrCA27PQASCA2<fromu_specCAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5SMMAXC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.
Local Ltac flia := L5FastLia.plia.
Local Ltac fd := first [assumption | flia].

Module PQAAFUC.
Import L5A L5SAR PQAKG3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation accA := PMSPA.accA.
Abbreviation kstr_at := (PQMA.kstr_at RSEGS accA).
Abbreviation kcontent := (NEM.kcontent RSEGS).
Abbreviation bvu x := (bv_unsigned x).
Import PQAKZ4.

(* [comment removed for export] *)
Definition N0 : Z := 0xb8fb0.
Definition RA_SM : Z := 0xb9020.
Definition LOOP : Z := 0xb9184.
Definition FORK : Z := 0xb91b0.
Definition QB : Z := 0xb9280.
Definition PBPC : Z := 0xf4640.
Definition RA_PB : Z := 0xb929c.
Definition THUNK : Z := 0x82834.
Definition RA_TH : Z := 0xb926c.
Definition RET : Z := 0xb93c8.
Definition M10 : Z := 14757395258967641293.

(* [comment removed for export] *)
Lemma div10 v : 0 <= v < 2 ^ 64 -> ((v * 14757395258967641293) / 2 ^ 64) / 8 = v / 10.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) [] (Mh_0270_blobs1.kr_b_223 ())). Qed.
Lemma to_bv_mod a : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) [] (Mh_0270_blobs1.kr_b_224 ())). Qed.
Lemma to_bv_congr a b : (a - b) mod 2 ^ 64 = 0 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) [] (Mh_0270_blobs1.kr_b_225 ())). Qed.
Lemma ndig_f_ge f v : 10 <= v -> PQVA.ndig_f (Datatypes.S f) v = 1 + PQVA.ndig_f f (v / 10).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) [] (Mh_0270_blobs1.kr_b_226 ())). Qed.
Lemma ndig_f_lt f v : v < 10 -> PQVA.ndig_f f v = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) [] (Mh_0270_blobs1.kr_b_227 ())). Qed.
Lemma ndig_f_ge1 f w : 1 <= PQVA.ndig_f f w.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) [] (Mh_0270_blobs1.kr_b_228 ())). Qed.
Lemma land_m49 d : 0 <= d < 10 -> Z.land d 18446744073709551567 = d.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) [] (Mh_0270_blobs1.kr_b_229 ())). Qed.
(* [comment removed for export] *)
Lemma digit_q (EE : AX2.env) (w : Z) :
  bv_unsigned (AX2.ev EE 36%nat) = w ->
  bv_unsigned (alu64 Instr.ALU_SRL (mul_div Instr.M_MULHU (AX2.ev EE 36%nat) (Z_to_bv 64 14757395258967641293)) (Z_to_bv 64 3)) = w / 10.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) [] (Mh_0270_blobs1.kr_b_230 ())). Qed.
Lemma digit_edenot (EE : AX2.env) (w : Z) :
  bv_unsigned (AX2.ev EE 36%nat) = w ->
  bv_unsigned (AX2.edenot EE (AX2.EAlu Instr.ALU_ADD (AX2.EAlu Instr.ALU_AND (AX2.EAluw Instr.ALU_SUB (AX2.EVar 36) (AX2.EMd Instr.M_MUL (AX2.ELit 10) (AX2.EAlu Instr.ALU_SRL (AX2.EMd Instr.M_MULHU (AX2.EVar 36) (AX2.ELit 14757395258967641293)) (AX2.ELit 3)))) (AX2.ELit (-49))) (AX2.ELit 48)))
  = 48 + w mod 10.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) [] (Mh_0270_blobs1.kr_b_231 ())). Qed.
Lemma u8_of_defined (Mx : mem) a : 0 <= a -> a + 1 <= 2 ^ 64 -> L5.defined Mx a 1 -> exists b, 0 <= b < 256 /\ L5.u8_at RSEGS Mx a b.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) [] (Mh_0270_blobs1.kr_b_232 ())). Qed.
(* [comment removed for export] *)
Definition KD : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 21; 24; 25; 26; 27]%nat.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Hypothesis PB : PQASCA.pb_specCA RSEGS AD L ar HI 0xf4640.

Lemma Hh2 : 1 <= PQASA.FROM_H <= 16.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"] (Mh_0270_blobs1.kr_b_233 ())). Qed.

(* [comment removed for export] *)
Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (V2 cls r o v SM g : Z) (x : PM.vstr) (bs : list Z).
Local Notation sp := (V2 + cls).
Local Notation spc := (V2 - 128).
Local Notation W := ([(o, 24)] : list L5.range).
Local Notation BX0 := (PM.vs_own x).
Local Notation ND := (PQVA.ndig v).
Hypothesis Hcls : cls = 0 \/ cls = 16.
Hypothesis V32 : V2 mod 32 = 0.
Hypothesis HH : ri_inv HI (BX0 ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r PQASA.FROM_H.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM PQASA.FROM_H FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 v.
Hypothesis Hv : 0 <= v < 2 ^ 64.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 o.
Hypothesis AO : PMSPA.aobjA FF o 24.
Hypothesis O8 : o mod 8 = 0.
Hypothesis KS : kstr_at M o x.
Hypothesis KC : kcontent M o x bs.
Hypothesis KOK : PQMA.ks_ok SM x g.
Hypothesis SMX : SM <= PQASA.SMMAX.
Hypothesis H20 : PM.vs_size x + 20 <= SM.
Hypothesis BASE : PMSTA.base_okA RSEGS AD M.
Hypothesis CR : PMSP.credit_le (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (x' : PM.vstr) (g' : Z) (cr' : credit) (ds : list Z),
    regs_preserved R R' -> kstr_at M' o x' -> kcontent M' o x' (bs ++ ds) -> NEM.ascii ds -> PQMA.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + ND ->
    L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr PQASA.FROM_H) W M M' ->
    PMSP.credit_keep cr cr' (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x' g')) ->
    model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
    ri_inv HI (PM.vs_own x' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Local Notation OWN := (own12 sp R).
Local Notation OC := (ocell12 sp).

(* [comment removed for export] *)
Lemma o_facts : 7036928 <= o /\ o + 24 <= ahl_ceil ar /\ o + 24 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= o \/ o + 24 <= 2147446784).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_234 ())). Qed.
Lemma wappW : PMKA.wapp W.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_235 ())). Qed.
(* [comment removed for export] *)
Local Notation "'GX' f" := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r PQASA.FROM_H BX0 W HH AM K0 ENT FRM FRS Hh2 wappW) (at level 10, f at level 9, only parsing).

Lemma sp_facts : 140735332487264 + 16 <= V2 /\ V2 + cls <= 140737488355328 /\ (V2 + cls) mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_236 ())). Qed.
Lemma V2_lo : 140735332487360 <= V2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_237 ())). Qed.
Lemma HSPCf : sp - 2048 <= spc /\ spc mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_238 ())). Qed.
Lemma x_facts : 0 <= PM.vs_size x <= SM /\ 0 <= g.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_239 ())). Qed.
Lemma nd_facts : 1 <= ND <= 20.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_240 ())). Qed.

(* [comment removed for export] *)
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK Aw sp (PMSPA.pm_scr PQASA.FROM_H) spc (sp - 96) sp OC OWN F fl 3 LK2 M2 model2 cr BX0.
Hypothesis APART : forall a n0 sp0 scr0, (forall i, 0 <= i < n0 -> aclient L ar (BX0 ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n0 ->
         (a + n0 <= F \/ F + ff_bytes 3 <= a) /\ (a + n0 <= F / 8 + SB \/ F / 8 + SB + ff_bytes 3 / 8 <= a) /\ (a + n0 <= fl \/ fl + 1 <= a).
Local Notation FF' := ((F, 3, spc + 32) :: FF).
(* [comment removed for export] *)
Local Notation GM := (PQAKR3.g_mem L ar HI M model LBX FF LK Aw sp PQASA.FROM_H W spc OWN 3 F).
Local Notation "'GF' f" := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r PQASA.FROM_H BX0 W HH AM K0 ENT FRM FRS Hh2 wappW spc (sp - 96) sp OC OWN 3 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Definition vals (j : nat) : Z :=
  match j with 2%nat => spc | 3%nat => pa_gp AD | 4%nat => hl_tp L | 8%nat => sp | 9%nat => spc | 18%nat => F / 8 + 2147450880 | 19%nat => F | 20%nat => ND | 21%nat => o
             | 24%nat => F | 25%nat => 2147450880 | 26%nat => F + 32 | 27%nat => bvu (getr R (reg 27)) | _ => 0 end.
Definition IXP : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat.
Local Notation REGSP := (regl IXP vals).

(* [comment removed for export] *)
Ltac pf BIx :=
  destruct ((GF PQAKR3.g_pfacts) _ _ _ _ _ _ BIx) as ((PF1 & PF2 & PF3 & PF4 & _) & (FD & FW & FSW & FLU & FLW) & (PL1 & PL2 & PL3 & PL4) & (SW & OWNV & PS1 & PS2 & PS3 & PS4) & (CSB & CUAR & IMGC) & (AVSH & AVF & AVS));
  change (ff_bytes 3) with 512 in *; change (512 / 8) with 64 in *.

(* [comment removed for export] *)
Lemma KSKEEP LB1 FFx spx scr (M1 M3 : mem) y :
  (forall f, In f FFx -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) -> (forall b, In b LB1 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  L5SAR.ek L ar LB1 FFx spx scr [] M1 M3 -> incl (PM.vs_own y) LB1 -> PMSPA.aobjA FFx o 24 -> kstr_at M1 o y -> kstr_at M3 o y.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_241 ())). Qed.

(* [comment removed for export] *)
Lemma GEK BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) (Wp : Z -> Prop) :
  GM BX1 M1 model1 LK1 Aw1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (sp - PMSPA.pm_scr PQASA.FROM_H <= a < sp) \/ (F <= a < F + 512) \/ (F / 8 + SB <= a < F / 8 + SB + 64)) ->
  L5SAR.ek L ar (BX1 ++ LBX) FF sp (PMSPA.pm_scr PQASA.FROM_H) [] M1 M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_242 ())). Qed.

(* [comment removed for export] *)
Lemma KSX BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) (Wp : Z -> Prop) y :
  GM BX1 M1 model1 LK1 Aw1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (sp - PMSPA.pm_scr PQASA.FROM_H <= a < sp) \/ (F <= a < F + 512) \/ (F / 8 + SB <= a < F / 8 + SB + 64)) ->
  incl (PM.vs_own y) BX1 -> kstr_at M1 o y -> kstr_at M3 o y.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_243 ())). Qed.

(* [comment removed for export] *)
Lemma KCKEEP LB1 FFx spx scr (M1 M3 : mem) y cs :
  (forall f, In f FFx -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) -> (forall b, In b LB1 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  L5SAR.ek L ar LB1 FFx spx scr [] M1 M3 -> incl (PM.vs_own y) LB1 -> PMSPA.aobjA FFx o 24 -> kstr_at M1 o y -> kcontent M1 o y cs -> kcontent M3 o y cs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_244 ())). Qed.
Lemma KCX BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) (Wp : Z -> Prop) y cs :
  GM BX1 M1 model1 LK1 Aw1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (sp - PMSPA.pm_scr PQASA.FROM_H <= a < sp) \/ (F <= a < F + 512) \/ (F / 8 + SB <= a < F / 8 + SB + 64)) ->
  incl (PM.vs_own y) BX1 -> kstr_at M1 o y -> kcontent M1 o y cs -> kcontent M3 o y cs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_245 ())). Qed.

(* [comment removed for export] *)
Definition DGF (Mx : mem) : Prop := forall i, 0 <= i < ND -> exists dg, 0 <= dg <= 9 /\ L5.u8_at RSEGS Mx (F + 32 + i) (48 + dg).
Lemma DG_agree (Ma Mb : mem) : 7036928 <= F <= 140737488354816 ->
  (forall i, 0 <= i < 24 -> Mb (Z_to_bv 64 (F + 32 + i)) = Ma (Z_to_bv 64 (F + 32 + i))) -> DGF Ma -> DGF Mb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_246 ())). Qed.

(* [comment removed for export] *)
Lemma OAP : (o + 24 <= F \/ F + 512 <= o) /\ (o / 8 + SB + 3 <= F / 8 + SB \/ F / 8 + SB + 64 <= o / 8 + SB) /\ (o + 24 <= fl \/ fl + 1 <= o).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_247 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma FIN M6 model6 LK6 Aw6 cr6 (y : PM.vstr) (gy : Z) (fx6 : FPState) R6 (ds : list Z) :
  GM (PM.vs_own y) M6 model6 LK6 Aw6 cr6 -> kstr_at M6 o y -> kcontent M6 o y (bs ++ ds) -> NEM.ascii ds -> PQMA.ks_ok SM y gy -> PM.vs_size y = PM.vs_size x + ND ->
  PMSP.credit_keep cr cr6 (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) ->
  REGSP R6 -> getr R6 (reg 22) = Z_to_bv 64 (F + 32) -> getr R6 (reg 23) = Z_to_bv 64 (F + 32) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 RA_PB M6 model6) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_248 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma PBCALL My modely LKy Awy cry (y : PM.vstr) (gy : Z) (fx5 : FPState) R5 (c jj : Z) (bsy : list Z) :
  GM (PM.vs_own y) My modely LKy Awy cry -> kstr_at My o y -> kcontent My o y bsy -> PQMA.ks_ok SM y gy -> PM.vs_size y < SM ->
  PMSP.credit_le (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) cry ->
  REGSP R5 -> getr R5 (reg 1) = Z_to_bv 64 RA_PB -> getr R5 (reg 10) = Z_to_bv 64 o -> getr R5 (reg 11) = Z_to_bv 64 c -> 0 <= c < 256 ->
  getr R5 (reg 22) = Z_to_bv 64 jj -> getr R5 (reg 23) = Z_to_bv 64 jj ->
  L5KA.zeros_at My (F / 8 + 2147450880 + 4) 3 ->
  (forall (fx6 : FPState) R6 M6 model6 LK6 Aw6 (y' : PM.vstr) (gy' : Z) cr6,
      GM (PM.vs_own y') M6 model6 LK6 Aw6 cr6 -> kstr_at M6 o y' -> kcontent M6 o y' (bsy ++ [c]) -> PQMA.ks_ok SM y' gy' -> PM.vs_size y' = PM.vs_size y + 1 ->
      PMSP.credit_keep cry cr6 (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y' gy')) ->
      REGSP R6 -> getr R6 (reg 22) = Z_to_bv 64 jj -> getr R6 (reg 23) = Z_to_bv 64 jj -> L5KA.zeros_at M6 (F / 8 + 2147450880 + 4) 3 ->
      (forall i, 0 <= i < 24 -> M6 (Z_to_bv 64 (F + 32 + i)) = My (Z_to_bv 64 (F + 32 + i))) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 RA_PB M6 model6) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 PBPC My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_249 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma PBODY My modely LKy Awy cry (y : PM.vstr) (gy : Z) (fx5 : FPState) R5 (j : Z) (bsy : list Z) :
  GM (PM.vs_own y) My modely LKy Awy cry -> kstr_at My o y -> kcontent My o y bsy -> DGF My -> PQMA.ks_ok SM y gy -> PM.vs_size y < SM ->
  PMSP.credit_le (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) cry ->
  REGSP R5 -> getr R5 (reg 22) = Z_to_bv 64 (F + 32 + j) -> getr R5 (reg 23) = Z_to_bv 64 (F + 32 + j) ->
  L5KA.zeros_at My (F / 8 + 2147450880 + 4) 3 -> 0 <= j <= 19 -> j < ND ->
  (forall (fx6 : FPState) R6 M6 model6 LK6 Aw6 (y' : PM.vstr) (gy' : Z) cr6 (c : Z),
      GM (PM.vs_own y') M6 model6 LK6 Aw6 cr6 -> kstr_at M6 o y' -> kcontent M6 o y' (bsy ++ [c]) -> 48 <= c <= 57 -> DGF M6 -> PQMA.ks_ok SM y' gy' -> PM.vs_size y' = PM.vs_size y + 1 ->
      PMSP.credit_keep cry cr6 (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y' gy')) ->
      REGSP R6 -> getr R6 (reg 22) = Z_to_bv 64 (F + 32 + j) -> getr R6 (reg 23) = Z_to_bv 64 (F + 32 + j) -> L5KA.zeros_at M6 (F / 8 + 2147450880 + 4) 3 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 RA_PB M6 model6) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 QB My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_250 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma PUSH (jn : nat) : forall My modely LKy Awy cry (y : PM.vstr) (gy : Z) (fx5 : FPState) R5 (ds : list Z),
  GM (PM.vs_own y) My modely LKy Awy cry -> kstr_at My o y -> kcontent My o y (bs ++ ds) -> NEM.ascii ds -> DGF My ->
  PQMA.ks_ok SM y gy -> PM.vs_size y + 1 + Z.of_nat jn = PM.vs_size x + ND -> PM.vs_size x <= PM.vs_size y ->
  PMSP.credit_keep cr cry (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y gy)) ->
  REGSP R5 -> getr R5 (reg 22) = Z_to_bv 64 (F + 32 + Z.of_nat jn) -> getr R5 (reg 23) = Z_to_bv 64 (F + 32 + Z.of_nat jn) ->
  L5KA.zeros_at My (F / 8 + 2147450880 + 4) 3 -> Z.of_nat jn <= 19 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 QB My modely) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_251 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma DLOOP (f : nat) : forall (fx : FPState) (Rd : bvmap 5 word) (Mv : mem) (k xx : Z),
  getr Rd (reg 2) = Z_to_bv 64 spc -> getr Rd (reg 10) = Z_to_bv 64 (- k) -> getr Rd (reg 11) = Z_to_bv 64 10 -> getr Rd (reg 12) = Z_to_bv 64 M10 ->
  getr Rd (reg 13) = Z_to_bv 64 254 -> getr Rd (reg 20) = Z_to_bv 64 k -> getr Rd (reg 23) = Z_to_bv 64 xx -> getr Rd (reg 24) = Z_to_bv 64 F ->
  getr Rd (reg 26) = Z_to_bv 64 (F + 32) ->
  7036928 <= F <= 140737488354816 -> F mod 32 = 0 -> (2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784) ->
  L5.writable RSEGS Mv (F + 32) 24 ->
  0 <= xx < 2 ^ 64 -> 0 <= k -> Z.of_nat f = 20 - k -> k + PQVA.ndig_f f xx <= 20 ->
  exists (fx' : FPState) R' Mv', msteps RSEGS (st fx Rd LOOP Mv) (st fx' R' QB Mv') /\ mem_grows Mv Mv'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 + k <= a < F + 32 + (k + PQVA.ndig_f f xx)) -> Mv' (Z_to_bv 64 a) = Mv (Z_to_bv 64 a))
    /\ getr R' (reg 20) = Z_to_bv 64 (k + PQVA.ndig_f f xx)
    /\ getr R' (reg 22) = Z_to_bv 64 (F + 32 + (k + PQVA.ndig_f f xx - 1)) /\ getr R' (reg 23) = Z_to_bv 64 (F + 32 + (k + PQVA.ndig_f f xx - 1))
    /\ (forall i, In i KD -> getr R' (reg i) = getr Rd (reg i))
    /\ (forall i, k <= i < k + PQVA.ndig_f f xx -> exists dg, 0 <= dg <= 9 /\ L5.u8_at RSEGS Mv' (F + 32 + i) (48 + dg)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_252 ())). Qed.

(* [comment removed for export] *)
Definition WPD (a : Z) : Prop :=
  (V2 - 104 <= a < V2 - 104 + 8) \/ (F + 0 <= a < F + 0 + 24) \/ (F / 8 + 2147450880 + 0 <= a < F / 8 + 2147450880 + 0 + 52) \/ (F + 32 <= a < F + 32 + 24).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma DIGITS (fx2 : FPState) (R2 : bvmap 5 word) :
  GM BX0 M2 model2 LK2 Aw cr -> L5SAR.ek L ar (BX0 ++ LBX) FF sp (PMSPA.pm_scr PQASA.FROM_H) [] M M2 ->
  getr R2 (reg 2) = Z_to_bv 64 spc -> getr R2 (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R2 (reg 8) = Z_to_bv 64 sp ->
  getr R2 (reg 9) = Z_to_bv 64 spc -> getr R2 (reg 10) = Z_to_bv 64 F -> getr R2 (reg 21) = Z_to_bv 64 o -> getr R2 (reg 23) = Z_to_bv 64 v ->
  getr R2 (reg 25) = Z_to_bv 64 2147450880 -> getr R2 (reg 27) = getr R (reg 27) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 RA_SM M2 model2) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_253 ())). Qed.
End Frame.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zl HV HS HC := clear - HV HS HC; Lia.lia.
Ltac enter_tac Aconc fxv MVv HRgp HRtp HV HS HC :=
  pose proof (LF2CBN( Aconc fxv R MVv (fun j : nat => match j with 2%nat => V2 | 33%nat => o | 34%nat => v | _ => 0 end) )) as P;
  L5SAR.feed P ltac:(fd);
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T21 & T23 & T25 & C26 & C25 & C24 & C23 & C22 & C21 & C20 & C19 & C18 & C9 & C8 & C1 & C0);
  apply ((GX PQAKR3.g_enter) spc (sp - 96) sp OC OWN 3 fxv fx1 R1 757600 757712 M1v);
  [ right; right; right; left; reflexivity | zl HV HS HC | exact (proj2 HSPCf) | zl HV HS HC | zl HV HS HC | zl HV HS HC | intros a Ha; unfold ocell12 in Ha; clear - HV HS HC Ha; Lia.lia
  | intros Ma Mb OW AG; apply (own12_agree sp R Ma Mb ltac:(zl HV HS HC) ltac:(zl HV HS HC) OW AG)
  | exact MS1 | exact MG1 | intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; clear - HV HS HC X; Lia.lia]
  | intros M1 VIS1 AV; unfold own12;
    repeat match goal with |- _ /\ _ => split end;
    (match goal with |- L5.u64_at _ _ ?a0 ?v0 => apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a0 v0 (AV a0 8 ltac:(zl HV HS HC) ltac:(zl HV HS HC)) ltac:(zl HV HS HC) ltac:(zl HV HS HC))) end; rewrite VIS1;
     match goal with |- L5.u64_at _ _ ?a _ => first [ replace a with (V2 + 8) by (zl HV HS HC); assumption
        | replace a with V2 by (zl HV HS HC); assumption
        | replace a with (V2 - 8) by (zl HV HS HC); assumption
        | replace a with (V2 - 16) by (zl HV HS HC); assumption
        | replace a with (V2 - 24) by (zl HV HS HC); assumption
        | replace a with (V2 - 32) by (zl HV HS HC); assumption
        | replace a with (V2 - 40) by (zl HV HS HC); assumption
        | replace a with (V2 - 48) by (zl HV HS HC); assumption
        | replace a with (V2 - 56) by (zl HV HS HC); assumption
        | replace a with (V2 - 64) by (zl HV HS HC); assumption
        | replace a with (V2 - 72) by (zl HV HS HC); assumption
        | replace a with (V2 - 80) by (zl HV HS HC); assumption
        | replace a with (V2 - 88) by (zl HV HS HC); assumption
        | replace a with (V2 - 96) by (zl HV HS HC); assumption ] end)
  | exact T2 | apply KS1; inl | exact T1 | reflexivity | zl HV HS HC |];
  intros R2 M2 model2 F fl LK2 G APART LM2 EK2 G10 RP2 _;
  apply (DIGITS F fl LK2 M2 model2 G APART fx1 R2 LM2 EK2);
  [ rewrite (L5SAR.cs_of_preserved _ _ 2%nat RP2 ltac:(inl)); exact T2
  | rewrite (L5SAR.cs_of_preserved _ _ 3%nat RP2 ltac:(inl)); rewrite (KS1 3%nat) by inl; exact HRgp
  | rewrite (L5SAR.cs_of_preserved _ _ 4%nat RP2 ltac:(inl)); rewrite (KS1 4%nat) by inl; exact HRtp
  | rewrite (L5SAR.cs_of_preserved _ _ 8%nat RP2 ltac:(inl)); rewrite T8; f_equal; zl HV HS HC
  | rewrite (L5SAR.cs_of_preserved _ _ 9%nat RP2 ltac:(inl)); exact T9
  | exact G10
  | rewrite (L5SAR.cs_of_preserved _ _ 21%nat RP2 ltac:(inl)); exact T21
  | rewrite (L5SAR.cs_of_preserved _ _ 23%nat RP2 ltac:(inl)); exact T23
  | rewrite (L5SAR.cs_of_preserved _ _ 25%nat RP2 ltac:(inl)); exact T25
  | rewrite (L5SAR.cs_of_preserved _ _ 27%nat RP2 ltac:(inl)); apply KS1; inl ].

Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R N0 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_254 ())). Qed.
End Run.

(* [comment removed for export] *)
Theorem fromu_ok : PQASCA2.fromu_specCA RSEGS AD L ar HI 0xb8fb0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdFuC ()) ["WithHeap"] (Mh_0270_blobs1.kr_b_255 ())). Qed.

End WithHeap.
End PQAAFUC.

End PnAAdFuC.
Module PnAAdI64.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdStrCK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObjA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAdStrCK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKSlotA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKCallA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKStepA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKFromA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKEncNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemFrameA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdI64P1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdI64P2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdI64P3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdI64P4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdI64P5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdI64P6 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016.Na0_code_rb22d0_b22d4.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdI64 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_02136PnVisA4PQVA6ndig_fC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z6ltb_geC69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF3:ndig_f_rngC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z7pow_1_rK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI69ndig_f_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA4ndigC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z6leb_gtK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI67ndig_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5w_u64C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF39ndig_f_ltC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_symK46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib7Numbers7BinNums1N01C69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF38ndig_rngC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specC69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_strC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3absC56Stdlib6ZArith6BinInt1Z6abs_eqC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z7abs_neqC69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA6ncharsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA4svalC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5w_i64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib7Numbers7BinNums1Z03c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI6:w_u64_ndigC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG37bvu_rngC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7enc_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA4PMEAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8pot_encAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA;epot_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;pot_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7pot_aeAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI69pot_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8sink_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ec_stateAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092;PnQStaticsA5PQSTA7err_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_KBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5VIS_HC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib6ZArith4Zdiv:Z_mod_multI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38obj_pf_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI64OWNEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5own13C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI63OCEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7ocell13C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;own13_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI68sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI65V2_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI6:nchars_rngC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8abs_specC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List6filterC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_tC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5lv_eoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl01C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List:filter_appC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3advC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ndestC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List9incl_applC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5a_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5xinvGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI63ESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6kbsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_oaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7alvl_okC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI64valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P58PQAAI6P57alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6set_lvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI69ndest_advC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprK46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5s_xlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI63FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6s_advXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P58PQAAI6P5=qviAk2e0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P58PQAAI6P5=qviAk2e1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P58PQAAI6P5=qviAk1e1_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI63IXAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI64QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI65HSPCfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3LSZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P58PQAAI6P5;KS_qviAk2e0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P58PQAAI6P5;KS_qviAk2e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P58PQAAI6P5;KS_qviAk1e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_WAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4EVISC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5wappWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P68PQAAI6P67alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P68PQAAI6P6:qviD2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI6:mem_eq_frzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA<v_int64_specC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI6:w_i64_ndigC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8aargs_ofC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ea_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4svalC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pre_i64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8step_i64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P1:qviJ1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG38regl_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI63ADVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_pfactsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7s_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ENC_SLOTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3Hh3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI62IXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ENC_HC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI67oec_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI68ov_rng56C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P68PQAAI6P68KS_qviD2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9eargs_i64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8TAG_NONEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P18KS_qviJ1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P1:qviJ2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI67DU_DPHIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P18PQAAI6P18KS_qviJ2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI64EST0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P39qviC_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N8pb_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N6pb_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_restC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_setC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_app_asciiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_xcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N9s_call_sCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P37KS_qviCC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multK46Stdlib9micromega=RingMicromega3Op206C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5asciiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N9s_key_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7src_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ins_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7ins_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA8src_okCAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI67AFTER_VC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI67AFTER_KC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5INS_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8AOFF_KEYC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbc69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI64INS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_kcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P37alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG>u64_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI65COMMAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI65KDESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P3;qviDKz_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P3;qviDKn_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P3;qviDV2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P3<qviDV1z_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P3<qviDV1n_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P39KS_qviDKzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P39KS_qviDKnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P39KS_qviDV2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P3:KS_qviDV1zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202:PnAAdI64P38PQAAI6P3:KS_qviDV1nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lv_shapeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_kbgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8lv_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N:lv_last_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI66KEYLITC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI66PATH_DC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lv_rootC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5aeownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8args_i64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5d_i64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA7pre_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6cls_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;evis_of_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA4svalC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA4ndigC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6edepthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdI646PQAAI63RUNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ:qa_v_int64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA<v_int64_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8step_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3phiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAAI6.
Import L5A L5SAR PQAKS3N PQAKC3N PQAKT3N PQAKG3 PQAKENA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
(* [comment removed for export] *)
Ltac flia := solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ].
Ltac fd := first [assumption | flia].
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AQ := PnLayoutQA.QADDR_A.
Abbreviation AE := NemLayoutA.NEADDR_A.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation adaptor_at := (PQMA.adaptor_at RSEGS AD accA annA (qa_vp_adaptor AQ)).
Abbreviation kcontent := (NEM.kcontent RSEGS).
Abbreviation bvu x := (bv_unsigned x).

(* [comment removed for export] *)
Lemma ndig_f_lb f : forall v k, 10 ^ k <= v -> k <= Z.of_nat f -> 0 <= k -> k + 1 <= PQVA.ndig_f f v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) [] (Mh_0270_blobs1.kr_b_256 ())). Qed.
Lemma ndig_lb v k : 0 <= k <= 19 -> 10 ^ k <= v -> k + 1 <= PQVA.ndig v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) [] (Mh_0270_blobs1.kr_b_257 ())). Qed.
Lemma w_u64_ndig v : 0 <= v -> NEM.w_u64 v <= PQVA.ndig v + 2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) [] (Mh_0270_blobs1.kr_b_258 ())). Qed.
Lemma ndig_u32 v : 0 <= v < 2 ^ 32 -> PQVA.ndig v <= 10.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) [] (Mh_0270_blobs1.kr_b_259 ())). Qed.
Lemma hdr_str_ndig v : 0 <= v < 2 ^ 64 -> NEM.hdr_str (PQVA.ndig v) = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) [] (Mh_0270_blobs1.kr_b_260 ())). Qed.
(* [comment removed for export] *)
Lemma nchars_rng v : 0 <= v < 2 ^ 64 -> 1 <= PQASA.nchars v <= PQVA.ndig (Z.abs (PQVA.sval v)) + 1 /\ 1 <= PQVA.ndig (Z.abs (PQVA.sval v)) <= 20.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) [] (Mh_0270_blobs1.kr_b_261 ())). Qed.
Lemma w_i64_ndig v : 0 <= v < 2 ^ 64 -> NEM.w_i64 (PQVA.sval v) <= PQVA.ndig (Z.abs (PQVA.sval v)) + 3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) [] (Mh_0270_blobs1.kr_b_262 ())). Qed.

(* [comment removed for export] *)
Lemma aacc_join (Mx : mem) p n m : aacc Mx p n -> aacc Mx (p + n) m -> 0 <= n -> aacc Mx p (n + m).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) [] (Mh_0270_blobs1.kr_b_263 ())). Qed.
Lemma aacc_sub (Mx : mem) a0 n0 a1 n1 : aacc Mx a0 n0 -> a0 <= a1 -> a1 + n1 <= a0 + n0 -> aacc Mx a1 n1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) [] (Mh_0270_blobs1.kr_b_264 ())). Qed.

(* [comment removed for export] *)
Lemma mem_eq_frz (Ma Mb : mem) : (forall a, 0 <= a < 2 ^ 64 -> ~ False -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> Mb = Ma.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) [] (Mh_0270_blobs1.kr_b_265 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
(* [comment removed for export] *)
Hypothesis PB : PQASCA.pb_specCA RSEGS AD L ar HI 0xf4640.
Hypothesis FROMK : PQASCA2.fromi_specCA RSEGS AD L ar HI 0xba148.
Hypothesis INSI : PQASCA.ins_specCA RSEGS AD L ar HI 0xb95f0.
Hypothesis VIE : NECSA.v_int64_spec RSEGS AD AQ AAD AE L ar HI (NESKA.PMEA L).
Hypothesis VKE : NECSA.v_key_spec RSEGS AD AQ AAD AE L ar HI (NESKA.PMEA L).

(* [comment removed for export] *)
Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (V2 cls r oa ov osk oec cat bv tg : Z) (sa : PQMA.ast) (kbb : list Z) (en : NEM.enc) (k : NESK.sink) (bf ef : bool).
Local Notation sp := (V2 + cls).
Local Notation spc := (V2 - 160).
Local Notation EPOT := (NECSA.pot_encA L ar (NESKA.PMEA L)).
(* [comment removed for export] *)
Local Notation ESO := (NECS.eown en k).
Local Notation QE := (NECSA.pot_encA L ar (NESKA.PMEA L) en k).
Local Notation ST0 := (NEMA.AEST sa kbb en k).
Local Notation ND := (PQASA.nchars bv).
(* [comment removed for export] *)
Local Notation DU := (PQVA.ndig (Z.abs (PQVA.sval bv)) + 3).
Local Notation DPHI := (PQVA.ndig (Z.abs (PQVA.sval bv)) + 3).
Hypothesis Hcls : cls = 0 \/ cls = 16.
Hypothesis V32 : V2 mod 32 = 0.
Hypothesis HH : ri_inv HI ((PQMA.aown sa ++ ESO) ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r PNVA.VIS_H.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM PNVA.VIS_H FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 oa.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 bv.
Hypothesis Hbv : 0 <= bv < 2 ^ 64.
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 tg.
Hypothesis Htg : tg = NEM.TAG_NONE.
Hypothesis A14 : getr R (reg 14) = Z_to_bv 64 oec.
Hypothesis AO : PMSPA.aobjA FF oa PQMA.ASIZE.
Hypothesis O8 : oa mod 8 = 0.
Hypothesis AOV : PMSPA.aobjA FF ov 56.
Hypothesis OV8 : ov mod 8 = 0.
Hypothesis AOSK : PMSPA.aobjA FF osk 24.
Hypothesis OK8 : osk mod 8 = 0.
Hypothesis AOEC : PMSPA.aobjA FF oec 16.
Hypothesis OE8 : oec mod 8 = 0.
Hypothesis APT : oa + PQMA.ASIZE <= ov \/ ov + 56 <= oa.
Hypothesis APT2 : oa + PQMA.ASIZE <= osk \/ osk + 24 <= oa.
Hypothesis APT3 : oa + PQMA.ASIZE <= oec \/ oec + 16 <= oa.
Hypothesis APT4 : ov + 56 <= osk \/ osk + 24 <= ov.
Hypothesis APT5 : oec + 16 <= ov \/ ov + 56 <= oec.
Hypothesis APT6 : oec + 16 <= osk \/ osk + 24 <= oec.
Hypothesis AA : adaptor_at M oa ov sa.
Hypothesis OACC : accA M oa PQMA.ASIZE.
Hypothesis AOK : PQMA.adaptor_ok sa.
Hypothesis VIS : EVIS M ov.
Hypothesis BASE : PMSTA.base_okA RSEGS AD M.
(* [comment removed for export] *)
Hypothesis KC : kcontent M (oa + PQMA.AOFF_KB) (PQMA.a_kb sa) kbb.
Hypothesis U8 : utf8_valid kbb = true.
Hypothesis EDEP : NEM.en_depth en = NEMA.ndest (PQMA.a_lv sa).
Hypothesis ENA : NEMA.enc_atA RSEGS AE L ar M ov osk en.
Hypothesis SKA : NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) M osk k.
Hypothesis ECS : NEMA.ec_stateA RSEGS AD M oec bf cat.
Hypothesis ERR : PQSTA.err_okA RSEGS AD AAD AQ M ef.
Hypothesis PRE : PQMA.kbsize sa + DU <= PQMA.SMB /\ NESK.sk_z k + DPHI <= NESK.SMZ.
Hypothesis CRF : PMSP.credit_le (NEMA.pot_aeA L ar ST0) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (st' : NEMA.aest) (b' e' : bool) (cr' : credit),
      regs_preserved R R' ->
      NEMA.ae_atA RSEGS AD AE L ar (qa_vp_adaptor AQ) M' oa ov osk st' -> NEMA.ae_ok st' -> NEMA.ec_stateA RSEGS AD M' oec b' cat -> PMSTA.base_okA RSEGS AD M' -> PQSTA.err_okA RSEGS AD AAD AQ M' e' ->
      (bf = true -> b' = true) -> (ef = true -> e' = true) ->
      (NEMA.nlv st' = NEMA.nlv ST0 /\ NEMA.kbsize st' <= NEMA.kbsize ST0 + DU /\ NEMA.phi st' <= NEMA.phi ST0 + DPHI /\ NEMA.esize st' = NEMA.esize ST0
       /\ NEMA.edepth st' = NEMA.edepth ST0 /\ (b' = bf \/ False)) ->
      L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr PNVA.VIS_H) (NEMA.ae_WA AD oa ov osk oec) M M' ->
      PMSP.credit_keep cr cr' (NEMA.pot_aeA L ar ST0) (NEMA.pot_aeA L ar st') ->
      model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (NEMA.aeown st' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition OWNE (Mx : mem) : Prop := own13 sp R Mx /\ L5.u64_at RSEGS Mx (V2 - 136) oec.
Definition OCE (a : Z) : Prop := ocell13 sp a \/ (V2 - 136 <= a < V2 - 128).
Local Notation OWN := OWNE.
Local Notation OC := OCE.
(* [comment removed for export] *)
Lemma QENN : 0 <= fst QE /\ 0 <= snd QE.
Proof using LY ENA SKA.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_266 ())). Qed.
Local Notation "'SX' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Lemma pot_split x kb1 e1 k1 : NEMA.pot_aeA L ar (NEMA.AEST x kb1 e1 k1) = PM.credit_add (PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) x)) (EPOT e1 k1).
Proof using L ar.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_267 ())). Qed.
Lemma CR : PMSP.credit_le (PM.credit_add (PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) sa)) QE) cr.
Proof using CRF.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_268 ())). Qed.
Lemma xinv0 : PQAKENA.xinvG L ar oa ov osk oec cat M (PQMA.a_kb sa) kbb en k bf ef.
Proof using KC U8 ENA SKA ECS ERR.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_269 ())). Qed.

Lemma sp_facts : 140735332487264 + 16 <= V2 /\ V2 + cls <= 140737488355328 /\ (V2 + cls) mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof using ENT Hcls.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_270 ())). Qed.
Lemma V2_lo : 140735332487328 <= V2.
Proof using ENT Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_271 ())). Qed.
Lemma HSPCf : sp - 2048 <= spc /\ spc mod 16 = 0.
Proof using Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_272 ())). Qed.
Lemma oec_rng : 7036928 <= oec /\ oec + 16 <= 2 ^ 47.
Proof using LY HIok HH AOEC.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_273 ())). Qed.
Lemma oa_lo96 : 7036928 <= oa /\ oa + 96 <= 2 ^ 47.
Proof using LY HIok HH AO.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_274 ())). Qed.
Lemma ov_rng56 : 7036928 <= ov /\ ov + 56 <= ahl_ceil ar /\ ov + 56 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784).
Proof using LY HIok HH AOV.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_275 ())). Qed.
Lemma tg_rng : 0 <= tg < 2 ^ 64.
Proof using Htg.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_276 ())). Qed.
Lemma GOWNE : forall Ma Mb, OWN Ma -> (forall a, OC a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> OWN Mb.
Proof using ENT Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_277 ())). Qed.

(* [comment removed for export] *)
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK Aw sp (PMSPA.pm_scr PNVA.VIS_H) spc (V2 - 136) sp OC OWN F fl 0 LK2 M2 model2 cr (PQMA.aown sa ++ ESO).
Hypothesis APART : forall a n0 sp0 scr0, (forall i, 0 <= i < n0 -> aclient L ar ((PQMA.aown sa ++ ESO) ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n0 ->
         (a + n0 <= F \/ F + ff_bytes 0 <= a) /\ (a + n0 <= F / 8 + SB \/ F / 8 + SB + ff_bytes 0 / 8 <= a) /\ (a + n0 <= fl \/ fl + 1 <= a).
Local Notation FF' := ((F, 0, spc + 32) :: FF).
Local Notation AMF := (PQAKS3N.a_mem L ar HI M model LBX FF LK Aw cr sp oa ov osk oec sa QE spc OWN 0 F).
Local Notation xinv := (PQAKENA.xinvG L ar oa ov osk oec cat).
Local Notation "'SF' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE spc (V2 - 136) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).
Local Notation "'SE' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE cat OV8 OK8 OE8 APT2 APT3 APT4 APT5 APT6 spc (V2 - 136) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).
Local Notation "'SY' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE cat APT2 APT3 spc (V2 - 136) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).
Local Notation "'GF' f" := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r PNVA.VIS_H (PQMA.aown sa ++ ESO) (NEMA.ae_WA AD oa ov osk oec) HH AM K0 ENT FRM FRS PQAKS3N.Hh3 (SX PQAKS3N.wappW) spc (V2 - 136) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Definition vals (j : nat) : Z :=
  match j with 2%nat => spc | 3%nat => pa_gp AD | 4%nat => hl_tp L | 8%nat => sp | 18%nat => F | 19%nat => oa + 80 | 20%nat => oa | 22%nat => (oa + 80) / 8 + 2147450880 | 23%nat => tg | 24%nat => bv
             | 25%nat => F | 26%nat => 2147450880 | 27%nat => F / 8 + 2147450880 | 9%nat => spc | _ => 0 end.
Definition IXA : list nat := [2; 3; 4; 8; 18; 19; 22; 23; 25; 26; 27]%nat.
Definition IX : list nat := (9 :: 20 :: 24 :: IXA)%nat.
Local Notation REGSA := (regl IXA vals).
Local Notation REGS := (regl IX vals).

(* [comment removed for export] *)
Ltac pf LM :=
  let BIx := fresh "BIx" in pose proof (proj1 LM) as BIx;
  destruct ((GF PQAKR3.g_pfacts) _ _ _ _ _ _ BIx) as ((PF1 & PF2 & PF3 & PF4 & _) & (FD & FW & FSW & FLU & FLW) & (PL1 & PL2 & PL3 & PL4) & (SW & OWNV & PS1 & PS2 & PS3 & PS4) & (CSB & CUAR & _) & (AVSH & AVF & AVS));
  change (ff_bytes 0) with 64 in *; change (64 / 8) with 8 in *.

(* [comment removed for export] *)
Definition EST (en1 : NEM.enc) (k1 : NESK.sink) (b1 e1 : bool) : Prop :=
  NEM.en_n en1 = NEM.en_n en /\ NEM.en_depth en1 = NEM.en_depth en /\ NESK.sk_z k <= NESK.sk_z k1
  /\ (bf = true -> b1 = true) /\ (ef = true -> e1 = true) /\ (b1 = bf \/ False).
Lemma EST0 : EST en k bf ef.
Proof using Hbv.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_278 ())). Qed.
Lemma DU_DPHI : DU <= DPHI /\ ND + 1 <= DPHI /\ ND + 2 <= DU.
Proof using Hbv.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_279 ())). Qed.
(* [comment removed for export] *)
Lemma ndest_adv lv0 c : NEMA.ndest (lv0 ++ [PQAKS3N.adv c]) = NEMA.ndest (lv0 ++ [c]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_280 ())). Qed.

(* [comment removed for export] *)
Lemma FIN M5 model5 LK5 Aw5 st5 cr5 kbb5 en5 k5 (b5 e5 : bool) (fx5 : FPState) R5 :
  AMF M5 model5 LK5 Aw5 st5 (NECS.eown en5 k5) (EPOT en5 k5) cr5 -> REGSA R5 -> xinv M5 (PQMA.a_kb st5) kbb5 en5 k5 b5 e5 -> EST en5 k5 b5 e5 ->
  PQMA.nlv st5 = PQMA.nlv sa -> PQMA.kbsize st5 <= PQMA.kbsize sa + DU -> PQMA.kbsize st5 + NESK.sk_z k5 <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st5) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb213c M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_281 ())). Qed.


(* [comment removed for export] *)
Lemma ADV M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 en1 k1 (b1 e1 : bool) (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 (NECS.eown en1 k1) (EPOT en1 k1) cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en1 k1 b1 e1 -> EST en1 k1 b1 e1 ->
  PQMA.a_lv st1 = lv0 ++ [c] ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 <= PQMA.kbsize sa + DU -> PQMA.kbsize st1 + NESK.sk_z k1 <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st1) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb20c4 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_282 ())). Qed.


(* [comment removed for export] *)
Ltac of LM ELV :=
  destruct ((SF PQAKS3N.s_oa) _ _ _ _ _ _ _ _ LM) as ((OA1 & OA2 & OA3 & OA4 & OA5) & OAZ & O16 & (OV1 & OV2 & OV3 & OV4 & OVZ & OVW) & IMG & VTZ & (OAF & OVF & OASF & OVSF) & (OAV & OAW));
  destruct ((SF PQAKS3N.s_lv) _ _ _ _ _ _ _ _ _ _ LM ELV) as (E80 & (E1 & E2 & E8 & E4 & E5) & (Z24 & Z20 & Z16 & Z8) & (CT & CK & CEO) & (CD & CW & CVIS) & (EO1 & EF1 & EV1) & ((CTR & CKR & CER & CKE) & CT1) & INL & EHI).

(* [comment removed for export] *)
Lemma PATH_D M1 model1 LK1 Aw1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> PQMA.a_lv sa = lv0 ++ [c] -> PQMA.lv_t c = 0 -> PQMA.lv_eo c = 1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1c64 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_283 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AFTER_V M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1f94 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_284 ())). Qed.
(* [comment removed for export] *)
Lemma AFTER_K M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48) -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb20b8 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_285 ())). Qed.


(* [comment removed for export] *)
Lemma div2_2 n : (2 * n) / 2 = n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_286 ())). Qed.
(* [comment removed for export] *)
Lemma INS_CALL (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 (ra v11 v12 v13 v14 : Z) :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = false -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  ra = (if arm then 0xb1f94 else 0xb20b8) ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 v11 -> getr R1 (reg 12) = Z_to_bv 64 v12 ->
  getr R1 (reg 13) = Z_to_bv 64 v13 -> getr R1 (reg 14) = Z_to_bv 64 v14 ->
  v11 = PM.vs_data (oa + 48) (PQMA.a_kb st1) + PM.vs_size (PQMA.a_kb st1) -> v12 = PM.vs_data (oa + 24) (PQMA.a_key st1) ->
  v13 = v12 + v14 -> v14 = PM.vs_size (PQMA.a_key st1) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + v14 + (if arm then 0 else 1) <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb95f0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_287 ())). Qed.

Lemma INS2 (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = true -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + PM.vs_size (PQMA.a_key st1) + (if arm then 0 else 1) <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if arm then 0xb1dcc else 0xb1e24) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_288 ())). Qed.

(* [comment removed for export] *)
Lemma KDEST M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.lv_t c = 0 -> PQMA.lv_eo c = 0 ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 = PQMA.kbsize sa -> PM.vs_size (PQMA.a_key st1) <= ND ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1d38 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_289 ())). Qed.

(* [comment removed for export] *)
Lemma COMMA (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = true -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  getr R1 (reg 1) = Z_to_bv 64 (if arm then 0xb1dcc else 0xb1e24) -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 44 ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + 1 + PM.vs_size (PQMA.a_key st1) + (if arm then 0 else 1) <= PQMA.kbsize sa + DU -> 0 <= PM.vs_size (PQMA.a_key st1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xf4640 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_290 ())). Qed.

(* [comment removed for export] *)
Lemma DISP2 M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> (PQMA.lv_eo c = 0 \/ PQMA.lv_t c = 1) ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 = PQMA.kbsize sa -> 0 <= PM.vs_size (PQMA.a_key st1) <= ND ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1d38 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_291 ())). Qed.

(* [comment removed for export] *)
Lemma KEYLIT M1 model1 LK1 Aw1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> PQMA.a_lv sa = lv0 ++ [c] -> (PQMA.lv_eo c = 0 \/ PQMA.lv_t c = 1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1c64 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_292 ())). Qed.

(* [comment removed for export] *)
Lemma DISP1 M1 model1 LK1 Aw1 cr1 kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1c64 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_293 ())). Qed.

(* [comment removed for export] *)
Lemma SETUP Mx modelx LKx Awx (fx2 : FPState) R2 :
  AMF Mx modelx LKx Awx sa ESO QE cr -> xinv Mx (PQMA.a_kb sa) kbb en k bf ef ->
  getr R2 (reg 2) = Z_to_bv 64 spc -> getr R2 (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R2 (reg 8) = Z_to_bv 64 sp ->
  getr R2 (reg 9) = Z_to_bv 64 spc -> getr R2 (reg 10) = Z_to_bv 64 F -> getr R2 (reg 20) = Z_to_bv 64 oa -> getr R2 (reg 23) = Z_to_bv 64 tg -> getr R2 (reg 24) = Z_to_bv 64 bv ->
  getr R2 (reg 26) = Z_to_bv 64 2147450880 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0xb1bc4 Mx modelx) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_294 ())). Qed.

End Frame.

(* [comment removed for export] *)
Ltac enter_tac Aconc fxv MVv HRgp HRtp :=
  pose proof (LF2CBN( Aconc fxv R MVv (fun j : nat => match j with 2%nat => V2 | _ => 0 end) )) as P;
  L5SAR.feed P ltac:(fd);
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T20 & T21 & T23 & T24 & T26 & CEC & C27 & C26 & C25 & C24 & C23 & C22 & C21 & C20 & C19 & C18 & C9 & C8 & C1 & C0);
  apply ((SX PQAKS3N.s_enterX) spc (V2 - 136) sp OC OWN 0 fxv fx1 R1 0xb1af4 727924 M1v CR);
  [ left; reflexivity | flia | exact (proj2 HSPCf) | flia | flia | flia | intros a Ha; unfold OCE, ocell13 in Ha; destruct Ha as [Ha|Ha]; flia
  | exact GOWNE
  | exact MS1 | exact MG1 | intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; flia]
  | intros M1 VIS1 AV; unfold OWNE, own13; split;
    [ repeat match goal with |- _ /\ _ => split end;
      (match goal with |- L5.u64_at _ _ ?a0 ?v0 => apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a0 v0 (AV a0 8 ltac:(flia) ltac:(flia)) ltac:(flia) ltac:(flia))) end; rewrite VIS1;
       match goal with |- L5.u64_at _ _ ?a _ => first [ replace a with (V2 + 8) by flia; assumption
          | replace a with V2 by flia; assumption
          | replace a with (V2 - 8) by flia; assumption
          | replace a with (V2 - 16) by flia; assumption
          | replace a with (V2 - 24) by flia; assumption
          | replace a with (V2 - 32) by flia; assumption
          | replace a with (V2 - 40) by flia; assumption
          | replace a with (V2 - 48) by flia; assumption
          | replace a with (V2 - 56) by flia; assumption
          | replace a with (V2 - 64) by flia; assumption
          | replace a with (V2 - 72) by flia; assumption
          | replace a with (V2 - 80) by flia; assumption
          | replace a with (V2 - 88) by flia; assumption
          | replace a with (V2 - 96) by flia; assumption
          | replace a with (V2 - 104) by flia; assumption ] end)
    | apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 (V2 - 136) oec (AV (V2 - 136) 8 ltac:(flia) ltac:(flia)) ltac:(flia) ltac:(flia))); rewrite VIS1;
      rewrite A14 in CEC; rewrite (L5.unsigned_lit oec) in CEC by flia; exact CEC ]
  | exact T2 | apply KS1; inl | exact T1 | reflexivity | flia |];
  intros R2 M2 model2 F fl LK2 G APART LM2 EK2 G10 RP2 _;
  apply (SETUP F fl LK2 M2 model2 G APART M2 model2 LK2 Aw fx1 R2 LM2);
  [ apply (PQAKENA.xinv_ekF L ar C HI LY HIok oa ov osk oec cat (proj1 oa_lo96) _ FF sp (PMSPA.pm_scr PNVA.VIS_H) M M2 sa kbb en k bf ef
             (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) AO AOV AOSK AOEC AA
             ltac:(apply incl_appl; apply incl_appl; apply incl_refl) ltac:(apply incl_appl; apply incl_appr; unfold NECS.eown; apply incl_appl; apply incl_refl)
             ltac:(apply incl_appl; apply incl_appr; unfold NECS.eown; apply incl_appr; apply incl_refl) EK2 xinv0)
  | rewrite (L5SAR.cs_of_preserved _ _ 2%nat RP2 ltac:(inl)); exact T2
  | rewrite (L5SAR.cs_of_preserved _ _ 3%nat RP2 ltac:(inl)); rewrite (KS1 3%nat) by inl; exact HRgp
  | rewrite (L5SAR.cs_of_preserved _ _ 4%nat RP2 ltac:(inl)); rewrite (KS1 4%nat) by inl; exact HRtp
  | rewrite (L5SAR.cs_of_preserved _ _ 8%nat RP2 ltac:(inl)); rewrite T8; f_equal; flia
  | rewrite (L5SAR.cs_of_preserved _ _ 9%nat RP2 ltac:(inl)); exact T9
  | exact G10
  | rewrite (L5SAR.cs_of_preserved _ _ 20%nat RP2 ltac:(inl)); rewrite T20; exact A10
  | rewrite (L5SAR.cs_of_preserved _ _ 23%nat RP2 ltac:(inl)); rewrite T23; exact A12
  | rewrite (L5SAR.cs_of_preserved _ _ 24%nat RP2 ltac:(inl)); rewrite T24; exact A11
  | rewrite (L5SAR.cs_of_preserved _ _ 26%nat RP2 ltac:(inl)); exact T26 ].

Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb1b44 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_295 ())). Qed.

End Run.

(* [comment removed for export] *)
Theorem int64_ok : PNVA.v_int64_spec RSEGS AD AQ AAD AE L ar HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdI64 ()) ["WithHeap"] (Mh_0270_blobs1.kr_b_296 ())). Qed.

End WithHeap.
End PQAAI6.


End PnAAdI64.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014.
Module PnAAdInC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdStrCK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKSlotA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKStrA3c OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKStrA3d OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdInP1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdInP2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201.PnAAdIkP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014.Na0_code_rba0f4_ba0f8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014.Na0_code_rba0a8_ba0ac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014.Na0_code_rb99dc_b99e0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAdStrCK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKStrC3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdInC () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5INS_HC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR36obj_pfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2or00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_02137PnStepA4PMKA9wapp_consC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC7o_factsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01K46Stdlib9micromega6VarMap1t03K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z7add_0_rI47Corelib4Init5Logic5False00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib6ZArith4Zdiv:Z_mod_multC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7kstr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4GMAXC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ45own12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ47ocell12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ47g_stkshC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC5V2_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3Hh2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC5wappWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC5HSPCfC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS3:kstr_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4KCAPC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic9False_indC46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_ctxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_consC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=aclient_casesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_apart1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_pieceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6frb_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6brb_ofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3GEKC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_applc69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC6KSKEEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z;div_le_monoC59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA:accA_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C9rdn_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7src_okAC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC6KCKEEPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02566PmAUar6PMAUAR:aobjA_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_hiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<block_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAReset16PMARS1?own_not_aclientC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<client_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes?RelationClasses>eq_equivalenceC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrK46Stdlib9micromega=RingMicromega3Op206C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK=blk_obj_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8avis_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9u8_at_visC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z>testbit_even_0C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS37tb_longC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38word_visC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitK47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR3>g_callee_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_pfactsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAKStrC37PQAKZC39sc_specCAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC8src_pushC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR37g_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP28qiR_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR36g_footC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflc69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3KSXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3KCXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3cfgC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR37g_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC4SCPCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3IXAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC5RA_SCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC6RETIREC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3OAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213:PnAKStrA3c6PQAKZ36SC_SCRC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP26KS_qiRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP29qiC4_concC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_apprc69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC4SRCXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3SBXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG38regl_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC4CALLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC6RA_IPRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC2IXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC7x_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5SMMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdInP28PQAAINP27KS_qiC4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP:qkC2a_concC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_consC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC6C4CALLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3IXCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP8KS_qkC2aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0a8_ba0ac7W_b9f64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0a8_ba0ac7F_b9f64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0a8_ba0ac7D_b9f64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC6STKSH4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR39stk_w_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP:qkC2b_concC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ47g_footLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8aclientwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP9qkC3_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ4;g_piece_lowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP8KS_qkC2bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0f4_ba0f87W_b9fb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0f4_ba0f87F_b9fb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0f4_ba0f87D_b9fb0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP7KS_qkC3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA8src_okCAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS36cls_ofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdInC7PQAAINC3RUNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA:ins_specCAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.
(* [comment removed for export] *)
Local Ltac flia := L5FastLia.plia.
Local Ltac fd := first [assumption | flia].

Module PQAAINC.
Import L5A L5SAR PQAKG3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation accA := PMSPA.accA.
Abbreviation kstr_at := (PQMA.kstr_at RSEGS accA).
Abbreviation kcontent := (NEM.kcontent RSEGS).
Abbreviation bvu x := (bv_unsigned x).
Import PQAKZ4.

(* [comment removed for export] *)
Definition N0 : Z := 0xb95f0.
Definition RA_SM : Z := 0xb966c.
Definition CALLP : Z := 0xb9754.
Definition RA_IPR : Z := 0xb9760.
Definition RA_SC : Z := 0xb97b4.
Definition RETIRE : Z := 0xb981c.
Definition RET : Z := 0xb98e8.
Definition SCPC : Z := 0xb9a6c.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Hypothesis SC : PQAKZC3.sc_specCA L ar HI 0xb9a6c.

Lemma Hh2 : 1 <= PQASA.INS_H <= 16.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"] (Mh_0270_blobs1.kr_b_297 ())). Qed.

(* [comment removed for export] *)
Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (V2 cls r o q n SM g : Z) (x : PM.vstr) (kbs sbs : list Z).
Local Notation sp := (V2 + cls).
Local Notation spc := (V2 - 128).
Local Notation W := ([(o, 24)] : list L5.range).
Local Notation BX0 := (PM.vs_own x).
Hypothesis Hcls : cls = 0 \/ cls = 16.
Hypothesis V32 : V2 mod 32 = 0.
Hypothesis HH : ri_inv HI (BX0 ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r PQASA.INS_H.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM PQASA.INS_H FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 o.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 (PM.vs_data o x + PM.vs_size x).
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 q.
Hypothesis A13 : getr R (reg 13) = Z_to_bv 64 (q + n).
Hypothesis A14 : getr R (reg 14) = Z_to_bv 64 n.
Hypothesis Hn : 0 <= n.
Hypothesis HSM : PM.vs_size x + n <= SM.
Hypothesis SRC : PQASA.src_okA RSEGS L HI M LBX FF q n.
Hypothesis SQ : L5.bytes_at RSEGS M q sbs.
Hypothesis SLEN : Z.of_nat (length sbs) = n.
Hypothesis SBOK : NEM.bytes_ok sbs.
Hypothesis QAP : q + n <= o \/ o + 24 <= q.
Hypothesis AO : PMSPA.aobjA FF o 24.
Hypothesis O8 : o mod 8 = 0.
Hypothesis KS : kstr_at M o x.
Hypothesis KC : kcontent M o x kbs.
Hypothesis KOK : PQMA.ks_ok SM x g.
Hypothesis SMX : SM <= PQASA.SMMAX.
Hypothesis CR : PMSP.credit_le (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (x' : PM.vstr) (g' : Z) (cr' : credit),
    regs_preserved R R' -> kstr_at M' o x' -> kcontent M' o x' (kbs ++ sbs) -> PQMA.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + n ->
    (PM.vs_size x + n <= PM.vs_cap x -> PM.vs_own x' = PM.vs_own x /\ g' = g) ->
    L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr PQASA.INS_H) W M M' ->
    PMSP.credit_keep cr cr' (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x' g')) ->
    model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
    ri_inv HI (PM.vs_own x' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Local Notation OWN := (own12 sp R).
Local Notation OC := (ocell12 sp).

(* [comment removed for export] *)
Lemma o_facts : 7036928 <= o /\ o + 24 <= ahl_ceil ar /\ o + 24 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= o \/ o + 24 <= 2147446784).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_298 ())). Qed.
Lemma wappW : PMKA.wapp W.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_299 ())). Qed.
(* [comment removed for export] *)
Local Notation "'GX' f" := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r PQASA.INS_H BX0 W HH AM K0 ENT FRM FRS Hh2 wappW) (at level 10, f at level 9, only parsing).

Lemma sp_facts : 140735332487264 + 16 <= V2 /\ V2 + cls <= 140737488355328 /\ (V2 + cls) mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_300 ())). Qed.
Lemma V2_lo : 140735332487360 <= V2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_301 ())). Qed.
Lemma HSPCf : sp - 2048 <= spc /\ spc mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_302 ())). Qed.
Lemma x_facts : 0 <= PM.vs_size x <= SM /\ 0 <= g.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_303 ())). Qed.

(* [comment removed for export] *)
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK Aw sp (PMSPA.pm_scr PQASA.INS_H) spc (sp - 96) sp OC OWN F fl 1 LK2 M2 model2 cr BX0.
Hypothesis APART : forall a n0 sp0 scr0, (forall i, 0 <= i < n0 -> aclient L ar (BX0 ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n0 ->
         (a + n0 <= F \/ F + ff_bytes 1 <= a) /\ (a + n0 <= F / 8 + SB \/ F / 8 + SB + ff_bytes 1 / 8 <= a) /\ (a + n0 <= fl \/ fl + 1 <= a).
Local Notation FF' := ((F, 1, spc + 32) :: FF).
(* [comment removed for export] *)
Local Notation GM := (PQAKR3.g_mem L ar HI M model LBX FF LK Aw sp PQASA.INS_H W spc OWN 1 F).
Local Notation "'GF' f" := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r PQASA.INS_H BX0 W HH AM K0 ENT FRM FRS Hh2 wappW spc (sp - 96) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Definition vals (j : nat) : Z :=
  match j with 2%nat => spc | 3%nat => pa_gp AD | 4%nat => hl_tp L | 8%nat => sp | 9%nat => spc | 18%nat => F | 19%nat => n | 20%nat => o | 21%nat => q + n
             | 22%nat => q | 25%nat => F / 8 + 2147450880 | 26%nat => F | 27%nat => bvu (getr R (reg 27)) | _ => 0 end.
Definition IXA : list nat := [2; 3; 4; 8; 9; 18; 25; 26; 27]%nat.
Definition IXC : list nat := [3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]%nat.
Definition IX : list nat := (2 :: IXC)%nat.
Local Notation REGSA := (regl IXA vals).
Local Notation REGS := (regl IX vals).
Local Notation REGSC := (regl IXC vals).

(* [comment removed for export] *)
Ltac pf BIx :=
  destruct ((GF PQAKR3.g_pfacts) _ _ _ _ _ _ BIx) as ((PF1 & PF2 & PF3 & PF4 & _) & (FD & FW & FSW & FLU & FLW) & (PL1 & PL2 & PL3 & PL4) & (SW & OWNV & PS1 & PS2 & PS3 & PS4) & (CSB & CUAR & IMGC) & (AVSH & AVF & AVS));
  change (ff_bytes 1) with 128 in *; change (128 / 8) with 16 in *.

(* [comment removed for export] *)
Lemma STKSH4 BX1 M1 model1 LK1 Aw1 cr1 : GM BX1 M1 model1 LK1 Aw1 cr1 -> L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) ((V2 - 160) / 8 + 2147450880) 4.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_304 ())). Qed.


(* [comment removed for export] *)
Lemma KSKEEP LB1 FFx spx scr (M1 M3 : mem) y :
  (forall f, In f FFx -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) -> (forall b, In b LB1 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  L5SAR.ek L ar LB1 FFx spx scr [] M1 M3 -> incl (PM.vs_own y) LB1 -> PMSPA.aobjA FFx o 24 -> kstr_at M1 o y -> kstr_at M3 o y.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_305 ())). Qed.

(* [comment removed for export] *)
Lemma KCKEEP LB1 FFx spx scr (M1 M3 : mem) y cs :
  (forall f, In f FFx -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) -> (forall b, In b LB1 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  L5SAR.ek L ar LB1 FFx spx scr [] M1 M3 -> incl (PM.vs_own y) LB1 -> PMSPA.aobjA FFx o 24 -> kstr_at M1 o y -> kcontent M1 o y cs -> kcontent M3 o y cs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_306 ())). Qed.
(* [comment removed for export] *)
Lemma kc_nil0 (M1 : mem) : n = 0 -> kcontent M1 o x kbs -> kcontent M1 o x (kbs ++ sbs).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_307 ())). Qed.

(* [comment removed for export] *)
Lemma FIN M5 model5 LK5 Aw5 cr5 (fx5 : FPState) R5 (y : PM.vstr) (g' : Z) :
  GM (PM.vs_own y) M5 model5 LK5 Aw5 cr5 -> REGSA R5 ->
  kstr_at M5 o y -> kcontent M5 o y (kbs ++ sbs) -> PQMA.ks_ok SM y g' -> PM.vs_size y = PM.vs_size x + n ->
  (PM.vs_size x + n <= PM.vs_cap x -> PM.vs_own y = PM.vs_own x /\ g' = g) ->
  PMSP.credit_keep cr cr5 (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y g')) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 RETIRE M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_308 ())). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma GEK BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) (Wp : Z -> Prop) :
  GM BX1 M1 model1 LK1 Aw1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (sp - PMSPA.pm_scr PQASA.INS_H <= a < sp) \/ (F <= a < F + 128) \/ (F / 8 + SB <= a < F / 8 + SB + 16)) ->
  L5SAR.ek L ar (BX1 ++ LBX) FF sp (PMSPA.pm_scr PQASA.INS_H) [] M1 M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_309 ())). Qed.

(* [comment removed for export] *)
Lemma KSX BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) (Wp : Z -> Prop) y :
  GM BX1 M1 model1 LK1 Aw1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (sp - PMSPA.pm_scr PQASA.INS_H <= a < sp) \/ (F <= a < F + 128) \/ (F / 8 + SB <= a < F / 8 + SB + 16)) ->
  incl (PM.vs_own y) BX1 -> kstr_at M1 o y -> kstr_at M3 o y.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_310 ())). Qed.

(* [comment removed for export] *)
Lemma SRCX LB1 (M1 M3 : mem) LB3 FF3 LK3 cr3 Aw3 V3 :
  L5SAR.ek L ar LB1 FF sp (PMSPA.pm_scr PQASA.INS_H) [] M1 M3 -> incl LBX LB1 -> ri_inv HI LB3 FF3 LK3 cr3 Aw3 M3 V3 ->
  PQASA.src_okA RSEGS L HI M1 LBX FF q n -> PQASA.src_okA RSEGS L HI M3 LBX FF q n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_311 ())). Qed.

(* [comment removed for export] *)
Lemma KCX BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) (Wp : Z -> Prop) y cs :
  GM BX1 M1 model1 LK1 Aw1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (sp - PMSPA.pm_scr PQASA.INS_H <= a < sp) \/ (F <= a < F + 128) \/ (F / 8 + SB <= a < F / 8 + SB + 16)) ->
  incl (PM.vs_own y) BX1 -> kstr_at M1 o y -> kcontent M1 o y cs -> kcontent M3 o y cs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_312 ())). Qed.
(* [comment removed for export] *)
Lemma SBX LB1 (M1 M3 : mem) :
  L5SAR.ek L ar LB1 FF sp (PMSPA.pm_scr PQASA.INS_H) [] M1 M3 -> incl LBX LB1 ->
  PQASA.src_okA RSEGS L HI M1 LBX FF q n -> L5.bytes_at RSEGS M1 q sbs -> L5.bytes_at RSEGS M3 q sbs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_313 ())). Qed.

(* [comment removed for export] *)
Lemma src_push (M1 : mem) f : PQASA.src_okA RSEGS L HI M1 LBX FF q n -> PQASA.src_okA RSEGS L HI M1 LBX (f :: FF) q n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_314 ())). Qed.

(* [comment removed for export] *)
Lemma OSA (M1 : mem) LK1 cr1 Aw1 V1 FFx p c :
  ri_inv HI ((p, c) :: LBX) FFx LK1 cr1 Aw1 M1 V1 -> PQASA.src_okA RSEGS L HI M1 LBX FFx q n -> 0 < n -> q + n <= p \/ p + c <= q.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_315 ())). Qed.

(* [comment removed for export] *)
Lemma OAP : (o + 24 <= F \/ F + 128 <= o) /\ (o / 8 + SB + 3 <= F / 8 + SB \/ F / 8 + SB + 16 <= o / 8 + SB) /\ (o + 24 <= fl \/ fl + 1 <= o).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_316 ())). Qed.

(* [comment removed for export] *)
Lemma PBF BX1 M1 model1 LK1 Aw1 cr1 p c :
  GM BX1 M1 model1 LK1 Aw1 cr1 -> In (p, c) BX1 ->
  4096 <= p /\ p mod 16 = 0 /\ 0 < c /\ p + c <= ahl_ceil ar /\ p + c <= 2 ^ 47 /\ (p + c <= o \/ o + 24 <= p).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_317 ())). Qed.

(* [comment removed for export] *)
Lemma KSF BX1 M1 model1 LK1 Aw1 cr1 y :
  GM BX1 M1 model1 LK1 Aw1 cr1 -> kstr_at M1 o y ->
  L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (o / 8 + 2147450880) 3 /\ avis (ahid Aw1 model1) o 24 /\
  match y with
  | PM.VShort n0 => L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) o (2 * n0) /\ 0 <= 2 * n0 <= 44 /\ Z.testbit (2 * n0) 0 = false /\ 0 <= n0 <= 22
  | PM.VLong c n0 p => L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) o ((c + 1) mod 256) /\ 0 <= (c + 1) mod 256 <= 255 /\ Z.testbit ((c + 1) mod 256) 0 = true
      /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (o + 8) n0 /\ 0 <= n0 <= 2147483648
      /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (o + 16) p /\ 0 <= n0 < c /\ 26 <= c <= 2147483648
  end.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_318 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CALL M4 model4 (fx4 : FPState) R4 :
  GM BX0 M4 model4 LK2 Aw cr -> kstr_at M4 o x -> kcontent M4 o x kbs -> PQASA.src_okA RSEGS L HI M4 LBX FF q n -> L5.bytes_at RSEGS M4 q sbs -> 0 < n ->
  REGSA R4 -> getr R4 (reg 1) = Z_to_bv 64 RA_SC ->
  getr R4 (reg 10) = Z_to_bv 64 o -> getr R4 (reg 11) = Z_to_bv 64 n -> getr R4 (reg 12) = Z_to_bv 64 (PM.vs_size x) ->
  getr R4 (reg 13) = Z_to_bv 64 q -> getr R4 (reg 14) = Z_to_bv 64 (q + n) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 SCPC M4 model4) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_319 ())). Qed.

(* [comment removed for export] *)
Lemma C4CALL M5 model5 (fx5 : FPState) R5 :
  GM BX0 M5 model5 LK2 Aw cr -> kstr_at M5 o x -> kcontent M5 o x kbs -> PQASA.src_okA RSEGS L HI M5 LBX FF q n -> L5.bytes_at RSEGS M5 q sbs -> 0 < n ->
  REGS R5 -> getr R5 (reg 10) = Z_to_bv 64 0 -> getr R5 (reg 23) = Z_to_bv 64 (PM.vs_size x) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 RA_IPR M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_320 ())). Qed.

(* [comment removed for export] *)
Definition WP5 (a : Z) : Prop :=
  (V2 - 136 <= a < V2 - 136 + 8) \/ (V2 - 144 <= a < V2 - 144 + 8) \/ (V2 - 152 <= a < V2 - 152 + 8) \/ (V2 - 160 <= a < V2 - 160 + 8) \/ (V2 - 184 <= a < V2 - 184 + 8).

(* [comment removed for export] *)
Lemma K2A M4 model4 (fx4 : FPState) R4 :
  GM BX0 M4 model4 LK2 Aw cr -> kstr_at M4 o x -> kcontent M4 o x kbs -> PQASA.src_okA RSEGS L HI M4 LBX FF q n -> L5.bytes_at RSEGS M4 q sbs -> 0 < n ->
  REGSC R4 -> getr R4 (reg 2) = Z_to_bv 64 (V2 - 176) -> getr R4 (reg 10) = Z_to_bv 64 1 -> getr R4 (reg 23) = Z_to_bv 64 (PM.vs_size x) ->
  L5.u64_at RSEGS (mrestrict (ahid Aw model4) M4) (V2 - 136) 759648 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xb9f90 M4 model4) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_321 ())). Qed.

(* [comment removed for export] *)
Lemma K2B M4 model4 (fx4 : FPState) R4 (e : Z) :
  GM BX0 M4 model4 LK2 Aw cr -> kstr_at M4 o x -> kcontent M4 o x kbs -> PQASA.src_okA RSEGS L HI M4 LBX FF q n -> L5.bytes_at RSEGS M4 q sbs -> 0 < n ->
  REGSC R4 -> getr R4 (reg 2) = Z_to_bv 64 (V2 - 176) -> getr R4 (reg 10) = Z_to_bv 64 0 -> getr R4 (reg 23) = Z_to_bv 64 (PM.vs_size x) ->
  L5.u64_at RSEGS (mrestrict (ahid Aw model4) M4) (V2 - 136) 759648 ->
  L5.u64_at RSEGS (mrestrict (ahid Aw model4) M4) (V2 - 160) q ->
  L5.u64_at RSEGS (mrestrict (ahid Aw model4) M4) (V2 - 152) e -> 0 <= e -> e <= q ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xb9f90 M4 model4) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_322 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CHAIN M3 model3 (fx3 : FPState) R3 :
  GM BX0 M3 model3 LK2 Aw cr -> kstr_at M3 o x -> kcontent M3 o x kbs -> PQASA.src_okA RSEGS L HI M3 LBX FF q n -> L5.bytes_at RSEGS M3 q sbs -> 0 < n ->
  REGS R3 -> getr R3 (reg 23) = Z_to_bv 64 (PM.vs_size x) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 CALLP M3 model3) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_323 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WPB (a : Z) : Prop := (V2 - 104 <= a < V2 - 104 + 8) \/ (F + 0 <= a < F + 0 + 24) \/ (F / 8 + 2147450880 + 0 <= a < F / 8 + 2147450880 + 0 + 12).

(* [comment removed for export] *)
Lemma SETUP (fx2 : FPState) (R2 : bvmap 5 word) :
  GM BX0 M2 model2 LK2 Aw cr -> L5SAR.ek L ar (BX0 ++ LBX) FF sp (PMSPA.pm_scr PQASA.INS_H) [] M M2 ->
  getr R2 (reg 2) = Z_to_bv 64 spc -> getr R2 (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R2 (reg 8) = Z_to_bv 64 sp ->
  getr R2 (reg 9) = Z_to_bv 64 spc -> getr R2 (reg 10) = Z_to_bv 64 F -> getr R2 (reg 19) = Z_to_bv 64 n -> getr R2 (reg 20) = Z_to_bv 64 o ->
  getr R2 (reg 21) = Z_to_bv 64 (q + n) -> getr R2 (reg 22) = Z_to_bv 64 q -> getr R2 (reg 23) = Z_to_bv 64 (PM.vs_data o x + PM.vs_size x) -> getr R2 (reg 24) = Z_to_bv 64 2147450880 ->
  getr R2 (reg 27) = getr R (reg 27) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 RA_SM M2 model2) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_324 ())). Qed.
End Frame.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zl HV HS HC := clear - HV HS HC; Lia.lia.
Ltac enter_tac Aconc fxv MVv HRgp HRtp HV HS HC :=
  pose proof (LF2CBN( Aconc fxv R MVv (fun j : nat => match j with 2%nat => V2 | _ => 0 end) )) as P;
  L5SAR.feed P ltac:(fd);
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T19 & T20 & T21 & T22 & T23 & T24 & C26 & C25 & C24 & C23 & C22 & C21 & C20 & C19 & C18 & C9 & C8 & C1 & C0);
  apply ((GX PQAKR3.g_enter) spc (sp - 96) sp OC OWN 1 fxv fx1 R1 759200 759324 M1v);
  [ right; left; reflexivity | zl HV HS HC | exact (proj2 HSPCf) | zl HV HS HC | zl HV HS HC | zl HV HS HC | intros a Ha; unfold ocell12 in Ha; clear - HV HS HC Ha; Lia.lia
  | intros Ma Mb OW AG; apply (own12_agree sp R Ma Mb ltac:(zl HV HS HC) ltac:(zl HV HS HC) OW AG)
  | exact MS1 | exact MG1 | intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; clear - HV HS HC X; Lia.lia]
  | intros M1 VIS1 AV; unfold own12;
    repeat match goal with |- _ /\ _ => split end;
    (match goal with |- L5.u64_at _ _ ?a0 ?v0 => apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a0 v0 (AV a0 8 ltac:(zl HV HS HC) ltac:(zl HV HS HC)) ltac:(zl HV HS HC) ltac:(zl HV HS HC))) end; rewrite VIS1;
     match goal with |- L5.u64_at _ _ ?a _ => first [ replace a with (V2 + 8) by (zl HV HS HC); assumption
        | replace a with V2 by (zl HV HS HC); assumption
        | replace a with (V2 - 8) by (zl HV HS HC); assumption
        | replace a with (V2 - 16) by (zl HV HS HC); assumption
        | replace a with (V2 - 24) by (zl HV HS HC); assumption
        | replace a with (V2 - 32) by (zl HV HS HC); assumption
        | replace a with (V2 - 40) by (zl HV HS HC); assumption
        | replace a with (V2 - 48) by (zl HV HS HC); assumption
        | replace a with (V2 - 56) by (zl HV HS HC); assumption
        | replace a with (V2 - 64) by (zl HV HS HC); assumption
        | replace a with (V2 - 72) by (zl HV HS HC); assumption
        | replace a with (V2 - 80) by (zl HV HS HC); assumption
        | replace a with (V2 - 88) by (zl HV HS HC); assumption
        | replace a with (V2 - 96) by (zl HV HS HC); assumption ] end)
  | exact T2 | apply KS1; inl | exact T1 | reflexivity | zl HV HS HC |];
  intros R2 M2 model2 F fl LK2 G APART LM2 EK2 G10 RP2 _;
  apply (SETUP F fl LK2 M2 model2 G APART fx1 R2 LM2 EK2);
  [ rewrite (L5SAR.cs_of_preserved _ _ 2%nat RP2 ltac:(inl)); exact T2
  | rewrite (L5SAR.cs_of_preserved _ _ 3%nat RP2 ltac:(inl)); rewrite (KS1 3%nat) by inl; exact HRgp
  | rewrite (L5SAR.cs_of_preserved _ _ 4%nat RP2 ltac:(inl)); rewrite (KS1 4%nat) by inl; exact HRtp
  | rewrite (L5SAR.cs_of_preserved _ _ 8%nat RP2 ltac:(inl)); rewrite T8; f_equal; zl HV HS HC
  | rewrite (L5SAR.cs_of_preserved _ _ 9%nat RP2 ltac:(inl)); exact T9
  | exact G10
  | rewrite (L5SAR.cs_of_preserved _ _ 19%nat RP2 ltac:(inl)); rewrite T19; exact A14
  | rewrite (L5SAR.cs_of_preserved _ _ 20%nat RP2 ltac:(inl)); rewrite T20; exact A10
  | rewrite (L5SAR.cs_of_preserved _ _ 21%nat RP2 ltac:(inl)); rewrite T21; exact A13
  | rewrite (L5SAR.cs_of_preserved _ _ 22%nat RP2 ltac:(inl)); rewrite T22; exact A12
  | rewrite (L5SAR.cs_of_preserved _ _ 23%nat RP2 ltac:(inl)); rewrite T23; exact A11
  | rewrite (L5SAR.cs_of_preserved _ _ 24%nat RP2 ltac:(inl)); exact T24
  | rewrite (L5SAR.cs_of_preserved _ _ 27%nat RP2 ltac:(inl)); apply KS1; inl ].

Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R N0 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_325 ())). Qed.
End Run.

(* [comment removed for export] *)
Theorem ins_ok : PQASCA.ins_specCA RSEGS AD L ar HI 0xb95f0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdInC ()) ["WithHeap"] (Mh_0270_blobs1.kr_b_326 ())). Qed.

End WithHeap.
End PQAAINC.

End PnAAdInC.
Module PnAAdJnC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdStrCK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKSlotA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKStrA3c OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKStrA3d OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdJnP1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdJnP2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0201.PnAAdIkP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014.Na0_code_rba0f4_ba0f8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014.Na0_code_rba0a8_ba0ac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014.Na0_code_rbe71c_be720 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAdStrCK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKStrC3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdJnC () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5INS_HC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR36obj_pfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2or00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_02137PnStepA4PMKA9wapp_consC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC7o_factsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01K46Stdlib9micromega6VarMap1t03K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z7add_0_rI47Corelib4Init5Logic5False00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib6ZArith4Zdiv:Z_mod_multC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7kstr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4GMAXC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ45own12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ47ocell12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ47g_stkshC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC5V2_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3Hh2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC5wappWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC5HSPCfC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS3:kstr_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4KCAPC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic9False_indC46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_ctxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_consC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=aclient_casesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_apart1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_pieceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6frb_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6brb_ofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3GEKC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_applc69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC6KSKEEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z;div_le_monoC59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA:accA_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C9rdn_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7src_okAC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC6KCKEEPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02566PmAUar6PMAUAR:aobjA_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_hiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<block_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAReset16PMARS1?own_not_aclientC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<client_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes?RelationClasses>eq_equivalenceC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrK46Stdlib9micromega=RingMicromega3Op206C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK=blk_obj_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8avis_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9u8_at_visC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z>testbit_even_0C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS37tb_longC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38word_visC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitK47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR3>g_callee_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_pfactsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAKStrC37PQAKZC39sc_specCAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC8src_pushC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR37g_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP28qjR_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR36g_footC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflc69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3KSXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3KCXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3cfgC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR37g_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC4SCPCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3IXAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC5RA_SCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC6RETIREC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3OAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213:PnAKStrA3c6PQAKZ36SC_SCRC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP26KS_qjRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP29qjC4_concC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_apprc69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC4SRCXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3SBXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG38regl_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC4CALLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC6RA_IPRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC2IXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC7x_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5SMMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdJnP28PQAAJNP27KS_qjC4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP:qkC2a_concC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_consC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC6C4CALLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3IXCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP8KS_qkC2aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0a8_ba0ac7W_b9f64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0a8_ba0ac7F_b9f64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0a8_ba0ac7D_b9f64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC6STKSH4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR39stk_w_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP:qkC2b_concC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ47g_footLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8aclientwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP9qkC3_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKStrA3d6PQAKZ4;g_piece_lowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP8KS_qkC2bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0f4_ba0f87W_b9fb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0f4_ba0f87F_b9fb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rba0f4_ba0f87D_b9fb0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02018PnAAdIkP7PQAAIKP7KS_qkC3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA8src_okCAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256:PnAKSlotA36PQAKS36cls_ofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02708PnAAdJnC7PQAAJNC3RUNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA:ins_specCAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.
(* [comment removed for export] *)
Local Ltac flia := L5FastLia.plia.
Local Ltac fd := first [assumption | flia].

Module PQAAJNC.
Import L5A L5SAR PQAKG3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation accA := PMSPA.accA.
Abbreviation kstr_at := (PQMA.kstr_at RSEGS accA).
Abbreviation kcontent := (NEM.kcontent RSEGS).
Abbreviation bvu x := (bv_unsigned x).
Import PQAKZ4.

(* [comment removed for export] *)
Definition N0 : Z := 0xbe330.
Definition RA_SM : Z := 0xbe3ac.
Definition CALLP : Z := 0xbe494.
Definition RA_IPR : Z := 0xbe4a0.
Definition RA_SC : Z := 0xbe4f4.
Definition RETIRE : Z := 0xbe55c.
Definition RET : Z := 0xbe628.
Definition SCPC : Z := 0xbe70c.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Hypothesis SC : PQAKZC3.sc_specCA L ar HI 0xbe70c.

Lemma Hh2 : 1 <= PQASA.INS_H <= 16.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"] (Mh_0270_blobs1.kr_b_327 ())). Qed.

(* [comment removed for export] *)
Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (V2 cls r o q n SM g : Z) (x : PM.vstr) (kbs sbs : list Z).
Local Notation sp := (V2 + cls).
Local Notation spc := (V2 - 128).
Local Notation W := ([(o, 24)] : list L5.range).
Local Notation BX0 := (PM.vs_own x).
Hypothesis Hcls : cls = 0 \/ cls = 16.
Hypothesis V32 : V2 mod 32 = 0.
Hypothesis HH : ri_inv HI (BX0 ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r PQASA.INS_H.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM PQASA.INS_H FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 o.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 (PM.vs_data o x + PM.vs_size x).
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 q.
Hypothesis A13 : getr R (reg 13) = Z_to_bv 64 (q + n).
Hypothesis A14 : getr R (reg 14) = Z_to_bv 64 n.
Hypothesis Hn : 0 <= n.
Hypothesis HSM : PM.vs_size x + n <= SM.
Hypothesis SRC : PQASA.src_okA RSEGS L HI M LBX FF q n.
Hypothesis SQ : L5.bytes_at RSEGS M q sbs.
Hypothesis SLEN : Z.of_nat (length sbs) = n.
Hypothesis SBOK : NEM.bytes_ok sbs.
Hypothesis QAP : q + n <= o \/ o + 24 <= q.
Hypothesis AO : PMSPA.aobjA FF o 24.
Hypothesis O8 : o mod 8 = 0.
Hypothesis KS : kstr_at M o x.
Hypothesis KC : kcontent M o x kbs.
Hypothesis KOK : PQMA.ks_ok SM x g.
Hypothesis SMX : SM <= PQASA.SMMAX.
Hypothesis CR : PMSP.credit_le (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (x' : PM.vstr) (g' : Z) (cr' : credit),
    regs_preserved R R' -> kstr_at M' o x' -> kcontent M' o x' (kbs ++ sbs) -> PQMA.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + n ->
    (PM.vs_size x + n <= PM.vs_cap x -> PM.vs_own x' = PM.vs_own x /\ g' = g) ->
    L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr PQASA.INS_H) W M M' ->
    PMSP.credit_keep cr cr' (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x' g')) ->
    model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
    ri_inv HI (PM.vs_own x' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Local Notation OWN := (own12 sp R).
Local Notation OC := (ocell12 sp).

(* [comment removed for export] *)
Lemma o_facts : 7036928 <= o /\ o + 24 <= ahl_ceil ar /\ o + 24 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= o \/ o + 24 <= 2147446784).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_328 ())). Qed.
Lemma wappW : PMKA.wapp W.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_329 ())). Qed.
(* [comment removed for export] *)
Local Notation "'GX' f" := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r PQASA.INS_H BX0 W HH AM K0 ENT FRM FRS Hh2 wappW) (at level 10, f at level 9, only parsing).

Lemma sp_facts : 140735332487264 + 16 <= V2 /\ V2 + cls <= 140737488355328 /\ (V2 + cls) mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_330 ())). Qed.
Lemma V2_lo : 140735332487360 <= V2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_331 ())). Qed.
Lemma HSPCf : sp - 2048 <= spc /\ spc mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_332 ())). Qed.
Lemma x_facts : 0 <= PM.vs_size x <= SM /\ 0 <= g.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"] (Mh_0270_blobs1.kr_b_333 ())). Qed.

(* [comment removed for export] *)
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK Aw sp (PMSPA.pm_scr PQASA.INS_H) spc (sp - 96) sp OC OWN F fl 1 LK2 M2 model2 cr BX0.
Hypothesis APART : forall a n0 sp0 scr0, (forall i, 0 <= i < n0 -> aclient L ar (BX0 ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n0 ->
         (a + n0 <= F \/ F + ff_bytes 1 <= a) /\ (a + n0 <= F / 8 + SB \/ F / 8 + SB + ff_bytes 1 / 8 <= a) /\ (a + n0 <= fl \/ fl + 1 <= a).
Local Notation FF' := ((F, 1, spc + 32) :: FF).
(* [comment removed for export] *)
Local Notation GM := (PQAKR3.g_mem L ar HI M model LBX FF LK Aw sp PQASA.INS_H W spc OWN 1 F).
Local Notation "'GF' f" := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r PQASA.INS_H BX0 W HH AM K0 ENT FRM FRS Hh2 wappW spc (sp - 96) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Definition vals (j : nat) : Z :=
  match j with 2%nat => spc | 3%nat => pa_gp AD | 4%nat => hl_tp L | 8%nat => sp | 9%nat => spc | 18%nat => F | 19%nat => n | 20%nat => o | 21%nat => q + n
             | 22%nat => q | 25%nat => F / 8 + 2147450880 | 26%nat => F | 27%nat => bvu (getr R (reg 27)) | _ => 0 end.
Definition IXA : list nat := [2; 3; 4; 8; 9; 18; 25; 26; 27]%nat.
Definition IXC : list nat := [3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]%nat.
Definition IX : list nat := (2 :: IXC)%nat.
Local Notation REGSA := (regl IXA vals).
Local Notation REGS := (regl IX vals).
Local Notation REGSC := (regl IXC vals).

(* [comment removed for export] *)
Ltac pf BIx :=
  destruct ((GF PQAKR3.g_pfacts) _ _ _ _ _ _ BIx) as ((PF1 & PF2 & PF3 & PF4 & _) & (FD & FW & FSW & FLU & FLW) & (PL1 & PL2 & PL3 & PL4) & (SW & OWNV & PS1 & PS2 & PS3 & PS4) & (CSB & CUAR & IMGC) & (AVSH & AVF & AVS));
  change (ff_bytes 1) with 128 in *; change (128 / 8) with 16 in *.

(* [comment removed for export] *)
Lemma STKSH4 BX1 M1 model1 LK1 Aw1 cr1 : GM BX1 M1 model1 LK1 Aw1 cr1 -> L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) ((V2 - 160) / 8 + 2147450880) 4.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_334 ())). Qed.


(* [comment removed for export] *)
Lemma KSKEEP LB1 FFx spx scr (M1 M3 : mem) y :
  (forall f, In f FFx -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) -> (forall b, In b LB1 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  L5SAR.ek L ar LB1 FFx spx scr [] M1 M3 -> incl (PM.vs_own y) LB1 -> PMSPA.aobjA FFx o 24 -> kstr_at M1 o y -> kstr_at M3 o y.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_335 ())). Qed.

(* [comment removed for export] *)
Lemma KCKEEP LB1 FFx spx scr (M1 M3 : mem) y cs :
  (forall f, In f FFx -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) -> (forall b, In b LB1 -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  L5SAR.ek L ar LB1 FFx spx scr [] M1 M3 -> incl (PM.vs_own y) LB1 -> PMSPA.aobjA FFx o 24 -> kstr_at M1 o y -> kcontent M1 o y cs -> kcontent M3 o y cs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_336 ())). Qed.
(* [comment removed for export] *)
Lemma kc_nil0 (M1 : mem) : n = 0 -> kcontent M1 o x kbs -> kcontent M1 o x (kbs ++ sbs).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_337 ())). Qed.

(* [comment removed for export] *)
Lemma FIN M5 model5 LK5 Aw5 cr5 (fx5 : FPState) R5 (y : PM.vstr) (g' : Z) :
  GM (PM.vs_own y) M5 model5 LK5 Aw5 cr5 -> REGSA R5 ->
  kstr_at M5 o y -> kcontent M5 o y (kbs ++ sbs) -> PQMA.ks_ok SM y g' -> PM.vs_size y = PM.vs_size x + n ->
  (PM.vs_size x + n <= PM.vs_cap x -> PM.vs_own y = PM.vs_own x /\ g' = g) ->
  PMSP.credit_keep cr cr5 (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM x g)) (PMSPA.scA L (PQMA.pot_ks (PMSPA.HV L ar) SM y g')) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 RETIRE M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_338 ())). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma GEK BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) (Wp : Z -> Prop) :
  GM BX1 M1 model1 LK1 Aw1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (sp - PMSPA.pm_scr PQASA.INS_H <= a < sp) \/ (F <= a < F + 128) \/ (F / 8 + SB <= a < F / 8 + SB + 16)) ->
  L5SAR.ek L ar (BX1 ++ LBX) FF sp (PMSPA.pm_scr PQASA.INS_H) [] M1 M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_339 ())). Qed.

(* [comment removed for export] *)
Lemma KSX BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) (Wp : Z -> Prop) y :
  GM BX1 M1 model1 LK1 Aw1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (sp - PMSPA.pm_scr PQASA.INS_H <= a < sp) \/ (F <= a < F + 128) \/ (F / 8 + SB <= a < F / 8 + SB + 16)) ->
  incl (PM.vs_own y) BX1 -> kstr_at M1 o y -> kstr_at M3 o y.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_340 ())). Qed.

(* [comment removed for export] *)
Lemma SRCX LB1 (M1 M3 : mem) LB3 FF3 LK3 cr3 Aw3 V3 :
  L5SAR.ek L ar LB1 FF sp (PMSPA.pm_scr PQASA.INS_H) [] M1 M3 -> incl LBX LB1 -> ri_inv HI LB3 FF3 LK3 cr3 Aw3 M3 V3 ->
  PQASA.src_okA RSEGS L HI M1 LBX FF q n -> PQASA.src_okA RSEGS L HI M3 LBX FF q n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_341 ())). Qed.

(* [comment removed for export] *)
Lemma KCX BX1 M1 model1 LK1 Aw1 cr1 (M3 : mem) (Wp : Z -> Prop) y cs :
  GM BX1 M1 model1 LK1 Aw1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (sp - PMSPA.pm_scr PQASA.INS_H <= a < sp) \/ (F <= a < F + 128) \/ (F / 8 + SB <= a < F / 8 + SB + 16)) ->
  incl (PM.vs_own y) BX1 -> kstr_at M1 o y -> kcontent M1 o y cs -> kcontent M3 o y cs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_342 ())). Qed.
(* [comment removed for export] *)
Lemma SBX LB1 (M1 M3 : mem) :
  L5SAR.ek L ar LB1 FF sp (PMSPA.pm_scr PQASA.INS_H) [] M1 M3 -> incl LBX LB1 ->
  PQASA.src_okA RSEGS L HI M1 LBX FF q n -> L5.bytes_at RSEGS M1 q sbs -> L5.bytes_at RSEGS M3 q sbs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_343 ())). Qed.

(* [comment removed for export] *)
Lemma src_push (M1 : mem) f : PQASA.src_okA RSEGS L HI M1 LBX FF q n -> PQASA.src_okA RSEGS L HI M1 LBX (f :: FF) q n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_344 ())). Qed.

(* [comment removed for export] *)
Lemma OSA (M1 : mem) LK1 cr1 Aw1 V1 FFx p c :
  ri_inv HI ((p, c) :: LBX) FFx LK1 cr1 Aw1 M1 V1 -> PQASA.src_okA RSEGS L HI M1 LBX FFx q n -> 0 < n -> q + n <= p \/ p + c <= q.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_345 ())). Qed.

(* [comment removed for export] *)
Lemma OAP : (o + 24 <= F \/ F + 128 <= o) /\ (o / 8 + SB + 3 <= F / 8 + SB \/ F / 8 + SB + 16 <= o / 8 + SB) /\ (o + 24 <= fl \/ fl + 1 <= o).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_346 ())). Qed.

(* [comment removed for export] *)
Lemma PBF BX1 M1 model1 LK1 Aw1 cr1 p c :
  GM BX1 M1 model1 LK1 Aw1 cr1 -> In (p, c) BX1 ->
  4096 <= p /\ p mod 16 = 0 /\ 0 < c /\ p + c <= ahl_ceil ar /\ p + c <= 2 ^ 47 /\ (p + c <= o \/ o + 24 <= p).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_347 ())). Qed.

(* [comment removed for export] *)
Lemma KSF BX1 M1 model1 LK1 Aw1 cr1 y :
  GM BX1 M1 model1 LK1 Aw1 cr1 -> kstr_at M1 o y ->
  L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (o / 8 + 2147450880) 3 /\ avis (ahid Aw1 model1) o 24 /\
  match y with
  | PM.VShort n0 => L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) o (2 * n0) /\ 0 <= 2 * n0 <= 44 /\ Z.testbit (2 * n0) 0 = false /\ 0 <= n0 <= 22
  | PM.VLong c n0 p => L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) o ((c + 1) mod 256) /\ 0 <= (c + 1) mod 256 <= 255 /\ Z.testbit ((c + 1) mod 256) 0 = true
      /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (o + 8) n0 /\ 0 <= n0 <= 2147483648
      /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (o + 16) p /\ 0 <= n0 < c /\ 26 <= c <= 2147483648
  end.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_348 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CALL M4 model4 (fx4 : FPState) R4 :
  GM BX0 M4 model4 LK2 Aw cr -> kstr_at M4 o x -> kcontent M4 o x kbs -> PQASA.src_okA RSEGS L HI M4 LBX FF q n -> L5.bytes_at RSEGS M4 q sbs -> 0 < n ->
  REGSA R4 -> getr R4 (reg 1) = Z_to_bv 64 RA_SC ->
  getr R4 (reg 10) = Z_to_bv 64 o -> getr R4 (reg 11) = Z_to_bv 64 n -> getr R4 (reg 12) = Z_to_bv 64 (PM.vs_size x) ->
  getr R4 (reg 13) = Z_to_bv 64 q -> getr R4 (reg 14) = Z_to_bv 64 (q + n) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 SCPC M4 model4) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_349 ())). Qed.

(* [comment removed for export] *)
Lemma C4CALL M5 model5 (fx5 : FPState) R5 :
  GM BX0 M5 model5 LK2 Aw cr -> kstr_at M5 o x -> kcontent M5 o x kbs -> PQASA.src_okA RSEGS L HI M5 LBX FF q n -> L5.bytes_at RSEGS M5 q sbs -> 0 < n ->
  REGS R5 -> getr R5 (reg 10) = Z_to_bv 64 0 -> getr R5 (reg 23) = Z_to_bv 64 (PM.vs_size x) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 RA_IPR M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_350 ())). Qed.

(* [comment removed for export] *)
Definition WP5 (a : Z) : Prop :=
  (V2 - 136 <= a < V2 - 136 + 8) \/ (V2 - 144 <= a < V2 - 144 + 8) \/ (V2 - 152 <= a < V2 - 152 + 8) \/ (V2 - 160 <= a < V2 - 160 + 8) \/ (V2 - 184 <= a < V2 - 184 + 8).

(* [comment removed for export] *)
Lemma K2A M4 model4 (fx4 : FPState) R4 :
  GM BX0 M4 model4 LK2 Aw cr -> kstr_at M4 o x -> kcontent M4 o x kbs -> PQASA.src_okA RSEGS L HI M4 LBX FF q n -> L5.bytes_at RSEGS M4 q sbs -> 0 < n ->
  REGSC R4 -> getr R4 (reg 2) = Z_to_bv 64 (V2 - 176) -> getr R4 (reg 10) = Z_to_bv 64 1 -> getr R4 (reg 23) = Z_to_bv 64 (PM.vs_size x) ->
  L5.u64_at RSEGS (mrestrict (ahid Aw model4) M4) (V2 - 136) 779424 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xb9f90 M4 model4) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_351 ())). Qed.

(* [comment removed for export] *)
Lemma K2B M4 model4 (fx4 : FPState) R4 (e : Z) :
  GM BX0 M4 model4 LK2 Aw cr -> kstr_at M4 o x -> kcontent M4 o x kbs -> PQASA.src_okA RSEGS L HI M4 LBX FF q n -> L5.bytes_at RSEGS M4 q sbs -> 0 < n ->
  REGSC R4 -> getr R4 (reg 2) = Z_to_bv 64 (V2 - 176) -> getr R4 (reg 10) = Z_to_bv 64 0 -> getr R4 (reg 23) = Z_to_bv 64 (PM.vs_size x) ->
  L5.u64_at RSEGS (mrestrict (ahid Aw model4) M4) (V2 - 136) 779424 ->
  L5.u64_at RSEGS (mrestrict (ahid Aw model4) M4) (V2 - 160) q ->
  L5.u64_at RSEGS (mrestrict (ahid Aw model4) M4) (V2 - 152) e -> 0 <= e -> e <= q ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xb9f90 M4 model4) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_352 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CHAIN M3 model3 (fx3 : FPState) R3 :
  GM BX0 M3 model3 LK2 Aw cr -> kstr_at M3 o x -> kcontent M3 o x kbs -> PQASA.src_okA RSEGS L HI M3 LBX FF q n -> L5.bytes_at RSEGS M3 q sbs -> 0 < n ->
  REGS R3 -> getr R3 (reg 23) = Z_to_bv 64 (PM.vs_size x) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 CALLP M3 model3) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_353 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WPB (a : Z) : Prop := (V2 - 104 <= a < V2 - 104 + 8) \/ (F + 0 <= a < F + 0 + 24) \/ (F / 8 + 2147450880 + 0 <= a < F / 8 + 2147450880 + 0 + 12).

(* [comment removed for export] *)
Lemma SETUP (fx2 : FPState) (R2 : bvmap 5 word) :
  GM BX0 M2 model2 LK2 Aw cr -> L5SAR.ek L ar (BX0 ++ LBX) FF sp (PMSPA.pm_scr PQASA.INS_H) [] M M2 ->
  getr R2 (reg 2) = Z_to_bv 64 spc -> getr R2 (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R2 (reg 8) = Z_to_bv 64 sp ->
  getr R2 (reg 9) = Z_to_bv 64 spc -> getr R2 (reg 10) = Z_to_bv 64 F -> getr R2 (reg 19) = Z_to_bv 64 n -> getr R2 (reg 20) = Z_to_bv 64 o ->
  getr R2 (reg 21) = Z_to_bv 64 (q + n) -> getr R2 (reg 22) = Z_to_bv 64 q -> getr R2 (reg 23) = Z_to_bv 64 (PM.vs_data o x + PM.vs_size x) -> getr R2 (reg 24) = Z_to_bv 64 2147450880 ->
  getr R2 (reg 27) = getr R (reg 27) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 RA_SM M2 model2) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs1.kr_b_354 ())). Qed.
End Frame.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zl HV HS HC := clear - HV HS HC; Lia.lia.
Ltac enter_tac Aconc fxv MVv HRgp HRtp HV HS HC :=
  pose proof (LF2CBN( Aconc fxv R MVv (fun j : nat => match j with 2%nat => V2 | _ => 0 end) )) as P;
  L5SAR.feed P ltac:(fd);
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T19 & T20 & T21 & T22 & T23 & T24 & C26 & C25 & C24 & C23 & C22 & C21 & C20 & C19 & C18 & C9 & C8 & C1 & C0);
  apply ((GX PQAKR3.g_enter) spc (sp - 96) sp OC OWN 1 fxv fx1 R1 778976 779100 M1v);
  [ right; left; reflexivity | zl HV HS HC | exact (proj2 HSPCf) | zl HV HS HC | zl HV HS HC | zl HV HS HC | intros a Ha; unfold ocell12 in Ha; clear - HV HS HC Ha; Lia.lia
  | intros Ma Mb OW AG; apply (own12_agree sp R Ma Mb ltac:(zl HV HS HC) ltac:(zl HV HS HC) OW AG)
  | exact MS1 | exact MG1 | intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; clear - HV HS HC X; Lia.lia]
  | intros M1 VIS1 AV; unfold own12;
    repeat match goal with |- _ /\ _ => split end;
    (match goal with |- L5.u64_at _ _ ?a0 ?v0 => apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a0 v0 (AV a0 8 ltac:(zl HV HS HC) ltac:(zl HV HS HC)) ltac:(zl HV HS HC) ltac:(zl HV HS HC))) end; rewrite VIS1;
     match goal with |- L5.u64_at _ _ ?a _ => first [ replace a with (V2 + 8) by (zl HV HS HC); assumption
        | replace a with V2 by (zl HV HS HC); assumption
        | replace a with (V2 - 8) by (zl HV HS HC); assumption
        | replace a with (V2 - 16) by (zl HV HS HC); assumption
        | replace a with (V2 - 24) by (zl HV HS HC); assumption
        | replace a with (V2 - 32) by (zl HV HS HC); assumption
        | replace a with (V2 - 40) by (zl HV HS HC); assumption
        | replace a with (V2 - 48) by (zl HV HS HC); assumption
        | replace a with (V2 - 56) by (zl HV HS HC); assumption
        | replace a with (V2 - 64) by (zl HV HS HC); assumption
        | replace a with (V2 - 72) by (zl HV HS HC); assumption
        | replace a with (V2 - 80) by (zl HV HS HC); assumption
        | replace a with (V2 - 88) by (zl HV HS HC); assumption
        | replace a with (V2 - 96) by (zl HV HS HC); assumption ] end)
  | exact T2 | apply KS1; inl | exact T1 | reflexivity | zl HV HS HC |];
  intros R2 M2 model2 F fl LK2 G APART LM2 EK2 G10 RP2 _;
  apply (SETUP F fl LK2 M2 model2 G APART fx1 R2 LM2 EK2);
  [ rewrite (L5SAR.cs_of_preserved _ _ 2%nat RP2 ltac:(inl)); exact T2
  | rewrite (L5SAR.cs_of_preserved _ _ 3%nat RP2 ltac:(inl)); rewrite (KS1 3%nat) by inl; exact HRgp
  | rewrite (L5SAR.cs_of_preserved _ _ 4%nat RP2 ltac:(inl)); rewrite (KS1 4%nat) by inl; exact HRtp
  | rewrite (L5SAR.cs_of_preserved _ _ 8%nat RP2 ltac:(inl)); rewrite T8; f_equal; zl HV HS HC
  | rewrite (L5SAR.cs_of_preserved _ _ 9%nat RP2 ltac:(inl)); exact T9
  | exact G10
  | rewrite (L5SAR.cs_of_preserved _ _ 19%nat RP2 ltac:(inl)); rewrite T19; exact A14
  | rewrite (L5SAR.cs_of_preserved _ _ 20%nat RP2 ltac:(inl)); rewrite T20; exact A10
  | rewrite (L5SAR.cs_of_preserved _ _ 21%nat RP2 ltac:(inl)); rewrite T21; exact A13
  | rewrite (L5SAR.cs_of_preserved _ _ 22%nat RP2 ltac:(inl)); rewrite T22; exact A12
  | rewrite (L5SAR.cs_of_preserved _ _ 23%nat RP2 ltac:(inl)); rewrite T23; exact A11
  | rewrite (L5SAR.cs_of_preserved _ _ 24%nat RP2 ltac:(inl)); exact T24
  | rewrite (L5SAR.cs_of_preserved _ _ 27%nat RP2 ltac:(inl)); apply KS1; inl ].

Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R N0 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_355 ())). Qed.
End Run.

(* [comment removed for export] *)
Theorem ins_ok : PQASCA.ins_specCA RSEGS AD L ar HI 0xbe330.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdJnC ()) ["WithHeap"] (Mh_0270_blobs2.kr_b_356 ())). Qed.

End WithHeap.
End PQAAJNC.

End PnAAdJnC.
Module PnAAdNl.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdStrCK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObjA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAdStrCK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKSlotA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKCallA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKStepA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKFromA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKEncNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemFrameA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdNlP1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdNlP2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdNlP3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdNlP4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdNlP5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014.Na0_code_rb44b8_b44bc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180.Na0DiagKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdNl () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_02136PnVisA4PQVA6ndig_fC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z6ltb_geC69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF3:ndig_f_rngC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z7pow_1_rK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL9ndig_f_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA4ndigC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z6leb_gtK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL7ndig_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5w_u64C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF39ndig_f_ltC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_symK46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib7Numbers7BinNums1N01C69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF38ndig_rngC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specC69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_strC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL2LQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL2LNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL2LBC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL7lit_rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_01028NemModel3NEM5asciiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_rw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3LQNC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK7rdn_imgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL6LB_lenC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib9PnAdStrCK6PQASCK?bytes_at_of_rdnC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG37bvu_rngC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7enc_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA4PMEAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8pot_encAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA;epot_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;pot_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7pot_aeAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL9pot_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8sink_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ec_stateAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092;PnQStaticsA5PQSTA7err_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_KBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5VIS_HC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rc69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL8sp_factsC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38obj_pf_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK47Corelib4Init5Logic2or01C59OSSVerify5KrLib7Mh_0089:IcptIfaceA;icl_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA<aicl_globalsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2or02c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL4OWNEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3OCEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7ocell13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;own13_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL5V2_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List6filterC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_tC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5lv_eoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl01C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List:filter_appC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3advC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ndestC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_applC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5a_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5xinvGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3ESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6kbsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_oaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7alvl_okC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP48PQAANLP47alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6set_lvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL9ndest_advC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5s_xlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6s_advXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP48PQAANLP4=qvnAk2e0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP48PQAANLP4=qvnAk2e1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP48PQAANLP4=qvnAk1e1_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3IXAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL5HSPCfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3LSZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP48PQAANLP4;KS_qvnAk2e0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP48PQAANLP4;KS_qvnAk2e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP48PQAANLP4;KS_qvnAk1e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_WAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4EVISC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5wappWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP58PQAANLP57alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP58PQAANLP5:qvnD2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL:mem_eq_frzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA;v_null_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8aargs_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5pre_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6step_wC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP1:qvnJ1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG38regl_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3ADVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_pfactsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7s_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ENC_SLOTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3Hh3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL2IXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ENC_HC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL7oec_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL8ov_rng56C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP58PQAANLP58KS_qvnD2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL5Hbv64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8eargs_t3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP18KS_qvnJ1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP1:qvnJ2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL7DU_DPHIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP18PQAANLP18KS_qvnJ2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL4EST0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP29qvnC_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N8pb_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N6pb_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_restC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_setC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_app_asciiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_xcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N9s_call_sCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdNlP28PQAANLP27KS_qvnCC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multK46Stdlib9micromega=RingMicromega3Op206C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N9s_key_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7src_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ins_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7ins_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA8src_okCAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL7AFTER_VC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL7AFTER_KC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5INS_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8AOFF_KEYC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbc69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL4INS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_kcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lv_shapeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_kbgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8lv_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N:lv_last_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL6KEYLITC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL6PATH_DC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lv_rootC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5aeownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8args_ec3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6cls_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;evis_of_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6edepthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdNl6PQAANL3RUNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ9qa_v_nullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA;v_null_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA7pre_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8step_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3phiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA6d_nullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAANL.
Import L5A L5SAR PQAKS3N PQAKC3N PQAKT3N PQAKG3 PQAKENA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
(* [comment removed for export] *)
Ltac flia := solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ].
Ltac fd := first [assumption | flia].
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AQ := PnLayoutQA.QADDR_A.
Abbreviation AE := NemLayoutA.NEADDR_A.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation adaptor_at := (PQMA.adaptor_at RSEGS AD accA annA (qa_vp_adaptor AQ)).
Abbreviation kcontent := (NEM.kcontent RSEGS).
Abbreviation bvu x := (bv_unsigned x).

(* [comment removed for export] *)
Lemma ndig_f_lb f : forall v k, 10 ^ k <= v -> k <= Z.of_nat f -> 0 <= k -> k + 1 <= PQVA.ndig_f f v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_357 ())). Qed.
Lemma ndig_lb v k : 0 <= k <= 19 -> 10 ^ k <= v -> k + 1 <= PQVA.ndig v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_358 ())). Qed.
Lemma w_u64_ndig v : 0 <= v -> NEM.w_u64 v <= PQVA.ndig v + 2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_359 ())). Qed.
Lemma ndig_u32 v : 0 <= v < 2 ^ 32 -> PQVA.ndig v <= 10.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_360 ())). Qed.
Lemma hdr_str_ndig v : 0 <= v < 2 ^ 64 -> NEM.hdr_str (PQVA.ndig v) = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_361 ())). Qed.

(* [comment removed for export] *)
Definition LQ (t : bool) : Z := 157024.
Definition LN (t : bool) : Z := 4.
Definition LB (t : bool) : list Z := [110; 117; 108; 108].
Lemma LQN t : 65536 <= LQ t /\ LQ t + LN t <= 1409024 /\ LQ t mod 8 = 0 /\ 4 <= LN t <= 5.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_362 ())). Qed.
Lemma LB_len t : Z.of_nat (length (LB t)) = LN t.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_363 ())). Qed.
Lemma lit_rdn t : rdn RSEGS (fun _ => None) (Z_to_bv 64 (LQ t)) (Z.to_nat (LN t)) = Some (map (Z_to_bv 8) (LB t)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_364 ())). Qed.
Lemma LITR t : exists bs, length bs = Z.to_nat (LN t) /\ rdn RSEGS (fun _ => None) (Z_to_bv 64 (LQ t)) (length bs) = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_365 ())). Qed.
Lemma lit_ascii t : NEM.ascii (LB t).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_366 ())). Qed.
(* [comment removed for export] *)
Lemma lit_bytes_at (Mx : mem) t : L5.img_clear Mx 65536 (pa_rw_lo AD) -> L5.bytes_at RSEGS Mx (LQ t) (LB t) /\ NEM.bytes_ok (LB t).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_367 ())). Qed.

(* [comment removed for export] *)
Lemma aacc_join (Mx : mem) p n m : aacc Mx p n -> aacc Mx (p + n) m -> 0 <= n -> aacc Mx p (n + m).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_368 ())). Qed.
Lemma aacc_sub (Mx : mem) a0 n0 a1 n1 : aacc Mx a0 n0 -> a0 <= a1 -> a1 + n1 <= a0 + n0 -> aacc Mx a1 n1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_369 ())). Qed.

(* [comment removed for export] *)
Lemma mem_eq_frz (Ma Mb : mem) : (forall a, 0 <= a < 2 ^ 64 -> ~ False -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> Mb = Ma.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) [] (Mh_0270_blobs2.kr_b_370 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
(* [comment removed for export] *)
Hypothesis PB : PQASCA.pb_specCA RSEGS AD L ar HI 0xf4640.
Hypothesis INSJ : PQASCA.ins_specCA RSEGS AD L ar HI 0xbe330.
Hypothesis INSI : PQASCA.ins_specCA RSEGS AD L ar HI 0xb95f0.
Hypothesis VNE : NECSA.v_null_spec RSEGS AD AQ AAD AE L ar HI (NESKA.PMEA L).
Hypothesis VKE : NECSA.v_key_spec RSEGS AD AQ AAD AE L ar HI (NESKA.PMEA L).

(* [comment removed for export] *)
Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (V2 cls r oa ov osk oec cat tg cx : Z) (sa : PQMA.ast) (kbb : list Z) (en : NEM.enc) (k : NESK.sink) (bf ef : bool).
Local Notation sp := (V2 + cls).
Local Notation spc := (V2 - 128).
Local Notation EPOT := (NECSA.pot_encA L ar (NESKA.PMEA L)).
(* [comment removed for export] *)
Local Notation ESO := (NECS.eown en k).
Local Notation QE := (NECSA.pot_encA L ar (NESKA.PMEA L) en k).
Local Notation ST0 := (NEMA.AEST sa kbb en k).
(* [comment removed for export] *)
Local Notation ND := 4.
Local Notation DU := 6.
Local Notation DPHI := 6.
Hypothesis Hcls : cls = 0 \/ cls = 16.
Hypothesis V32 : V2 mod 32 = 0.
Hypothesis HH : ri_inv HI ((PQMA.aown sa ++ ESO) ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r PNVA.VIS_H.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM PNVA.VIS_H FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 oa.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 tg.
Hypothesis Htg : 0 <= tg < 2 ^ 64.
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 cx.
Hypothesis Hcx : 0 <= cx < 2 ^ 64.
Hypothesis A13 : getr R (reg 13) = Z_to_bv 64 oec.
Hypothesis AO : PMSPA.aobjA FF oa PQMA.ASIZE.
Hypothesis O8 : oa mod 8 = 0.
Hypothesis AOV : PMSPA.aobjA FF ov 56.
Hypothesis OV8 : ov mod 8 = 0.
Hypothesis AOSK : PMSPA.aobjA FF osk 24.
Hypothesis OK8 : osk mod 8 = 0.
Hypothesis AOEC : PMSPA.aobjA FF oec 16.
Hypothesis OE8 : oec mod 8 = 0.
Hypothesis APT : oa + PQMA.ASIZE <= ov \/ ov + 56 <= oa.
Hypothesis APT2 : oa + PQMA.ASIZE <= osk \/ osk + 24 <= oa.
Hypothesis APT3 : oa + PQMA.ASIZE <= oec \/ oec + 16 <= oa.
Hypothesis APT4 : ov + 56 <= osk \/ osk + 24 <= ov.
Hypothesis APT5 : oec + 16 <= ov \/ ov + 56 <= oec.
Hypothesis APT6 : oec + 16 <= osk \/ osk + 24 <= oec.
Hypothesis AA : adaptor_at M oa ov sa.
Hypothesis OACC : accA M oa PQMA.ASIZE.
Hypothesis AOK : PQMA.adaptor_ok sa.
Hypothesis VIS : EVIS M ov.
Hypothesis BASE : PMSTA.base_okA RSEGS AD M.
(* [comment removed for export] *)
Hypothesis KC : kcontent M (oa + PQMA.AOFF_KB) (PQMA.a_kb sa) kbb.
Hypothesis U8 : utf8_valid kbb = true.
Hypothesis EDEP : NEM.en_depth en = NEMA.ndest (PQMA.a_lv sa).
Hypothesis ENA : NEMA.enc_atA RSEGS AE L ar M ov osk en.
Hypothesis SKA : NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) M osk k.
Hypothesis ECS : NEMA.ec_stateA RSEGS AD M oec bf cat.
Hypothesis ERR : PQSTA.err_okA RSEGS AD AAD AQ M ef.
Hypothesis PRE : PQMA.kbsize sa + DU <= PQMA.SMB /\ NESK.sk_z k + DPHI <= NESK.SMZ.
Hypothesis CRF : PMSP.credit_le (NEMA.pot_aeA L ar ST0) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (st' : NEMA.aest) (b' e' : bool) (cr' : credit),
      regs_preserved R R' ->
      NEMA.ae_atA RSEGS AD AE L ar (qa_vp_adaptor AQ) M' oa ov osk st' -> NEMA.ae_ok st' -> NEMA.ec_stateA RSEGS AD M' oec b' cat -> PMSTA.base_okA RSEGS AD M' -> PQSTA.err_okA RSEGS AD AAD AQ M' e' ->
      (bf = true -> b' = true) -> (ef = true -> e' = true) ->
      (NEMA.nlv st' = NEMA.nlv ST0 /\ NEMA.kbsize st' <= NEMA.kbsize ST0 + DU /\ NEMA.phi st' <= NEMA.phi ST0 + DPHI /\ NEMA.esize st' = NEMA.esize ST0
       /\ NEMA.edepth st' = NEMA.edepth ST0 /\ (b' = bf \/ False)) ->
      L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr PNVA.VIS_H) (NEMA.ae_WA AD oa ov osk oec) M M' ->
      PMSP.credit_keep cr cr' (NEMA.pot_aeA L ar ST0) (NEMA.pot_aeA L ar st') ->
      model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (NEMA.aeown st' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition OWNE (Mx : mem) : Prop := own13 sp R Mx.
Definition OCE (a : Z) : Prop := ocell13 sp a.
Local Notation OWN := OWNE.
Local Notation OC := OCE.
(* [comment removed for export] *)
Lemma QENN : 0 <= fst QE /\ 0 <= snd QE.
Proof using LY ENA SKA.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_371 ())). Qed.
Local Notation "'SX' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Lemma pot_split x kb1 e1 k1 : NEMA.pot_aeA L ar (NEMA.AEST x kb1 e1 k1) = PM.credit_add (PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) x)) (EPOT e1 k1).
Proof using L ar.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_372 ())). Qed.
Lemma CR : PMSP.credit_le (PM.credit_add (PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) sa)) QE) cr.
Proof using CRF.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_373 ())). Qed.
Lemma xinv0 : PQAKENA.xinvG L ar oa ov osk oec cat M (PQMA.a_kb sa) kbb en k bf ef.
Proof using KC U8 ENA SKA ECS ERR.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_374 ())). Qed.

Lemma sp_facts : 140735332487264 + 16 <= V2 /\ V2 + cls <= 140737488355328 /\ (V2 + cls) mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof using ENT Hcls.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_375 ())). Qed.
Lemma V2_lo : 140735332487296 <= V2.
Proof using ENT Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_376 ())). Qed.
Lemma HSPCf : sp - 2048 <= spc /\ spc mod 16 = 0.
Proof using Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_377 ())). Qed.
Lemma oec_rng : 7036928 <= oec /\ oec + 16 <= 2 ^ 47.
Proof using LY HIok HH AOEC.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_378 ())). Qed.
Lemma oa_lo96 : 7036928 <= oa /\ oa + 96 <= 2 ^ 47.
Proof using LY HIok HH AO.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_379 ())). Qed.
Lemma ov_rng56 : 7036928 <= ov /\ ov + 56 <= ahl_ceil ar /\ ov + 56 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784).
Proof using LY HIok HH AOV.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_380 ())). Qed.
Lemma tg_rng : 0 <= tg < 2 ^ 64.
Proof using Htg.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_381 ())). Qed.
Lemma Hbv64 : 0 <= cx < 2 ^ 64.
Proof using Hcx.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_382 ())). Qed.
(* [comment removed for export] *)
Lemma ING t : In (LQ t, LN t + 1) (icl_globals IL).
Proof using ILY.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_383 ())). Qed.
Lemma GOWNE : forall Ma Mb, OWN Ma -> (forall a, OC a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> OWN Mb.
Proof using ENT Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_384 ())). Qed.

(* [comment removed for export] *)
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK Aw sp (PMSPA.pm_scr PNVA.VIS_H) spc (sp - 104) sp OC OWN F fl 0 LK2 M2 model2 cr (PQMA.aown sa ++ ESO).
Hypothesis APART : forall a n0 sp0 scr0, (forall i, 0 <= i < n0 -> aclient L ar ((PQMA.aown sa ++ ESO) ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n0 ->
         (a + n0 <= F \/ F + ff_bytes 0 <= a) /\ (a + n0 <= F / 8 + SB \/ F / 8 + SB + ff_bytes 0 / 8 <= a) /\ (a + n0 <= fl \/ fl + 1 <= a).
Local Notation FF' := ((F, 0, spc + 32) :: FF).
Local Notation AMF := (PQAKS3N.a_mem L ar HI M model LBX FF LK Aw cr sp oa ov osk oec sa QE spc OWN 0 F).
Local Notation xinv := (PQAKENA.xinvG L ar oa ov osk oec cat).
Local Notation "'SF' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE spc (sp - 104) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).
Local Notation "'SE' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE cat OV8 OK8 OE8 APT2 APT3 APT4 APT5 APT6 spc (sp - 104) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).
Local Notation "'SY' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE cat APT2 APT3 spc (sp - 104) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).
Local Notation "'GF' f" := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r PNVA.VIS_H (PQMA.aown sa ++ ESO) (NEMA.ae_WA AD oa ov osk oec) HH AM K0 ENT FRM FRS PQAKS3N.Hh3 (SX PQAKS3N.wappW) spc (sp - 104) sp OC OWN 0 F fl LK2 M2 model2 G APART HSPCf) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Definition vals (j : nat) : Z :=
  match j with 2%nat => spc | 3%nat => pa_gp AD | 4%nat => hl_tp L | 8%nat => sp | 18%nat => F | 19%nat => oa + 80 | 20%nat => oa | 24%nat => F
             | 25%nat => 2147450880 | 26%nat => F / 8 + 2147450880 | 27%nat => (oa + 80) / 8 + 2147450880 | _ => 0 end.
Definition IXA : list nat := [2; 3; 4; 8; 18; 19; 24; 25; 26; 27]%nat.
Definition IX : list nat := (20 :: IXA)%nat.
Local Notation REGSA := (regl IXA vals).
Local Notation REGS := (regl IX vals).

(* [comment removed for export] *)
Ltac pf LM :=
  let BIx := fresh "BIx" in pose proof (proj1 LM) as BIx;
  destruct ((GF PQAKR3.g_pfacts) _ _ _ _ _ _ BIx) as ((PF1 & PF2 & PF3 & PF4 & _) & (FD & FW & FSW & FLU & FLW) & (PL1 & PL2 & PL3 & PL4) & (SW & OWNV & PS1 & PS2 & PS3 & PS4) & (CSB & CUAR & _) & (AVSH & AVF & AVS));
  change (ff_bytes 0) with 64 in *; change (64 / 8) with 8 in *.

(* [comment removed for export] *)
Definition EST (en1 : NEM.enc) (k1 : NESK.sink) (b1 e1 : bool) : Prop :=
  NEM.en_n en1 = NEM.en_n en /\ NEM.en_depth en1 = NEM.en_depth en /\ NESK.sk_z k <= NESK.sk_z k1
  /\ (bf = true -> b1 = true) /\ (ef = true -> e1 = true) /\ (b1 = bf \/ False).
Lemma EST0 : EST en k bf ef.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_385 ())). Qed.
Lemma DU_DPHI : DU <= DPHI /\ ND + 1 <= DPHI /\ ND + 2 <= DU.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_386 ())). Qed.
(* [comment removed for export] *)
Lemma ndest_adv lv0 c : NEMA.ndest (lv0 ++ [PQAKS3N.adv c]) = NEMA.ndest (lv0 ++ [c]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_387 ())). Qed.

(* [comment removed for export] *)
Lemma FIN M5 model5 LK5 Aw5 st5 cr5 kbb5 en5 k5 (b5 e5 : bool) (fx5 : FPState) R5 :
  AMF M5 model5 LK5 Aw5 st5 (NECS.eown en5 k5) (EPOT en5 k5) cr5 -> REGSA R5 -> xinv M5 (PQMA.a_kb st5) kbb5 en5 k5 b5 e5 -> EST en5 k5 b5 e5 ->
  PQMA.nlv st5 = PQMA.nlv sa -> PQMA.kbsize st5 <= PQMA.kbsize sa + DU -> PQMA.kbsize st5 + NESK.sk_z k5 <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st5) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb4324 M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_388 ())). Qed.


(* [comment removed for export] *)
Lemma ADV M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 en1 k1 (b1 e1 : bool) (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 (NECS.eown en1 k1) (EPOT en1 k1) cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en1 k1 b1 e1 -> EST en1 k1 b1 e1 ->
  PQMA.a_lv st1 = lv0 ++ [c] ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 <= PQMA.kbsize sa + DU -> PQMA.kbsize st1 + NESK.sk_z k1 <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st1) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb42ac M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_389 ())). Qed.


(* [comment removed for export] *)
Ltac of LM ELV :=
  destruct ((SF PQAKS3N.s_oa) _ _ _ _ _ _ _ _ LM) as ((OA1 & OA2 & OA3 & OA4 & OA5) & OAZ & O16 & (OV1 & OV2 & OV3 & OV4 & OVZ & OVW) & IMG & VTZ & (OAF & OVF & OASF & OVSF) & (OAV & OAW));
  destruct ((SF PQAKS3N.s_lv) _ _ _ _ _ _ _ _ _ _ LM ELV) as (E80 & (E1 & E2 & E8 & E4 & E5) & (Z24 & Z20 & Z16 & Z8) & (CT & CK & CEO) & (CD & CW & CVIS) & (EO1 & EF1 & EV1) & ((CTR & CKR & CER & CKE) & CT1) & INL & EHI).

(* [comment removed for export] *)
Lemma PATH_D M1 model1 LK1 Aw1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> getr R1 (reg 21) = Z_to_bv 64 oec -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> PQMA.a_lv sa = lv0 ++ [c] -> PQMA.lv_t c = 0 -> PQMA.lv_eo c = 1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb3e10 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_390 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AFTER_V M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb417c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_391 ())). Qed.
(* [comment removed for export] *)
Lemma AFTER_K M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48) -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb42a0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_392 ())). Qed.


(* [comment removed for export] *)
Lemma div2_2 n : (2 * n) / 2 = n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_393 ())). Qed.
(* [comment removed for export] *)
Lemma INS_CALL (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 (ra v11 v12 v13 v14 : Z) :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = false -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  ra = (if arm then 0xb417c else 0xb42a0) ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 v11 -> getr R1 (reg 12) = Z_to_bv 64 v12 ->
  getr R1 (reg 13) = Z_to_bv 64 v13 -> getr R1 (reg 14) = Z_to_bv 64 v14 ->
  v11 = PM.vs_data (oa + 48) (PQMA.a_kb st1) + PM.vs_size (PQMA.a_kb st1) -> v12 = PM.vs_data (oa + 24) (PQMA.a_key st1) ->
  v13 = v12 + v14 -> v14 = PM.vs_size (PQMA.a_key st1) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + v14 + (if arm then 0 else 1) <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb95f0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_394 ())). Qed.

Lemma INS2 (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = true -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + PM.vs_size (PQMA.a_key st1) + (if arm then 0 else 1) <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if arm then 0xb3fb8 else 0xb4010) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_395 ())). Qed.

(* [comment removed for export] *)
Lemma KDEST M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> getr R1 (reg 21) = Z_to_bv 64 oec -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.lv_t c = 0 -> PQMA.lv_eo c = 0 ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 = PQMA.kbsize sa -> PM.vs_size (PQMA.a_key st1) <= ND ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb3f24 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_396 ())). Qed.

(* [comment removed for export] *)
Lemma COMMA (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = true -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  getr R1 (reg 1) = Z_to_bv 64 (if arm then 0xb3fb8 else 0xb4010) -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 44 ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + 1 + PM.vs_size (PQMA.a_key st1) + (if arm then 0 else 1) <= PQMA.kbsize sa + DU -> 0 <= PM.vs_size (PQMA.a_key st1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xf4640 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_397 ())). Qed.

(* [comment removed for export] *)
Lemma DISP2 M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> getr R1 (reg 21) = Z_to_bv 64 oec -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> (PQMA.lv_eo c = 0 \/ PQMA.lv_t c = 1) ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 = PQMA.kbsize sa -> 0 <= PM.vs_size (PQMA.a_key st1) <= ND ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb3f24 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_398 ())). Qed.

(* [comment removed for export] *)
Lemma KEYLIT M1 model1 LK1 Aw1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> getr R1 (reg 21) = Z_to_bv 64 oec -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> PQMA.a_lv sa = lv0 ++ [c] -> (PQMA.lv_eo c = 0 \/ PQMA.lv_t c = 1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb3e10 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_399 ())). Qed.

(* [comment removed for export] *)
Lemma DISP1 M1 model1 LK1 Aw1 cr1 kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> getr R1 (reg 21) = Z_to_bv 64 oec -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb3e10 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_400 ())). Qed.

(* [comment removed for export] *)
Lemma SETUP Mx modelx LKx Awx (fx2 : FPState) R2 :
  AMF Mx modelx LKx Awx sa ESO QE cr -> xinv Mx (PQMA.a_kb sa) kbb en k bf ef ->
  getr R2 (reg 2) = Z_to_bv 64 spc -> getr R2 (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R2 (reg 8) = Z_to_bv 64 sp ->
  getr R2 (reg 9) = Z_to_bv 64 spc -> getr R2 (reg 10) = Z_to_bv 64 F -> getr R2 (reg 20) = Z_to_bv 64 oa -> getr R2 (reg 21) = Z_to_bv 64 oec ->
  getr R2 (reg 25) = Z_to_bv 64 2147450880 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0xb3d70 Mx modelx) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_401 ())). Qed.

End Frame.

(* [comment removed for export] *)
Ltac enter_tac Aconc fxv MVv HRgp HRtp :=
  pose proof (LF2CBN( Aconc fxv R MVv (fun j : nat => match j with 2%nat => V2 | _ => 0 end) )) as P;
  L5SAR.feed P ltac:(fd);
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T20 & T21 & T22 & T23 & T25 & C27 & C26 & C25 & C24 & C23 & C22 & C21 & C20 & C19 & C18 & C9 & C8 & C1 & C0);
  apply ((SX PQAKS3N.s_enterX) spc (sp - 104) sp OC OWN 0 fxv fx1 R1 0xb3ca4 736544 M1v CR);
  [ left; reflexivity | flia | exact (proj2 HSPCf) | flia | flia | flia | intros a Ha; unfold OCE, ocell13 in Ha; flia
  | exact GOWNE
  | exact MS1 | exact MG1 | intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; flia]
  | intros M1 VIS1 AV; unfold OWNE, own13;
      repeat match goal with |- _ /\ _ => split end;
      (match goal with |- L5.u64_at _ _ ?a0 ?v0 => apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a0 v0 (AV a0 8 ltac:(flia) ltac:(flia)) ltac:(flia) ltac:(flia))) end; rewrite VIS1;
       match goal with |- L5.u64_at _ _ ?a _ => first [ replace a with (V2 + 8) by flia; assumption
          | replace a with V2 by flia; assumption
          | replace a with (V2 - 8) by flia; assumption
          | replace a with (V2 - 16) by flia; assumption
          | replace a with (V2 - 24) by flia; assumption
          | replace a with (V2 - 32) by flia; assumption
          | replace a with (V2 - 40) by flia; assumption
          | replace a with (V2 - 48) by flia; assumption
          | replace a with (V2 - 56) by flia; assumption
          | replace a with (V2 - 64) by flia; assumption
          | replace a with (V2 - 72) by flia; assumption
          | replace a with (V2 - 80) by flia; assumption
          | replace a with (V2 - 88) by flia; assumption
          | replace a with (V2 - 96) by flia; assumption
          | replace a with (V2 - 104) by flia; assumption ] end)
  | exact T2 | apply KS1; inl | exact T1 | reflexivity | flia |];
  intros R2 M2 model2 F fl LK2 G APART LM2 EK2 G10 RP2 _;
  apply (SETUP F fl LK2 M2 model2 G APART M2 model2 LK2 Aw fx1 R2 LM2);
  [ apply (PQAKENA.xinv_ekF L ar C HI LY HIok oa ov osk oec cat (proj1 oa_lo96) _ FF sp (PMSPA.pm_scr PNVA.VIS_H) M M2 sa kbb en k bf ef
             (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) AO AOV AOSK AOEC AA
             ltac:(apply incl_appl; apply incl_appl; apply incl_refl) ltac:(apply incl_appl; apply incl_appr; unfold NECS.eown; apply incl_appl; apply incl_refl)
             ltac:(apply incl_appl; apply incl_appr; unfold NECS.eown; apply incl_appr; apply incl_refl) EK2 xinv0)
  | rewrite (L5SAR.cs_of_preserved _ _ 2%nat RP2 ltac:(inl)); exact T2
  | rewrite (L5SAR.cs_of_preserved _ _ 3%nat RP2 ltac:(inl)); rewrite (KS1 3%nat) by inl; exact HRgp
  | rewrite (L5SAR.cs_of_preserved _ _ 4%nat RP2 ltac:(inl)); rewrite (KS1 4%nat) by inl; exact HRtp
  | rewrite (L5SAR.cs_of_preserved _ _ 8%nat RP2 ltac:(inl)); rewrite T8; f_equal; flia
  | rewrite (L5SAR.cs_of_preserved _ _ 9%nat RP2 ltac:(inl)); exact T9
  | exact G10
  | rewrite (L5SAR.cs_of_preserved _ _ 20%nat RP2 ltac:(inl)); rewrite T20; exact A10
  | rewrite (L5SAR.cs_of_preserved _ _ 21%nat RP2 ltac:(inl)); rewrite T21; exact A13
  | rewrite (L5SAR.cs_of_preserved _ _ 25%nat RP2 ltac:(inl)); exact T25 ].

Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb3cf4 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_402 ())). Qed.

End Run.

(* [comment removed for export] *)
Theorem null_ok : PNVA.v_null_spec RSEGS AD AQ AAD AE L ar HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdNl ()) ["WithHeap"] (Mh_0270_blobs2.kr_b_403 ())). Qed.

End WithHeap.
End PQAANL.


End PnAAdNl.
Module PnAAdVs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgTxtKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObjA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKOwner OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAHarnessKit5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemFrameA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKSlotA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKCallA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKStepA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKSlotNA3bN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKEncNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKEncNF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdVsP1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdVsP2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdVsP3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAAdVsP4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016.Na0_code_rb52d0_b52d4.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdVs () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2lec69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4own7C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvc69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS6ocell7C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic3and01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7enc_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA;epot_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA4PMEAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8pot_encAC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3ENKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4VSRAC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;pot_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS@credit_add_assocC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7pot_aeAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS9pot_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8sink_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ec_stateAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092;PnQStaticsA5PQSTA7err_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_KBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5VIS_HC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS:own7_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS8sp_factsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38obj_pf_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA3agAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS8agA_reflC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS2XVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6frb_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_objC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS9agA_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN6n_memGC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5binvNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4EVISC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_WAC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_ncwC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS5xv_ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS2CRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS5HFR64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4GOCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4GOWNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA7view_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_ctxC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS7oa_lo96C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA:accA_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8avis_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38word_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38aobj_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR3<acc8_sh0_visC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6brb_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5wappWC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK=blk_obj_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK7blk_imgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA7agA_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7src_okAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specC69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG8rdn_someC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_restC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA8src_okCAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappK47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5xinvGC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_applC69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA8xinv_ekFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS5QENNxC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List6filterC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_tC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5lv_eoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl01C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List:filter_appC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3advC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ndestC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP17alignedC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG37bvu_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP19qvsX_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS7xpieceIC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5zsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6edepthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3phiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA5akeptC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_transC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8dk_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9ahpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA8ck_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ>model_rt_transC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_tranC69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5aeownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN7n_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4valsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_retC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3IXAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP17KS_qvsXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb52d0_b52d47W_b518cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb52d0_b52d47F_b518cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb52d0_b52d47D_b518cC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9TAG_ENANOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP1:qvsJ1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP1:qvsJ2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3ADVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP18KS_qvsJ1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP18KS_qvsJ2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7ck_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8spa_modeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR6rchain00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5W_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA;eslot_specAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA;eslot_specFC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR6fvalidC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR6rchain01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02567PnAKRun5PQAKR4scr8C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multC69OSSVerify5KrLib7Mh_02567PnAKRun5PQAKR9mod16_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8mod16_8'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA;stksh_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PgTxtKitA5PGTKA;ffroom_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA16PQAKRA=model_rt_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3JMPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS9DKB_factsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_visitorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN4n_oaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3s_gC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_permC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_setC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8s_set_idC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib7Sorting;PermutationDPermutation_app_tailC69OSSVerify5KrLib7Mh_02569PnAKRunA16PQAKRA7ri_permC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7blk_outC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lvec_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN>kcontent_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C69OSSVerify5KrLib7Mh_02259NemFrameA5NEMFA9enc_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemFrameA5NEMFA:sink_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemFrameA5NEMFA>ec_state_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN8err_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lvec_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7kstr_atC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_DVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9AOFF_DESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8AOFF_KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_LVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3xvNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG38regl_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N8pb_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N6pb_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN5n_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_app_asciiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS6xcallNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS7xv_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN9n_call_sCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4XNN0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3EK0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3DK0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3CK0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4XGE0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4EST0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP2;qvsCqV_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4ADV0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS5NPUSHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3IXBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP29KS_qvsCqVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP29qvsC_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP27KS_qvsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP2;qvsCqK_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS5COLONC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP29KS_qvsCqKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multK46Stdlib9micromega=RingMicromega3Op206C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS:n_view_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ins_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7ins_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_valid_appC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3CQVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3CQKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5INS_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO7aown_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN6n_kstrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4n_pvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP38PQAAVSP37alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS8INS_CALLC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP38PQAAVSP3;qvsIVS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS6div2_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP38PQAAVSP3;qvsIVL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP38PQAAVSP3;qvsIKS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP38PQAAVSP3;qvsIKL_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_02029PnAAdVsP38PQAAVSP39KS_qvsIVSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP38PQAAVSP39KS_qvsIVLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP38PQAAVSP39KS_qvsIKSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP38PQAAVSP39KS_qvsIKLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP2:qvsQV_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4INS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP2:qvsQK_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_consC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP28KS_qvsQVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP28KS_qvsQKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lv_shapeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_kbgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8lv_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN4n_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7alvl_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG>u64_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS5QUOTEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4DESTC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP2;qvsDKz_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP2;qvsDKn_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP2;qvsDV2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP2<qvsDV1z_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP2<qvsDV1n_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3IXDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP29KS_qvsDKzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP29KS_qvsDKnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP29KS_qvsDV2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP2:KS_qvsDV1zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP28PQAAVSP2:KS_qvsDV1nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN7n_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275=PnAKSlotNA3bN7PQAKSNN6n_memEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP19qvsA_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u64_at_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS5DISP1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS5xinv0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02029PnAAdVsP18PQAAVSP17KS_qvsAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3xv0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8args_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA7pre_strC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS4tspVC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lc69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS:u64_at_injC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;evis_of_encC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02707PnAAdVs6PQAAVS3RUNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ;qa_v_stringC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8step_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8view_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8dphi_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA>v_string_specFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8TAG_NONEC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00". Local Ltac lia := L5FastLia.plia.

Module PQAAVS.
Import L5A L5SAR PQAKS3N PQAKC3N PQAKG3 PQAKSNN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac flia := solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ].
Ltac fd := first [assumption | flia].
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AQ := PnLayoutQA.QADDR_A.
Abbreviation AE := NemLayoutA.NEADDR_A.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation adaptor_at := (PQMA.adaptor_at RSEGS AD accA annA (qa_vp_adaptor AQ)).
Abbreviation bvu x := (bv_unsigned x).

(* [comment removed for export] *)
Definition VSRA : Z := 0xb4fec.

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) [] (Mh_0270_blobs2.kr_b_404 ())). Qed.

(* [comment removed for export] *)
Definition own7 (sp : Z) (R : bvmap 5 word) (M : mem) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (bvu (getr R (reg 1))) /\ L5.u64_at RSEGS M (sp - 16) (bvu (getr R (reg 8))) /\ L5.u64_at RSEGS M (sp - 24) (bvu (getr R (reg 9)))
  /\ L5.u64_at RSEGS M (sp - 32) (bvu (getr R (reg 18))) /\ L5.u64_at RSEGS M (sp - 40) (bvu (getr R (reg 19))) /\ L5.u64_at RSEGS M (sp - 48) (bvu (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (sp - 56) (bvu (getr R (reg 21))).
Definition ocell7 (sp : Z) (a : Z) : Prop := sp - 56 <= a < sp.
Lemma own7_agree sp R M1 M1' : 0 <= sp - 56 -> sp <= 2 ^ 64 ->
  own7 sp R M1 -> (forall a, ocell7 sp a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own7 sp R M1'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) [] (Mh_0270_blobs2.kr_b_405 ())). Qed.
Lemma HFR64 : 16 <= 64 <= 2048 /\ 64 mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) [] (Mh_0270_blobs2.kr_b_406 ())). Qed.
Lemma u64_at_inj (M0 : mem) a v w : L5.u64_at RSEGS M0 a v -> L5.u64_at RSEGS M0 a w -> 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> v = w.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) [] (Mh_0270_blobs2.kr_b_407 ())). Qed.
Lemma credit_add_assoc a b c : PM.credit_add (PM.credit_add a b) c = PM.credit_add a (PM.credit_add b c).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) [] (Mh_0270_blobs2.kr_b_408 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (LR : HAR.layoutR) (HIk : list (list Z) -> asan_iface)
          (tspE : Z -> Z -> list (list Z) -> list Z -> credit).
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis FAMok : HAR.asan_famR_ok L ar C SCFG LR HIk.
Hypothesis ICokF : forall D, aicpt_ok L ar IL SCFG (HIk D).
(* [comment removed for export] *)
Hypothesis TSNN : forall t q Dx RCx, 0 <= fst (tspE t q Dx RCx) /\ 0 <= snd (tspE t q Dx RCx).
Hypothesis TSANTI : forall t q Dx Dy RCx, incl Dx Dy -> PMSP.credit_le (tspE t q Dy RCx) (tspE t q Dx RCx).
Let LYa := PMA.ly_as0 L C LY.
Let HIokF (D : list (list Z)) : HAJ.asan_iface_okR L ar C SCFG (HIk D) := HAR.fr_base L ar C SCFG LR HIk FAMok D.
(* [comment removed for export] *)
Hypothesis PB : forall D, PQASCA.pb_specCA RSEGS AD L ar (HIk D) 0xf4640.
Hypothesis INSJ : forall D, PQASCA.ins_specCA RSEGS AD L ar (HIk D) 0xbe330.
Hypothesis VKE : forall D, NECSA.v_key_spec RSEGS AD AQ AAD AE L ar (HIk D) (NESKA.PMEA L).
Hypothesis VSE : NECSA.v_string_specF RSEGS AD AQ AAD AE L ar HIk (NESKA.PMEA L) tspE.

(* [comment removed for export] *)
Definition tspV (t : Z) (D : list (list Z)) (RC : list Z) : credit := tspE t VSRA D [].

Local Notation EPOT := (NECSA.pot_encA L ar (NESKA.PMEA L)).
Local Notation POT := (fun x => PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) x)).

Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (sp r oa ov osk oec cat pv d n tg ctx : Z) (sa : PQMA.ast) (kbb vbs : list Z) (en : NEM.enc) (k : NESK.sink) (bf ef : bool) (D : list (list Z)).
Local Notation HI := (HIk D).
Local Notation HIok := (HIokF D).
Local Notation ICok := (ICokF D).
Local Notation ESO := (NECS.eown en k).
Local Notation X0 := (tspE tg VSRA D []).
Local Notation QE0 := (PM.credit_add (NECSA.pot_encA L ar (NESKA.PMEA L) en k) (tspE tg VSRA D [])).
Local Notation ST0 := (NEMA.AEST sa kbb en k).
Local Notation DK := (n + 4).
Local Notation DPHI := (if tg =? NEM.TAG_ENANO then Z.max (n + 5) 15 else n + 5).
Local Notation SCR := (PMSPA.pm_scr PNVA.VIS_H).
Local Notation WA := (NEMA.ae_WA AD oa ov osk oec).
Hypothesis SP16 : sp mod 16 = 0.
Hypothesis HH : ri_inv HI ((PQMA.aown sa ++ ESO) ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r PNVA.VIS_H.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM PNVA.VIS_H FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 oa.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 pv.
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 tg.
Hypothesis A13 : getr R (reg 13) = Z_to_bv 64 ctx.
Hypothesis A14 : getr R (reg 14) = Z_to_bv 64 oec.
Hypothesis Htg : tg = NEM.TAG_NONE \/ tg = NEM.TAG_ENANO.
Hypothesis Hctx : 0 <= ctx < 2 ^ 64.
Hypothesis APV : PMSPA.aobjA FF pv 16.
Hypothesis VOK : PNVA.view_ok RSEGS M FF LBX oa ov osk pv d n.
Hypothesis AO : PMSPA.aobjA FF oa PQMA.ASIZE.
Hypothesis O8 : oa mod 8 = 0.
Hypothesis AOV : PMSPA.aobjA FF ov 56.
Hypothesis OV8 : ov mod 8 = 0.
Hypothesis AOSK : PMSPA.aobjA FF osk 24.
Hypothesis OK8 : osk mod 8 = 0.
Hypothesis AOEC : PMSPA.aobjA FF oec 16.
Hypothesis OE8 : oec mod 8 = 0.
Hypothesis APT : oa + PQMA.ASIZE <= ov \/ ov + 56 <= oa.
Hypothesis APT2 : oa + PQMA.ASIZE <= osk \/ osk + 24 <= oa.
Hypothesis APT3 : oa + PQMA.ASIZE <= oec \/ oec + 16 <= oa.
Hypothesis APT4 : ov + 56 <= osk \/ osk + 24 <= ov.
Hypothesis APT5 : oec + 16 <= ov \/ ov + 56 <= oec.
Hypothesis APT6 : oec + 16 <= osk \/ osk + 24 <= oec.
Hypothesis AA : adaptor_at M oa ov sa.
Hypothesis OACC : accA M oa PQMA.ASIZE.
Hypothesis AOK : PQMA.adaptor_ok sa.
Hypothesis VIS : EVIS M ov.
Hypothesis BASE : PMSTA.base_okA RSEGS AD M.
(* [comment removed for export] *)
Hypothesis KC : NEM.kcontent RSEGS M (oa + PQMA.AOFF_KB) (PQMA.a_kb sa) kbb.
Hypothesis U8 : utf8_valid kbb = true.
Hypothesis EDEP : NEM.en_depth en = NEMA.ndest (PQMA.a_lv sa).
Hypothesis ENA : NEMA.enc_atA RSEGS AE L ar M ov osk en.
Hypothesis SKA : NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) M osk k.
Hypothesis ECS : NEMA.ec_stateA RSEGS AD M oec bf cat.
Hypothesis ERR : PQSTA.err_okA RSEGS AD AAD AQ M ef.
(* [comment removed for export] *)
Hypothesis VBS : L5.bytes_at RSEGS M d vbs.
Hypothesis VLEN : Z.of_nat (length vbs) = n.
Hypothesis VU8 : utf8_valid vbs = true.
Hypothesis VBOK : NEM.bytes_ok vbs.
Hypothesis VR8 : tg = NEM.TAG_ENANO -> n <= 31.
Hypothesis Hn26 : 0 <= n < 2 ^ 26.   (* [comment removed for export] *)
Hypothesis PRE : PQMA.kbsize sa + DK <= PQMA.SMB /\ NESK.sk_z k + DPHI <= NESK.SMZ.
Hypothesis CRF : PMSP.credit_le (PM.credit_add (NEMA.pot_aeA L ar ST0) X0) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (st' : NEMA.aest) (b' e' : bool) (cr' : credit)
                         (D' : list (list Z)),
      regs_preserved R R' ->
      NEMA.ae_atA RSEGS AD AE L ar (qa_vp_adaptor AQ) M' oa ov osk st' -> NEMA.ae_ok st' -> NEMA.ec_stateA RSEGS AD M' oec b' cat -> PMSTA.base_okA RSEGS AD M' -> PQSTA.err_okA RSEGS AD AAD AQ M' e' ->
      (bf = true -> b' = true) -> (ef = true -> e' = true) ->
      (NEMA.nlv st' = NEMA.nlv ST0 /\ NEMA.kbsize st' <= NEMA.kbsize ST0 + DK /\ NEMA.phi st' <= NEMA.phi ST0 + DPHI /\ NEMA.esize st' = NEMA.esize ST0
       /\ NEMA.edepth st' = NEMA.edepth ST0 /\ (b' = bf \/ tg = NEM.TAG_ENANO)) ->
      L5CA.ahpres L ar LBX FF sp SCR WA M M' ->
      PMSP.credit_keep cr cr' (PM.credit_add (NEMA.pot_aeA L ar ST0) X0) (PM.credit_add (NEMA.pot_aeA L ar st') (tspE tg VSRA D' [])) ->
      model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> incl D D' ->
      ri_inv (HIk D') (NEMA.aeown st' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Local Notation OWN := (own7 sp R).
Local Notation OC := (ocell7 sp).
Local Notation spc := (sp - 64).
(* [comment removed for export] *)
Lemma ENK : 0 <= NEM.en_k en <= NEM.EKMAX.
Proof using ENA.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_409 ())). Qed.
Lemma QENN : 0 <= fst QE0 /\ 0 <= snd QE0.
Proof using LY ENA SKA TSNN.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_410 ())). Qed.
Local Notation "'SX' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE0 HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Lemma pot_split x kb1 e1 k1 : NEMA.pot_aeA L ar (NEMA.AEST x kb1 e1 k1) = PM.credit_add (POT x) (EPOT e1 k1).
Proof using L ar.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_411 ())). Qed.
Lemma CR : PMSP.credit_le (PM.credit_add (POT sa) QE0) cr.
Proof using CRF.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_412 ())). Qed.
Lemma xinv0 : PQAKENA.xinvG L ar oa ov osk oec cat M (PQMA.a_kb sa) kbb en k bf ef.
Proof using KC U8 ENA SKA ECS ERR.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_413 ())). Qed.

Lemma sp_facts : 140735332487168 + 28672 <= sp /\ sp <= 140737488355328 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof using ENT.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_414 ())). Qed.
Lemma GOCR : forall a, OC a -> sp - 64 <= a < sp.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_415 ())). Qed.
Lemma GOWN : forall M1 M1' : mem, OWN M1 -> (forall a, OC a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> OWN M1'.
Proof using ENT.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_416 ())). Qed.
Lemma oec_rng : 7036928 <= oec /\ oec + 16 <= 2 ^ 47.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_417 ())). Qed.
Lemma oa_lo96 : 7036928 <= oa /\ oa + 96 <= ahl_ceil ar /\ oa + 96 <= 2 ^ 47.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_418 ())). Qed.
Lemma ov_rng56 : 7036928 <= ov /\ ov + 56 <= ahl_ceil ar /\ ov + 56 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_419 ())). Qed.
Lemma tg_rng : 0 <= tg < 2 ^ 64.
Proof using Htg.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_420 ())). Qed.
Lemma DKB_facts : 0 <= n < 2 ^ 26.
Proof using Hn26.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_421 ())). Qed.

(* [comment removed for export] *)
Definition vals (j : nat) : Z :=
  match j with 2%nat => spc | 3%nat => pa_gp AD | 4%nat => hl_tp L | 8%nat => oa + 80 | 9%nat => pv | 12%nat => tg | 13%nat => ctx | 14%nat => oec | 18%nat => oa | 19%nat => oa + 48
             | 20%nat => 2147450880 | 21%nat => (oa + 80) / 8 + 2147450880 | 22%nat => bvu (getr R (reg 22)) | 23%nat => bvu (getr R (reg 23)) | 24%nat => bvu (getr R (reg 24))
             | 25%nat => bvu (getr R (reg 25)) | 26%nat => bvu (getr R (reg 26)) | 27%nat => bvu (getr R (reg 27)) | _ => 0 end.
Definition IXA : list nat := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition IXB : list nat := (19 :: IXA)%nat.
Definition IXD : list nat := (12 :: 13 :: 14 :: IXA)%nat.
Local Notation REGSA := (regl IXA vals).
Local Notation REGSB := (regl IXB vals).
Local Notation REGSD := (regl IXD vals).
(* [comment removed for export] *)
Ltac cvis SVIS C a := apply (PQAKR3.word_vis _ _ _ a _ (SVIS a 8 ltac:(unfold PMSPA.pm_scr, PNVA.VIS_H, PNV.VIS_H; Lia.lia) ltac:(Lia.lia)) ltac:(Lia.lia) ltac:(Lia.lia)) in C.


(* [comment removed for export] *)
(* [comment removed for export] *)
Local Notation NMG := (PQAKSNN.n_memG L ar HI M model LBX FF LK Aw cr sp oa ov osk oec sa QE0).
Local Notation NM := (PQAKSNN.n_memG L ar HI M model LBX FF LK Aw cr sp oa ov osk oec sa QE0 OWN).
Local Notation "'SN' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE0 HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE CR 64 OC OWN HFR64 GOCR GOWN) (at level 10, f at level 9, only parsing).
Local Notation xinv := (PQAKENA.xinvG L ar oa ov osk oec cat).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition XV (Mx : mem) : Prop := PMFA.agA M Mx pv 16 /\ (PMSPA.aobjA FF d n -> PMFA.agA M Mx d n).
Lemma agA_refl (Mx : mem) a m : PMFA.agA Mx Mx a m.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_422 ())). Qed.
Lemma agA_trans (M0 M1 M2 : mem) a m : PMFA.agA M0 M1 a m -> PMFA.agA M1 M2 a m -> PMFA.agA M0 M2 a m.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_423 ())). Qed.
Lemma xv0 : XV M.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_424 ())). Qed.
(* [comment removed for export] *)
Lemma xv_ek LB1 spx scr W (M1 M3 : mem) :
  L5SAR.ek L ar LB1 FF spx scr W M1 M3 -> PMKA.wapp W ->
  (forall i, pv <= i < pv + 16 -> L5.outside W i) -> (PMSPA.aobjA FF d n -> forall i, d <= i < d + n -> L5.outside W i) -> XV M1 -> XV M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_425 ())). Qed.
(* [comment removed for export] *)
Lemma xvN own' M1 model1 LK1 Aw1 st1 eso1 qe1 cr1 (M3 : mem) (Wp : Z -> Prop) :
  NMG own' M1 model1 LK1 Aw1 st1 eso1 qe1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall a, Wp a -> sp - SCR <= a < sp) ->
  XV M1 -> XV M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_426 ())). Qed.
(* [comment removed for export] *)
Lemma xv_call LBc spx scr (M1 M3 : mem) :
  L5SAR.ek L ar LBc FF spx scr [(oa + 48, 24)] M1 M3 -> XV M1 -> XV M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_427 ())). Qed.

(* [comment removed for export] *)
Lemma n_pv own' M1 model1 LK1 Aw1 st1 eso1 qe1 cr1 :
  NMG own' M1 model1 LK1 Aw1 st1 eso1 qe1 cr1 -> XV M1 ->
  let MV := mrestrict (ahid Aw1 model1) M1 in
  (7036928 <= pv /\ pv <= 140737488355312 /\ (2147446784 + 17592186048512 <= pv \/ pv + 16 <= 2147446784) /\ pv + 16 <= ahl_ceil ar /\ pv + 16 <= spc)
  /\ (L5.u64_at RSEGS MV pv d /\ L5.u64_at RSEGS MV (pv + 8) n)
  /\ (L5KA.zeros_at MV (pv / 8 + 2147450880) 1 /\ L5KA.zeros_at MV ((pv + 8) / 8 + 2147450880) 1)
  /\ (0 <= d <= 140737488355328 /\ d + n <= 140737488355328 /\ 0 <= n < 536870912)
  /\ (pv + 16 <= oa \/ oa + 96 <= pv).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_428 ())). Qed.

(* [comment removed for export] *)
Lemma n_view_src own' M1 model1 LK1 Aw1 st1 eso1 qe1 cr1 :
  NMG own' M1 model1 LK1 Aw1 st1 eso1 qe1 cr1 -> XV M1 ->
  PQASCA.src_okCA RSEGS L HI M1 ((s_rest false st1 ++ eso1) ++ LBX) FF d n vbs /\ (d + n <= oa + 48 \/ oa + 48 + 24 <= d) /\ 0 <= n < 2 ^ 29
  /\ (n = 0 \/ PMFA.agA M M1 d n).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_429 ())). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section Inst.
Variables (Dx : list (list Z)) (Mx : mem) (modelx : Model) (LKx : list fframe) (Awx : list (Z * Z)) (crx : credit) (sax : PQMA.ast)
          (enx : NEM.enc) (kx : NESK.sink) (bx ex : bool) (Xx : credit).
Local Notation HIx := (HIk Dx).
Local Notation HIokx := (HIokF Dx).
Local Notation ICokx := (ICokF Dx).
Local Notation ESOx := (NECS.eown enx kx).
Local Notation QEx := (PM.credit_add (NECSA.pot_encA L ar (NESKA.PMEA L) enx kx) Xx).
Hypothesis HHx : ri_inv HIx ((PQMA.aown sax ++ ESOx) ++ LBX) FF LKx crx Awx Mx (vml_of modelx).
Hypothesis XNN : 0 <= fst Xx /\ 0 <= snd Xx.
Hypothesis AMx : L5CA.amodel_ok Awx modelx.
Hypothesis ENTx : PMSPA.entryA AD L ar R Mx sp r PNVA.VIS_H.
Hypothesis FRMx : PGSA.ffroomB PQRA.FCM PNVA.VIS_H FF LKx.
Hypothesis AAx : adaptor_at Mx oa ov sax.
Hypothesis OACCx : accA Mx oa PQMA.ASIZE.
Hypothesis AOKx : PQMA.adaptor_ok sax.
Hypothesis VISx : EVIS Mx ov.
Hypothesis BASEx : PMSTA.base_okA RSEGS AD Mx.
Hypothesis SKAx : NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) Mx osk kx.
Hypothesis ENKx : 0 <= NEM.en_k enx <= NEM.EKMAX.
Hypothesis CRx : PMSP.credit_le (PM.credit_add (POT sax) QEx) crx.
(* [comment removed for export] *)
Hypothesis EKx : L5SAR.ek L ar LBX FF sp SCR WA M Mx.
Hypothesis DKx : L5SAR.dk L ar LBX FF sp SCR M Mx.
Hypothesis MRTx : model_rt model modelx.
Hypothesis INCAx : incl Aw Awx.
Hypothesis INCLx : incl LKx LK.
Hypothesis INCDx : incl D Dx.
Hypothesis CKx : PMSP.credit_keep cr crx (PM.credit_add (POT sa) QE0) (PM.credit_add (POT sax) QEx).
Hypothesis XGE : PMSP.credit_le (tspE tg VSRA Dx []) Xx.
(* [comment removed for export] *)
Hypothesis ESTx : NEM.en_n enx = NEM.en_n en /\ NEM.en_depth enx = NEM.en_depth en /\ (bf = true -> bx = true) /\ (ef = true -> ex = true) /\ (bx = bf \/ tg = NEM.TAG_ENANO).

Lemma QENNx : 0 <= fst QEx /\ 0 <= snd QEx.
Proof using LY SKAx ENKx XNN.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"; "Inst"] (Mh_0270_blobs2.kr_b_430 ())). Qed.
Local Notation NMGx := (PQAKSNN.n_memG L ar HIx Mx modelx LBX FF LKx Awx crx sp oa ov osk oec sax QEx).
Local Notation NMx := (PQAKSNN.n_memG L ar HIx Mx modelx LBX FF LKx Awx crx sp oa ov osk oec sax QEx OWN).
Local Notation "'SI' f" := (f L ar C IL HIx LY HIokx ICokx ILY K R Mx modelx LBX FF LKx Awx crx sp r oa ov osk oec sax ESOx QEx HHx QENNx AMx K0 ENTx FRMx FRS AO O8 AOV APT AOSK AOEC AAx OACCx AOKx VISx BASEx CRx 64 OC OWN HFR64 GOCR GOWN) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Lemma xpieceI own' M1 model1 LK1 Aw1 st1 qe1 cr1 (M3 : mem) kbb1 (Wp : Z -> Prop) :
  NMGx own' M1 model1 LK1 Aw1 st1 ESOx qe1 cr1 -> xinv M1 (PQMA.a_kb st1) kbb1 enx kx bx ex ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall a, Wp a -> sp - SCR <= a < sp) ->
  xinv M3 (PQMA.a_kb st1) kbb1 enx kx bx ex.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"; "Inst"] (Mh_0270_blobs2.kr_b_431 ())). Qed.

(* [comment removed for export] *)
Lemma ndest_adv lv0 c : NEMA.ndest (lv0 ++ [adv c]) = NEMA.ndest (lv0 ++ [c]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"; "Inst"] (Mh_0270_blobs2.kr_b_432 ())). Qed.

(* [comment removed for export] *)
Lemma FIN M5 model5 LK5 Aw5 st5 cr5 kbb5 (fx5 : FPState) R5 :
  NMx M5 model5 LK5 Aw5 st5 ESOx QEx cr5 -> REGSA R5 -> xinv M5 (PQMA.a_kb st5) kbb5 enx kx bx ex ->
  PQMA.nlv st5 = PQMA.nlv sa -> PQMA.kbsize st5 <= PQMA.kbsize sa + DK -> PQMA.kbsize st5 + NESK.sk_z kx <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st5) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb51b8 M5 model5) K.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"; "Inst"] (Mh_0270_blobs2.kr_b_433 ())). Qed.

(* [comment removed for export] *)
Lemma ADV M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  NMx M1 model1 LK1 Aw1 st1 ESOx QEx cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 enx kx bx ex -> PQMA.a_lv st1 = lv0 ++ [c] ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 <= PQMA.kbsize sa + DK -> PQMA.kbsize st1 + NESK.sk_z kx <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st1) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5140 M1 model1) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Inst"] (Mh_0270_blobs2.kr_b_434 ())). Qed.

(* [comment removed for export] *)
Lemma JMP (isv : bool) model1 kbb1 lv0 c (fx1 : FPState) R1 :
  NMx Mx model1 LKx Awx sax ESOx QEx crx -> regl IXA vals R1 -> xinv Mx (PQMA.a_kb sax) kbb1 enx kx bx ex -> PQMA.a_lv sax = lv0 ++ [c] ->
  PQMA.nlv sax = PQMA.nlv sa -> PQMA.kbsize sax <= PQMA.kbsize sa + DK -> PQMA.kbsize sax + NESK.sk_z kx <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv sax) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if isv then 0xb4fec else 0xb5044) Mx model1) K.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"; "Inst"] (Mh_0270_blobs2.kr_b_435 ())). Qed.
End Inst.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma EK0 : L5SAR.ek L ar LBX FF sp SCR WA M M.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_436 ())). Qed.
Lemma DK0 : L5SAR.dk L ar LBX FF sp SCR M M.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_437 ())). Qed.
Lemma CK0 : PMSP.credit_keep cr cr (PM.credit_add (POT sa) QE0) (PM.credit_add (POT sa) QE0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_438 ())). Qed.
Lemma XNN0 : 0 <= fst X0 /\ 0 <= snd X0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_439 ())). Qed.
Lemma XGE0 : PMSP.credit_le X0 X0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_440 ())). Qed.
Lemma EST0 : NEM.en_n en = NEM.en_n en /\ NEM.en_depth en = NEM.en_depth en /\ (bf = true -> bf = true) /\ (ef = true -> ef = true) /\ (bf = bf \/ tg = NEM.TAG_ENANO).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_441 ())). Qed.
Local Notation "'IE0' f" := (f D M model LK Aw cr sa en k bf ef X0 HH XNN0 AM ENT FRM AA OACC AOK VIS BASE SKA ENK CR EK0 DK0 (PQAKRA.model_rt_refl model) (incl_refl Aw) (incl_refl LK) (incl_refl D) CK0 XGE0 EST0)
  (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma eslotA_famC (c : credit) pc h args pre step :
  0 <= fst c /\ 0 <= snd c ->
  (forall Dy, NECSA.eslot_specA RSEGS AD AQ AAD AE L ar (HIk Dy) (NESKA.PMEA L) pc h args pre step) ->
  NECSA.eslot_specF RSEGS AD AQ AAD AE L ar HIk (NESKA.PMEA L) (fun _ _ _ _ => c) pc h args pre step.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_442 ())). Qed.

(* [comment removed for export] *)
Lemma ne8_oa : oa + 80 <> spc + 8.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_443 ())). Qed.
Lemma rchain_nil (M1 : mem) : HAR.rchain L ar M1 spc (oa + 80) [].
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_444 ())). Qed.

(* [comment removed for export] *)
Lemma AFTERCALL (isv : bool) D4 M4 model4 LK4 Aw4 cr4 en4 k4 (b4 e4 : bool) X4 lv0 c (fx4 : FPState) R4 :
  incl D D4 ->
  PQAKSNN.n_memG L ar (HIk D4) M model LBX FF LK Aw cr sp oa ov osk oec sa QE0 OWN M4 model4 LK4 Aw4 sa (NECS.eown en4 k4) (PM.credit_add (EPOT en4 k4) X4) cr4 ->
  xinv M4 (PQMA.a_kb sa) kbb en4 k4 b4 e4 ->
  0 <= fst X4 /\ 0 <= snd X4 -> PMSP.credit_le (tspE tg VSRA D4 []) X4 ->
  NEM.en_n en4 = NEM.en_n en /\ NEM.en_depth en4 = NEM.en_depth en /\ (bf = true -> b4 = true) /\ (ef = true -> e4 = true) /\ (b4 = bf \/ tg = NEM.TAG_ENANO) ->
  NESK.sk_z k4 <= NESK.sk_z k + DPHI ->
  REGSA R4 -> PQMA.a_lv sa = lv0 ++ [c] ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 (if isv then 0xb4fec else 0xb5044) M4 model4) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_445 ())). Qed.

(* [comment removed for export] *)
Definition EARG : NECS.eargs := NECS.EA tg 0 n vbs.

(* [comment removed for export] *)
Lemma DEST (eo1 : bool) M1 model1 LK1 Aw1 cr1 lv0 c (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 sa ESO QE0 cr1 -> REGSD R1 -> XV M1 -> xinv M1 (PQMA.a_kb sa) kbb en k bf ef -> PQMA.a_lv sa = lv0 ++ [c] ->
  PQMA.lv_t c = 0 -> PQMA.lv_eo c = (if eo1 then 1 else 0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb4e78 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_446 ())). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma xcallN (w : bool) M1 model1 LK1 Aw1 st1 qe1 cr1 (M4 : mem) (hc : Z) kbb1 kb4 kbb4 :
  NMG OWN M1 model1 LK1 Aw1 st1 ESO qe1 cr1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> 0 <= hc ->
  L5CA.ahpres L ar ((s_rest w st1 ++ ESO) ++ LBX) FF spc (PMSPA.pm_scr hc) [(oa + s_off w, 24)] M1 M4 ->
  (if w then kb4 = PQMA.a_kb st1 /\ kbb4 = kbb1 else NEM.kcontent RSEGS M4 (oa + PQMA.AOFF_KB) kb4 kbb4 /\ utf8_valid kbb4 = true) ->
  xinv M4 kb4 kbb4 en k bf ef.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_447 ())). Qed.

(* [comment removed for export] *)
Lemma NPUSH (ix : list nat) M1 model1 LK1 Aw1 st1 cr1 kbb1 (fx1 fx2 : FPState) R1 R2 (pc0 ra ch : Z) (M2v : mem) :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> XV M1 ->
  msteps RSEGS (st fx1 R1 pc0 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 0xf4640 M2v) -> mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall i, 0 <= i < 2 ^ 64 -> M2v (Z_to_bv 64 i) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 i)) ->
  regl ix vals R2 -> subl [2; 3; 4]%nat ix = true -> subl ix L5SAR.cs_all = true ->
  getr R2 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R2 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R2 (reg 11) = Z_to_bv 64 ch -> 0 <= ch < 128 ->
  PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + DK ->
  (forall (fx6 : FPState) R6 (M6 : mem) model6 LK6 Aw6 x' g' cr6,
      NM M6 model6 LK6 Aw6 (s_set false st1 x' g') ESO QE0 cr6 -> PM.vs_size x' = PQMA.kbsize st1 + 1 -> regl ix vals R6 ->
      xinv M6 x' (kbb1 ++ [ch]) en k bf ef -> XV M6 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 ra M6 model6) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_448 ())). Qed.

(* [comment removed for export] *)
Lemma ADV0 M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> PQMA.a_lv st1 = lv0 ++ [c] ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 <= PQMA.kbsize sa + DK -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5140 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_449 ())). Qed.

(* [comment removed for export] *)
Lemma CQV M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> XV M1 -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + DK ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb50b4 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_450 ())). Qed.
(* [comment removed for export] *)
Lemma COLON M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> XV M1 -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + DK ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5134 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_451 ())). Qed.
(* [comment removed for export] *)
Lemma CQK M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> XV M1 -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 2 <= PQMA.kbsize sa + DK ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5128 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_452 ())). Qed.

(* [comment removed for export] *)
Lemma div2_2 m : (2 * m) / 2 = m.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_453 ())). Qed.
(* [comment removed for export] *)
Lemma INS_CALL (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 (ra v11 : Z) :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> XV M1 ->
  ra = (if arm then 0xb50b4 else 0xb5128) ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 v11 -> getr R1 (reg 12) = Z_to_bv 64 d ->
  getr R1 (reg 13) = Z_to_bv 64 (d + n) -> getr R1 (reg 14) = Z_to_bv 64 n ->
  v11 = PM.vs_data (oa + 48) (PQMA.a_kb st1) + PM.vs_size (PQMA.a_kb st1) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + n + (if arm then 1 else 2) <= PQMA.kbsize sa + DK ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xbe330 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_454 ())). Qed.

Lemma INS2 (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> XV M1 ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + n + (if arm then 1 else 2) <= PQMA.kbsize sa + DK ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if arm then 0xb4f10 else 0xb4f78) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_455 ())). Qed.

(* [comment removed for export] *)
Lemma QUOTE (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 st1 ESO QE0 cr1 -> regl (if arm then IXB else IXA) vals R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> XV M1 ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + n + (if arm then 2 else 3) <= PQMA.kbsize sa + DK ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if arm then 0xb4f04 else 0xb4f68) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_456 ())). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma DISP1 M1 model1 LK1 Aw1 cr1 (fx1 : FPState) R1 :
  NM M1 model1 LK1 Aw1 sa ESO QE0 cr1 -> REGSD R1 -> xinv M1 (PQMA.a_kb sa) kbb en k bf ef -> XV M1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb4e78 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_457 ())). Qed.

(* [comment removed for export] *)
Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb4e30 M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_458 ())). Qed.
End Run.


(* [comment removed for export] *)
Theorem string_ok : PNVA.v_string_specF RSEGS AD AQ AAD AE L ar HIk tspV.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdVs ()) ["WithHeap"] (Mh_0270_blobs2.kr_b_459 ())). Qed.

End WithHeap.
End PQAAVS.


End PnAAdVs.
From Stdlib Require ZArith List Lia Bool FunctionalExtensionality. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.
Module PnABegArr.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0009. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKOwner OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObjA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnRunNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKRunA1N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228.PnABegArrP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0009.Na0_code_rc6364_c6368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnABegArr () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2lec69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA3ownC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvc69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA5ocellC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic3and01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7add_0_rC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subK47Corelib7Numbers7BinNums1Z03C46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z9div_add_lC56Stdlib6ZArith6BinInt1Z8mul_commC46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C45stdpp9bitvector;definitions5bv_eqK45stdpp9bitvector;definitions2bv01I47Corelib7Numbers7BinNums1N00K47Corelib4Init5Logic4True01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA9own_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA8sp_factsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN6m_memGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN9ctx_factsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN9obj_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA4mownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN5binvGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5p_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8src_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA6W_mrunC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_parserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3o_pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA4o_isC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3o_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3o_vC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA6o_sinkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ;qa_off_vrefC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA4o_ecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8mgrow_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6p_moreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6p_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7p_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_tbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA4PMEAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8sink_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_visitorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02567PnAKRun5PQAKR7fb_mod8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC69OSSVerify5KrLib7Mh_02567PnAKRun5PQAKR9zeros_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA8div8_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9u8_at_visC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u32_at_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u64_at_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK;img_shz_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8mrun_finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:mparser_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6iss_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092;PnQStaticsA5PQSTA7err_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ec_stateAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_sbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_skC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5p_stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7mvec_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_bbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4PgV84PGV85v8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM9nullis_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM=src_fields_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7enc_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lvec_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA4annAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4mpst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4strm00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA2H6C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA3HFRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4GOCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4GOWNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5PSIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7OFF_SRCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8OFF_MAXDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6OFF_TBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6OFF_BBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7OFF_STKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_KBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_DVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9AOFF_DESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8AOFF_KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_LVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA6vfactsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctAmrestrict_visibleC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4REGSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARBpreserved_by_indexC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC47Corelib4Init5Logic8eq_transI47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3cplC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4acctC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5oacctC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6eboundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3balC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKObjA16PQAKOA7set_fldC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA6minv_dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA6mpush1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6unreadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA9room_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8pot_runAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4ownvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA7bvu_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP9qbaD_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallc69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA8fin_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8mrun_preC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA:mprog_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN9mk_pieceGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA;mrun_post_dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKRunA1N7PQAKRAN6mk_retC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP7KS_qbaDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rc6364_c63687W_d3244C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rc6364_c63687F_d3244C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0009ENa0_code_rc6364_c63687D_d3244C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_qcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_deC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6sr_remC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_vp_issC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_strbufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_classic_impC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM4sm_gC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_egC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_iss_iosC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7iosb_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5CHUNKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA7ly_costC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_b_linC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;pot_mparserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7pot_aeAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8TSRES_MEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA7PMEA_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA@sink_potA_nonnegC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C69OSSVerify5KrLib7Mh_01028NemModel3NEM:pot_estackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA7spa_potC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA7hv_costC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_off_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_off_isC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKObjA16PQAKOA?pot_rest_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKObjA16PQAKOAApot_vstack_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:pot_vstackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9pot_textMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_bgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4PgV84PGV86pot_v8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6adebitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKObjA16PQAKOA7set_vecC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9pow_add_rC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_tgC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4mpst01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6mstate00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3PSZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP:qbaB0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKObjA16PQAKOA:set_fld_idC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0228:PnABegArrP6PQABAP8KS_qbaB0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA9frame_okMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA;margs_beginC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA7ba_typeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7oacct_dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ>qa_begin_arrayC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA<mstack_shapeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7ms_modeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;mode_bottomC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9mode_contC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9mstate_okC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4MAINC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA4ERRXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA@begin_array_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6acct_dC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7ms_rootC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA7BEGIN_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02709PnABegArr5PQABA3r13C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op206". Local Ltac lia := L5FastLia.plia.

Module PQABA.
Import L5A L5SAR.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AQ := PnLayoutQA.QADDR_A.
Abbreviation mown := PNRNA.mown.
Abbreviation AE := NemLayoutA.NEADDR_A.
Abbreviation bvu x := (bv_unsigned x).
(* [comment removed for export] *)
Definition MODE : Z := 2.

(* [comment removed for export] *)
Definition own (E : Z) (R : bvmap 5 word) (M : mem) : Prop :=
  L5.u64_at RSEGS M (E - 8) (bvu (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bvu (getr R (reg 8)))
  /\ L5.u64_at RSEGS M (E - 24) (bvu (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bvu (getr R (reg 18)))
  /\ L5.u64_at RSEGS M (E - 40) (bvu (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bvu (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (E - 56) (bvu (getr R (reg 21))).
Definition ocell (E : Z) (a : Z) : Prop := E - 56 <= a < E.
Lemma own_agree E R M1 M1' : 0 <= E - 56 -> E <= 2 ^ 64 ->
  own E R M1 -> (forall a, ocell E a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own E R M1'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) [] (Mh_0270_blobs2.kr_b_460 ())). Qed.
Lemma div8_off o c : o mod 8 = 0 -> 0 <= c -> (o + c) / 8 = o / 8 + c / 8.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) [] (Mh_0270_blobs2.kr_b_461 ())). Qed.
Lemma r13 : (13%bv : bv 5) = Z_to_bv 5 (Z.of_nat 13).
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) [] (Mh_0270_blobs2.kr_b_462 ())). Qed.
Lemma bvu_rng (x : word) : 0 <= bv_unsigned x < 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) [] (Mh_0270_blobs2.kr_b_463 ())). Qed.
Lemma credit_keep_trans c0 c1 c2 p0 p1 p2 : PMSP.credit_keep c0 c1 p0 p1 -> PMSP.credit_keep c1 c2 p1 p2 -> PMSP.credit_keep c0 c2 p0 p2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) [] (Mh_0270_blobs2.kr_b_464 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (IL : icpt_layout).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Hypothesis GSS : PNRNA.get_size_spec RSEGS AD AQ AAD AE L ar HI.
Hypothesis MKE : PQRAa.make_ec_spec L ar HI.
Hypothesis PSH : PQSAXQ.push_cont_spec RSEGS AD L ar HI 0xd4dc8.
Hypothesis VBA : PNVA.v_begin_array_spec RSEGS AD AQ AAD AE L ar HI.

Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (sp r fb cat n : Z) (s : PQMA.mpst) (sa : NEMA.aest) (str : PM.vstr) (sm : PM.strm) (e eb : bool) (t : Z).
Local Notation spc := (sp - 80).
Local Notation op := (fb + 592).
Local Notation oa := (fb + 992).
Local Notation oec := (fb + 1232).
Hypothesis HH : ri_inv HI (mown s sa ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 9.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM 9 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PQRA.frame_okM FF fb.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 op.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 oa.
Hypothesis A13 : getr R (reg 13) = Z_to_bv 64 oec.
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 t.
Hypothesis Ht : PQRA.ba_type t.
Hypothesis ACD : PQMA.acct_d 4 n s (NEMA.ae_a sa) sm.
Hypothesis OACCT8 : NEMA.oacct_d 8 n s sa sm.
Hypothesis RPRE : PNRNA.mrun_pre RSEGS AD AQ AAD AE L ar M fb s sa str sm e eb cat n.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis INV : PQRA.minv_d 0 s.
Hypothesis CRED : PMSP.credit_le (PM.credit_add (PNRNA.pot_runA L ar s sa) (PMSPA.scA L PNRNA.TSRES_ME)) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PQMA.mpst) (st' : NEMA.aest)
          (sm' : PM.strm) (e' b' : bool) (cr' : credit),
      regs_preserved R R' ->
      PNRNA.mrun_post_d RSEGS AD AQ AAD AE L ar 0 PNRNA.mprog_push R' M' fb s s' sa st' str sm sm' e e' eb b' cat n ->
      L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 9) (PNRNA.W_mrun AD AQ AE fb) M M' ->
      PMSP.credit_keep cr cr' (PNRNA.pot_runA L ar s sa) (PNRNA.pot_runA L ar s' st') ->
      model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (mown s' st' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Local Notation OWN := (own sp R).
Local Notation OC := (ocell sp).
Local Notation MG := (PQAKRAN.m_memG L ar HI M model LBX FF LK Aw sp fb cat s str sm e eb 9).
Local Notation MM := (MG OWN).
Local Notation TT := (fun _ : mem => True).

Lemma H6 : 1 <= 9 <= 16.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_465 ())). Qed.
Lemma HFR : 16 <= 80 <= 2048 /\ 80 mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_466 ())). Qed.
Lemma sp_facts : 140735332487248 <= sp /\ sp <= 140737488355328 /\ sp mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0 /\ ahl_ceil ar + 4096 + 30720 <= sp.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_467 ())). Qed.

(* [comment removed for export] *)
Local Notation KIT f := (f L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e eb 9 HH AM K0 ENT FRM FRS FOK RPRE INCS H6 80 OC OWN HFR).
Lemma GOCR : forall a, OC a -> sp - 80 <= a < sp.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_468 ())). Qed.
Lemma GOWN : forall M1 M1' : mem, OWN M1 -> (forall a, OC a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> OWN M1'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_469 ())). Qed.

(* [comment removed for export] *)
Lemma vfacts own' M1 model1 LK1 Aw1 s1 sa1 sm1 e1 cr1 b1 :
  MG own' M1 model1 LK1 Aw1 s1 sa1 sm1 e1 cr1 b1 ->
  (L5.img_clear (mrestrict (ahid Aw1 model1) M1) 65536 1409024 /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) 1440376 2147450880)
  /\ (L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) spc 80 /\ forall a n0, spc <= a -> a + n0 <= sp -> avis (ahid Aw1 model1) a n0)
  /\ (7036928 <= op <= 140737488354928 /\ op mod 8 = 0 /\ (2147446784 + 17592186048512 <= op \/ op + 400 <= 2147446784) /\ (spc + 80 <= op \/ op + 400 <= spc))
  /\ (7036928 <= oa <= 140737488355232 /\ oa mod 8 = 0 /\ (2147446784 + 17592186048512 <= oa \/ oa + 96 <= 2147446784))
  /\ (forall off, 0 <= off < 504 -> L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((op + off) / 8) + 2147450880) 1)
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) ((oa / 8) + 2147450880) 1
  /\ (L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (op + 8) (PQMA.p_more s1) /\ L5.u32_at RSEGS (mrestrict (ahid Aw1 model1) M1) (op + 12) (PQMA.p_depth s1)
      /\ L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (op + 16) 0 /\ L5.u32_at RSEGS (mrestrict (ahid Aw1 model1) M1) (op + 320) 1024
      /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) oa 1379720)
  /\ (forall a n0, op <= a -> a + n0 <= op + 504 -> 0 <= n0 -> L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) a n0)
  /\ (forall a g, 160416 <= a -> a + 8 * g <= 1381664 -> a mod 8 = 0 -> 0 < g -> L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (a / 8 + 2147450880) g).
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_470 ())). Qed.

(* [comment removed for export] *)
Definition REGS (Rx : bvmap 5 word) : Prop :=
  getr Rx (reg 2) = Z_to_bv 64 spc /\ getr Rx (reg 8) = Z_to_bv 64 oec /\ getr Rx (reg 9) = Z_to_bv 64 op /\ getr Rx (reg 18) = Z_to_bv 64 oa
  /\ getr Rx (reg 20) = Z_to_bv 64 2147450880
  /\ (forall j, In j [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr Rx (reg j) = getr R (reg j)).
Ltac regs_keep KS Q :=
  let Q2 := fresh in let Q8 := fresh in let Q9 := fresh in let Q18 := fresh in let Q20 := fresh in let QK := fresh in
  destruct Q as (Q2 & Q8 & Q9 & Q18 & Q20 & QK);
  split; [rewrite (KS 2%nat) by inl; exact Q2|]; split; [rewrite (KS 8%nat) by inl; exact Q8|]; split; [rewrite (KS 9%nat) by inl; exact Q9|];
  split; [rewrite (KS 18%nat) by inl; exact Q18|]; split; [rewrite (KS 20%nat) by inl; exact Q20|];
  intros j Hj; rewrite <- (QK j Hj); destruct Hj as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; apply KS; inl.
Ltac regs_pres RP Q :=
  let Q2 := fresh in let Q8 := fresh in let Q9 := fresh in let Q18 := fresh in let Q20 := fresh in let QK := fresh in
  destruct Q as (Q2 & Q8 & Q9 & Q18 & Q20 & QK);
  split; [rewrite (L5SAR.cs_of_preserved _ _ 2%nat RP ltac:(inl)); exact Q2|]; split; [rewrite (L5SAR.cs_of_preserved _ _ 8%nat RP ltac:(inl)); exact Q8|];
  split; [rewrite (L5SAR.cs_of_preserved _ _ 9%nat RP ltac:(inl)); exact Q9|]; split; [rewrite (L5SAR.cs_of_preserved _ _ 18%nat RP ltac:(inl)); exact Q18|];
  split; [rewrite (L5SAR.cs_of_preserved _ _ 20%nat RP ltac:(inl)); exact Q20|];
  intros j Hj; rewrite <- (QK j Hj); destruct Hj as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; apply (L5SAR.cs_of_preserved _ _ _ RP); inl.

(* [comment removed for export] *)
Lemma ownv M1 model1 LK1 Aw1 s1 sa1 sm1 e1 cr1 b1 : MM M1 model1 LK1 Aw1 s1 sa1 sm1 e1 cr1 b1 -> OWN (mrestrict (ahid Aw1 model1) M1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_471 ())). Qed.

(* [comment removed for export] *)
Lemma fin_regs (R5 R9 : bvmap 5 word) (KS : list nat) :
  REGS R5 -> (forall x, In x KS -> getr R9 (reg x) = getr R5 (reg x)) -> (forall j, In j [3; 4; 22; 23; 24; 25; 26; 27]%nat -> In j KS) ->
  getr R9 (reg 2) = Z_to_bv 64 sp -> getr R9 (reg 8) = Z_to_bv 64 (bvu (getr R (reg 8))) -> getr R9 (reg 9) = Z_to_bv 64 (bvu (getr R (reg 9))) ->
  getr R9 (reg 18) = Z_to_bv 64 (bvu (getr R (reg 18))) -> getr R9 (reg 19) = Z_to_bv 64 (bvu (getr R (reg 19))) ->
  getr R9 (reg 20) = Z_to_bv 64 (bvu (getr R (reg 20))) -> getr R9 (reg 21) = Z_to_bv 64 (bvu (getr R (reg 21))) ->
  regs_preserved R R9.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_472 ())). Qed.

(* [comment removed for export] *)
Lemma FIN_D M5 model5 LK5 Aw5 s5 sa5 sm5 e5 cr5 (fx5 : FPState) R5 :
  MM M5 model5 LK5 Aw5 s5 sa5 sm5 e5 cr5 eb -> REGS R5 ->
  getr R5 (reg 19) = Z_to_bv 64 (op + 8) -> getr R5 (reg 21) = Z_to_bv 64 (((op + 8) / 8) + 2147450880) ->
  PQMA.cpl s5 (NEMA.ae_a sa5) -> PQMA.acct n s5 (NEMA.ae_a sa5) sm5 -> NEMA.oacct n s5 sa5 sm5 -> (eb = false -> NEMA.ebound sa5 /\ NEMA.bal sa5) ->
  PQRA.minv_d 0 (PQAKOA.set_fld s5 1 (PQMA.p_depth s5)) -> PQRA.mpush1 s s5 ->
  PM.unread (PQMA.p_src s5) sm5 <= PM.unread (PQMA.p_src s) sm -> PQRA.room_keep s s5 sm sm5 ->
  PMSP.credit_keep cr cr5 (PNRNA.pot_runA L ar s sa) (PNRNA.pot_runA L ar s5 sa5) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xd3248 M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_473 ())). Qed.

Lemma UNR0 : 0 <= PM.unread (PQMA.p_src s) sm.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_474 ())). Qed.
(* [comment removed for export] *)
Lemma hv_cost : HeapIface.hl_k_per_malloc (PMSPA.HV L ar) = 8 /\ HeapIface.hl_b_overhead (PMSPA.HV L ar) = 2 ^ 21.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_475 ())). Qed.
Lemma ck_slot cr4 cr5 s4 sa4 sa5 :
  PMSP.credit_keep cr cr4 (PNRNA.pot_runA L ar s sa) (PNRNA.pot_runA L ar s4 sa4) ->
  PMSP.credit_keep cr4 cr5 (NEMA.pot_aeA L ar sa4) (NEMA.pot_aeA L ar sa5) ->
  PMSP.credit_keep cr cr5 (PNRNA.pot_runA L ar s sa) (PNRNA.pot_runA L ar s4 sa5).
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_476 ())). Qed.
Lemma cle_of_keep cr4 s4 sa4 :
  PMSP.credit_keep cr cr4 (PNRNA.pot_runA L ar s sa) (PNRNA.pot_runA L ar s4 sa4) ->
  PMSP.credit_le (PM.credit_add (PNRNA.pot_runA L ar s4 sa4) (PMSPA.scA L PNRNA.TSRES_ME)) cr4.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_477 ())). Qed.
(* [comment removed for export] *)
Lemma pot_ae_nonneg Mx ov osk st :
  NEMA.enc_atA RSEGS AE L ar Mx ov osk (NEMA.ae_e st) -> NESKA.sink_atA RSEGS L ar (NESKA.PMEA L) Mx osk (NEMA.ae_s st) ->
  0 <= fst (PMSPA.scA L (NEM.pot_estack (PMSPA.HV L ar) (NEM.en_k (NEMA.ae_e st)))) /\ 0 <= snd (PMSPA.scA L (NEM.pot_estack (PMSPA.HV L ar) (NEM.en_k (NEMA.ae_e st))))
  /\ 0 <= fst (NESKA.spa_pot (NESKA.PMEA L) (NESK.sk_c (NEMA.ae_s st))) /\ 0 <= snd (NESKA.spa_pot (NESKA.PMEA L) (NESK.sk_c (NEMA.ae_s st))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_478 ())). Qed.
(* [comment removed for export] *)
Lemma pot_aeA_le_run M5 model5 LK5 Aw5 s5 sa5 sm5 e5 cr5 b5 :
  MM M5 model5 LK5 Aw5 s5 sa5 sm5 e5 cr5 b5 -> PMSP.credit_le (PM.credit_add (PNRNA.pot_runA L ar s5 sa5) (PMSPA.scA L PNRNA.TSRES_ME)) cr5 ->
  PMSP.credit_le (NEMA.pot_aeA L ar sa5) cr5.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_479 ())). Qed.

(* [comment removed for export] *)
Lemma SLOT M4 model4 LK4 Aw4 s4 sm4 e4 cr4 (fx4 : FPState) R4 len gsb :
  MM M4 model4 LK4 Aw4 s4 sa sm4 e4 cr4 eb -> REGS R4 ->
  getr R4 (reg 19) = Z_to_bv 64 (op + 8) -> getr R4 (reg 21) = Z_to_bv 64 (((op + 8) / 8) + 2147450880) ->
  L5.u64_at RSEGS M4 (sp - 64) len -> 0 <= len < 2 ^ 64 -> PNRNA.gs_class t len gsb ->
  Z.of_nat (length (PQMA.p_stk s4)) = NEMA.nlv sa + 1 -> NEMA.nlv sa <= PQMA.MAX_DEPTH ->
  PM.unread (PQMA.p_src s4) sm4 <= PM.unread (PQMA.p_src s) sm - gsb ->
  PQRA.minv_d 0 (PQAKOA.set_fld s4 1 (PQMA.p_depth s4)) -> PQRA.mpush1 s s4 -> PQRA.room_keep s s4 sm sm4 ->
  PMSP.credit_keep cr cr4 (PNRNA.pot_runA L ar s sa) (PNRNA.pot_runA L ar s4 sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xd3204 M4 model4) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_480 ())). Qed.

(* [comment removed for export] *)
Lemma ck_push cr3 s3 b' k' stk' :
  0 <= PQMA.p_sk s3 -> k' = PQMA.p_sk s3 + 1 ->
  PMSP.credit_keep cr cr3 (PNRNA.pot_runA L ar s sa) (PNRNA.pot_runA L ar s3 sa) ->
  PMSP.credit_keep cr (adebit L cr3 (PQMA.PSZ * 2 ^ k')) (PNRNA.pot_runA L ar s sa) (PNRNA.pot_runA L ar (PQAKOA.set_vec s3 b' k' stk') sa).
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_481 ())). Qed.

(* [comment removed for export] *)
Lemma PUSH M3 model3 LK3 Aw3 s3 sm3 e3 cr3 (fx3 : FPState) R3 len gsb :
  MM M3 model3 LK3 Aw3 s3 sa sm3 e3 cr3 eb -> REGS R3 ->
  PQRA.minv_d 1 s3 -> PQMA.p_stk s3 = PQMA.p_stk s -> Z.of_nat (length (PQMA.p_stk s)) <= 1024 ->
  getr R3 (reg 10) = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 -> PNRNA.gs_class t len gsb ->
  PM.unread (PQMA.p_src s3) sm3 <= PM.unread (PQMA.p_src s) sm - gsb -> PQRA.room_keep s s3 sm sm3 ->
  PMSP.credit_keep cr cr3 (PNRNA.pot_runA L ar s sa) (PNRNA.pot_runA L ar s3 sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xd31cc M3 model3) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_482 ())). Qed.

(* [comment removed for export] *)
Lemma GSERR M3 model3 LK3 Aw3 s3 sa3 sm3 e3 cr3 (fx3 : FPState) R3 :
  MM M3 model3 LK3 Aw3 s3 sa3 sm3 e3 cr3 true -> REGS R3 -> PQMA.p_more s3 = 0 ->
  PMSP.credit_keep cr cr3 (PNRNA.pot_runA L ar s sa) (PNRNA.pot_runA L ar s3 sa3) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xd31cc M3 model3) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_483 ())). Qed.

(* [comment removed for export] *)
Lemma own_of_vis (H : word -> bool) (M2v M3 : mem) :
  mrestrict H M3 = M2v -> (forall a n0, spc <= a -> a + n0 <= sp -> avis H a n0) ->
  L5.u64_at RSEGS M2v (sp - 56) (bvu (getr R (reg 21))) -> L5.u64_at RSEGS M2v (sp - 48) (bvu (getr R (reg 20))) -> L5.u64_at RSEGS M2v (sp - 40) (bvu (getr R (reg 19))) ->
  L5.u64_at RSEGS M2v (sp - 32) (bvu (getr R (reg 18))) -> L5.u64_at RSEGS M2v (sp - 24) (bvu (getr R (reg 9))) -> L5.u64_at RSEGS M2v (sp - 16) (bvu (getr R (reg 8))) ->
  L5.u64_at RSEGS M2v (sp - 8) (bvu (getr R (reg 1))) -> OWN M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_484 ())). Qed.

(* [comment removed for export] *)
Lemma ERRX (fx : FPState) : PQMA.p_depth s = 1024 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R (qa_begin_array AQ) M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_485 ())). Qed.

(* [comment removed for export] *)
Lemma MAIN (fx : FPState) : 0 <= PQMA.p_depth s <= 1023 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R (qa_begin_array AQ) M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_486 ())). Qed.
End Run.

Theorem begin_array_ok : PNRNA.begin_array_spec RSEGS AD AQ AAD AE L ar HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnABegArr ()) ["WithHeap"] (Mh_0270_blobs2.kr_b_487 ())). Qed.
End WithHeap.
End PQABA.

End PnABegArr.
Module PnAGetSize.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0235. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKOwner OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnRunNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAGetSizeP1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0235.PnAGetSizeP2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0235.PnAGetSizeP3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAGetSizeP4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016.Na0_code_rc6d9c_c6da0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAGetSize () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2lec69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS3ownC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS5ocellC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z6of_natC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z=mod_pos_boundI47Corelib4Init5Logic2or00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib6ZArith4Zdiv:Z_mod_multK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega:ZMicromega;ZArithProof01K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC46Stdlib5Lists4List2InI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN5m_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS4REGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8pot_runAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN9mk_pfactsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02567PnAKRun5PQAKR9zeros_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02567PnAKRun5PQAKR7fb_mod8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02567PnAKRun5PQAKR8div8_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP4:qgsE1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP47alignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO8set_moreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6p_moreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA6minv_dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5p_stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_bbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8gs_classC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5p_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6unreadC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN=mk_piece_moreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP48KS_qgsE1C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4mpst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4strm00C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS2H5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS5HSPCfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4PgV84PGV82v800C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP4:qgsE2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP48KS_qgsE2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP4:qgsE4_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP47PQAGSP48KS_qgsE4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC69OSSVerify5KrLib7Mh_0202<PnAGetSizeP17PQAGSP17alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP17PQAGSP19qgsB_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS4WALKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258PnAKRunN6PQAKRN8mk_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0202<PnAGetSizeP17PQAGSP17KS_qgsBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA7gs_typeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA4mownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA9frame_okMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8margs_gsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8mrun_preC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3o_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ;qa_get_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS6cls_ofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0270:PnAGetSize5PQAGS3RUNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA=get_size_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA9gs_post_dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA6W_mrunC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA4o_ecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA4GS_HC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnRunNA5PNRNA8TSRES_MEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAGS.
Import L5A L5SAR.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AQ := PnLayoutQA.QADDR_A.
Abbreviation mown := PNRNA.mown.
Abbreviation AE := NemLayoutA.NEADDR_A.
Abbreviation bvu x := (bv_unsigned x).

(* [comment removed for export] *)
Definition own (E : Z) (R : bvmap 5 word) (M : mem) : Prop :=
  L5.u64_at RSEGS M (E - 8) (bvu (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bvu (getr R (reg 8)))
  /\ L5.u64_at RSEGS M (E - 24) (bvu (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bvu (getr R (reg 18)))
  /\ L5.u64_at RSEGS M (E - 40) (bvu (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bvu (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (E - 56) (bvu (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bvu (getr R (reg 22)))
  /\ L5.u64_at RSEGS M (E - 72) (bvu (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bvu (getr R (reg 24)))
  /\ L5.u64_at RSEGS M (E - 88) (bvu (getr R (reg 25))).
Definition ocell (E : Z) (a : Z) : Prop := E - 88 <= a < E.
Lemma own_agree E R M1 M1' : 0 <= E - 88 -> E <= 2 ^ 64 ->
  own E R M1 -> (forall a, ocell E a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own E R M1'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAGetSize ()) [] (Mh_0270_blobs2.kr_b_488 ())). Qed.
Lemma cls_of sp : sp mod 16 = 0 -> exists cls, (cls = 0 \/ cls = 16) /\ (sp - cls) mod 32 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAGetSize ()) [] (Mh_0270_blobs2.kr_b_489 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Hypothesis SR : PQRAa.src_read_spec L ar HI.
Hypothesis MKE : PQRAa.make_ec_spec L ar HI.

Section Run.
Variables (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (V2 cls r fb cat n d : Z) (s : PQMA.mpst) (sa : NEMA.aest) (str : PM.vstr) (sm : PM.strm) (e b : bool) (t : Z).
Local Notation sp := (V2 + cls).
Local Notation spc := (V2 - 96).
Local Notation op := (fb + 592).
Local Notation oec := (fb + 1232).
Hypothesis Hcls : cls = 0 \/ cls = 16.
Hypothesis V32 : V2 mod 32 = 0.
Hypothesis Hd : 0 <= d <= 1.
Hypothesis HH : ri_inv HI (mown s sa ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 5.
Hypothesis FRM : PGSA.ffroomB PQRA.FCM 5 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PQRA.frame_okM FF fb.
Hypothesis A10 : getr R (reg 10) = Z_to_bv 64 op.
Hypothesis A12 : getr R (reg 12) = Z_to_bv 64 oec.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 t.
Hypothesis Ht : PQRA.gs_type t.
Hypothesis RPRE : PNRNA.mrun_pre RSEGS AD AQ AAD AE L ar M fb s sa str sm e b cat n.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis INV : PQRA.minv_d d s.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PQMA.mpst) (st' : NEMA.aest)
          (sm' : PM.strm) (e' b' : bool) (cr' : credit),
      regs_preserved R R' ->
      PNRNA.gs_post_d RSEGS AD AQ AAD AE L ar d t R' M' fb s s' sa st' str sm sm' e e' b b' cat n ->
      L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 5) (PNRNA.W_mrun AD AQ AE fb) M M' ->
      PMSP.credit_keep cr cr' (PNRNA.pot_runA L ar s sa) (PNRNA.pot_runA L ar s' st') ->
      model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (mown s' st' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Local Notation OWN := (own sp R).
Local Notation OC := (ocell sp).
Local Notation MM := (PQAKRN.m_mem L ar HI M model LBX FF LK Aw sp fb cat n s sa str sm e b 5 spc OWN 1).

Lemma sp_facts : 140735332487264 + 16 <= V2 /\ V2 + cls <= 140737488355328 /\ (V2 + cls) mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAGetSize ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_490 ())). Qed.

(* [comment removed for export] *)
Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : mem) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK Aw sp (PMSPA.pm_scr 5) spc (sp - 88) sp OC OWN F fl 1 LK2 M2 model2 cr (mown s sa).
Hypothesis APART : forall a n0 sp0 scr0, (forall i, 0 <= i < n0 -> aclient L ar (mown s sa ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n0 ->
         (a + n0 <= F \/ F + ff_bytes 1 <= a) /\ (a + n0 <= F / 8 + SB \/ F / 8 + SB + ff_bytes 1 / 8 <= a) /\ (a + n0 <= fl \/ fl + 1 <= a).
Local Notation MMF := (MM F).

(* [comment removed for export] *)
Definition REGS (Rx : bvmap 5 word) : Prop :=
  getr Rx (reg 2) = Z_to_bv 64 spc /\ getr Rx (reg 8) = Z_to_bv 64 sp /\ getr Rx (reg 18) = Z_to_bv 64 F /\ getr Rx (reg 20) = Z_to_bv 64 oec
  /\ getr Rx (reg 22) = Z_to_bv 64 ((F / 8) + 2147450880) /\ getr Rx (reg 23) = Z_to_bv 64 F /\ getr Rx (reg 24) = Z_to_bv 64 2147450880
  /\ (forall j, In j [3; 4; 26; 27]%nat -> getr Rx (reg j) = getr R (reg j)).
Lemma H5 : 1 <= 5 <= 16.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAGetSize ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_491 ())). Qed.
Lemma bvu_rng (x : word) : 0 <= bv_unsigned x < 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAGetSize ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_492 ())). Qed.
Lemma HSPCf : sp - 2048 <= spc /\ spc mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAGetSize ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_493 ())). Qed.

(* [comment removed for export] *)
Lemma FIN M5 model5 LK5 Aw5 s5 sm5 e5 b5 (fx5 : FPState) R5 :
  MMF M5 model5 LK5 Aw5 s5 sa sm5 e5 cr b5 -> REGS R5 -> PNRNA.pot_runA L ar s5 sa = PNRNA.pot_runA L ar s sa ->
  ( (b5 = true /\ PQMA.p_more s5 = 0)
    \/ (b5 = b /\ PQRA.minv_d d s5 /\ PQMA.p_stk s5 = PQMA.p_stk s /\ PQMA.p_bb s5 = PQMA.p_bb s
        /\ exists len gsb, 0 <= len < 2 ^ 64 /\ getr R5 (reg 10) = Z_to_bv 64 len /\ PNRNA.gs_class t len gsb /\ PM.unread (PQMA.p_src s5) sm5 <= PM.unread (PQMA.p_src s) sm - gsb) ) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xd3c08 M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_494 ())). Qed.
Ltac regs_keep KS Q :=
  let Q2 := fresh in let Q8 := fresh in let Q18 := fresh in let Q20 := fresh in let Q22 := fresh in let Q23 := fresh in let Q24 := fresh in let QK := fresh in
  destruct Q as (Q2 & Q8 & Q18 & Q20 & Q22 & Q23 & Q24 & QK);
  split; [rewrite (KS 2%nat) by inl; exact Q2|]; split; [rewrite (KS 8%nat) by inl; exact Q8|]; split; [rewrite (KS 18%nat) by inl; exact Q18|];
  split; [rewrite (KS 20%nat) by inl; exact Q20|]; split; [rewrite (KS 22%nat) by inl; exact Q22|]; split; [rewrite (KS 23%nat) by inl; exact Q23|];
  split; [rewrite (KS 24%nat) by inl; exact Q24|];
  intros j Hj; rewrite <- (QK j Hj); destruct Hj as [<-|[<-|[<-|[<-|[]]]]]; apply KS; inl.

(* [comment removed for export] *)
Ltac const_arm conc Vf :=
  lazymatch goal with LM : PQAKRN.m_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?M3 ?model3 _ ?Aw3 _ _ _ _ _ _, Q : REGS ?R3 |- srealizes _ _ (@PMSP.cfg _ ?fx3 ?R3 _ ?M3 ?model3) _ =>
    let P := fresh "P" in
    pose proof (LF2CBN( conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) Vf )) as P;
    pose proof Q as (?Q2 & _); pose proof sp_facts as (?SP1 & ?SP2 & _); pose proof Hcls as ?HC;
    L5SAR.feed P ltac:(first [assumption | unfold PQAGSP3.aligned; assumption | apply bvu_rng | lia]);
    let fx4 := fresh "fx4" in let R4 := fresh "R4" in let M4v := fresh "M4v" in
    destruct P as (fx4 & R4 & M4v & ?MG4 & _ & ?FRZ4 & ?MS4 & ?KS4 & ?A0 & _);
    eapply (PQAKRN.mk_piece L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e b 5 HH AM K0 ENT FRM FRS FOK RPRE INCS H5 spc (sp - 88) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf)
      with (W := fun _ => False); [exact LM| exact MS4| exact MG4| intros a Ha _; apply FRZ4; exact Ha| intros a []|];
    intros ?M5 ?model5 ?LM5 _ _ _ _;
    eapply FIN; [exact LM5| regs_keep KS4 Q| reflexivity|];
    right; split; [reflexivity|]; split; [exact INV|]; split; [reflexivity|]; split; [reflexivity|];
    exists (bvu (getr R4 (reg 10))), 0; split; [apply bvu_rng|]; split; [symmetry; apply Z_to_bv_bv_unsigned|]; split; [| lia];
    lazymatch type of A0 with
    | bv_unsigned _ = Z.land _ 15 => rewrite A0; change (Z.land t 15) with (Z.land t (Z.ones 4)); rewrite Z.land_ones by lia;
                                     pose proof (Z.mod_pos_bound t (2 ^ 4) ltac:(lia)) as MB; unfold PNRNA.gs_class; lia
    | _ = Z_to_bv 64 _ => rewrite A0; rewrite L5.unsigned_lit by lia; unfold PNRNA.gs_class; lia
    end
  end.

Lemma WALK_CONST M3 model3 LK3 Aw3 (fx3 : FPState) R3 :
  MMF M3 model3 LK3 Aw3 s sa sm e cr b -> REGS R3 -> getr R3 (reg 19) = Z_to_bv 64 op -> getr R3 (reg 21) = Z_to_bv 64 t ->
  getr R3 (reg 10) = Z_to_bv 64 (t - 196) -> getr R3 (reg 11) = Z_to_bv 64 27 ->
  (128 <= t <= 159) \/ (212 <= t <= 216) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xd3a1c M3 model3) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_495 ())). Qed.

Ltac regs_pres RP Q :=
  let Q2 := fresh in let Q8 := fresh in let Q18 := fresh in let Q20 := fresh in let Q22 := fresh in let Q23 := fresh in let Q24 := fresh in let QK := fresh in
  destruct Q as (Q2 & Q8 & Q18 & Q20 & Q22 & Q23 & Q24 & QK);
  split; [rewrite (L5SAR.cs_of_preserved _ _ 2%nat RP ltac:(inl)); exact Q2|]; split; [rewrite (L5SAR.cs_of_preserved _ _ 8%nat RP ltac:(inl)); exact Q8|];
  split; [rewrite (L5SAR.cs_of_preserved _ _ 18%nat RP ltac:(inl)); exact Q18|]; split; [rewrite (L5SAR.cs_of_preserved _ _ 20%nat RP ltac:(inl)); exact Q20|];
  split; [rewrite (L5SAR.cs_of_preserved _ _ 22%nat RP ltac:(inl)); exact Q22|]; split; [rewrite (L5SAR.cs_of_preserved _ _ 23%nat RP ltac:(inl)); exact Q23|];
  split; [rewrite (L5SAR.cs_of_preserved _ _ 24%nat RP ltac:(inl)); exact Q24|];
  intros j Hj; rewrite <- (QK j Hj); destruct Hj as [<-|[<-|[<-|[<-|[]]]]]; apply (L5SAR.cs_of_preserved _ _ _ RP); inl.

Ltac pf LM :=
  destruct (PQAKRN.mk_pfacts L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e b 5 HH AM K0 ENT FRM FRS FOK RPRE INCS H5 spc (sp - 88) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf
              _ _ _ _ _ _ _ _ _ _ LM) as (IMG & (PF1 & PF2 & PF3 & PF4 & _) & (FD & FW & FSW & FLU & FLW) & _ & (SW & _) & (FB1 & FB2 & FB3 & FB4) & (ZOP & WOP & _) & _ & (AVSH & _));
  change (ff_bytes 1) with 128 in *; change (128 / 8) with 16 in *.


(* [comment removed for export] *)
Ltac err_body Econc gaddr :=
  intros LM7 Q7 Q19'' POT;
  pose proof sp_facts as (SP1 & SP2 & SP3 & Hr1 & Hr2); pose proof Hcls as HC;
  lazymatch goal with |- srealizes _ _ (@PMSP.cfg _ ?fx7 ?R7 _ ?M7 ?model7) _ => lazymatch type of LM7 with PQAKRN.m_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?Aw7 _ _ _ _ _ _ =>
    pose proof Q7 as (Q2_7 & _ & _ & _ & Q22_7 & _ & Q24_7 & _);
    destruct (PQAKRN.mk_pfacts L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e b 5 HH AM K0 ENT FRM FRS FOK RPRE INCS H5 spc (sp - 88) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf
              _ _ _ _ _ _ _ _ _ _ LM7) as (IMG & (PF1 & PF2 & PF3 & PF4 & _) & (FD & FW & FSW & FLU & FLW) & _ & (SW & _) & (FB1 & FB2 & FB3 & FB4) & (ZOP & WOP & _) & _ & (AVSH & _));
    change (ff_bytes 1) with 128 in *; change (128 / 8) with 16 in *;
    assert (Z8 : L5KA.zeros_at (mrestrict (ahid Aw7 model7) M7) ((fb + 592 + 8) / 8 + 2147450880) 1)
      by (rewrite (PQAKR.div8_add (fb + 592) 8 (PQAKR.fb_mod8 fb 592 FB3 eq_refl) eq_refl); apply (PQAKR.zeros_sub _ _ 63 _ 1 ZOP); [change (8 / 8) with 1; lia| change (8 / 8) with 1; lia]);
    assert (W8 : L5.writable RSEGS (mrestrict (ahid Aw7 model7) M7) (fb + 592 + 8) 1) by (apply (L5.writable_sub RSEGS _ (fb + 592) 504); [exact WOP| lia| lia]);
    pose proof (PQAKR.fb_mod8 fb 592 FB3 eq_refl) as O8;
    pose proof (LF2CBN( Econc fx7 R7 (mrestrict (ahid Aw7 model7) M7) (fun j : nat => match j with 2%nat => spc | 33%nat => op | 50%nat => F | _ => 0 end) )) as P2;
    L5SAR.feed P2 ltac:(first [assumption | unfold PQAGSP4.aligned; assumption | lia]);
    destruct P2 as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & _ & _ & _ & _ & U80);
    eapply (PQAKRN.mk_piece_more L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e b 5 HH AM K0 ENT FRM FRS FOK RPRE INCS H5 spc (sp - 88) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf)
      with (W := fun a => a = fb + 600 \/ F / 8 + gaddr <= a < F / 8 + gaddr + 1);
      [exact LM7| exact MS8| exact MG8| intros a Ha N; apply FRZ8; [exact Ha| intros X; apply N; left; lia| intros X; apply N; right; lia]
      | intros a [Wa|Wa]; (split; [unfold ocell; lia|]); [do 3 right; exact Wa| right; right; left; change (ff_bytes 1 / 8) with 16; unfold SB; lia]
      | replace (fb + 600) with (fb + 592 + 8) by lia; exact U80|];
    intros M9 model9 LM9 _ _ _ _;
    eapply FIN; [exact LM9| regs_keep KS8 Q7| exact POT|];
    left; split; reflexivity
  end end.

(* [comment removed for export] *)
Ltac read_body Roconc Reconc ERR kv offv gaddr pcr pcm :=
  intros LM Q Q19 Q21 Q25 Q1 Q10 Q11 Q12 GC U8;
  pose proof sp_facts as (SP1 & SP2 & SP3 & Hr1 & Hr2); pose proof Hcls as HC;
  pose proof ENT as (_ & _ & _ & Rgp & Rtp & _); rewrite L5K.rl3 in Rgp; rewrite L5K.rl4 in Rtp;
  pose proof Q as (Q2 & Q8 & Q18 & Q20 & Q22 & Q23 & Q24 & QK);
  eapply (PQAKRN.mk_call_read L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e b 5 HH AM K0 ENT FRM FRS FOK RPRE INCS H5 spc (sp - 88) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf)
     with (ra := pcr) (off := offv) (kk := kv) (v := kv);
  [exact SR| lia| exact LM| exact Q1| split; [lia| reflexivity]| exact Q2| rewrite (QK 3%nat) by inl; exact Rgp| rewrite (QK 4%nat) by inl; exact Rtp| exact Q10| exact Q11| exact Q12
  | lia| change (ff_bytes 1) with 128; lia| reflexivity| right; lia | match goal with |- L5.u8_at _ _ ?a _ => replace a with (F / 8 + gaddr) by (cbn; lia) end; exact U8 |];
  intros fx5 R5 M5 model5 LK5 Aw5 src5 sm5 dd RP5 Y10 Hdd UNR RM1 RM0 DEFd QC5 LM5 KF1 KF2;
  assert (Q5 : REGS R5) by (regs_pres RP5 Q);
  assert (Q19' : getr R5 (reg 19) = Z_to_bv 64 op) by (rewrite (L5SAR.cs_of_preserved _ _ 19%nat RP5 ltac:(inl)); exact Q19);
  assert (Q21' : getr R5 (reg 21) = Z_to_bv 64 (F + offv)) by (rewrite (L5SAR.cs_of_preserved _ _ 21%nat RP5 ltac:(inl)); exact Q21);
  assert (Q25' : getr R5 (reg 25) = Z_to_bv 64 kv) by (rewrite (L5SAR.cs_of_preserved _ _ 25%nat RP5 ltac:(inl)); exact Q25);
  pose proof Q5 as (Q2' & Q8' & Q18' & Q20' & Q22' & Q23' & Q24' & QK');
  destruct (PQAKRN.mk_pfacts L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e b 5 HH AM K0 ENT FRM FRS FOK RPRE INCS H5 spc (sp - 88) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf
              _ _ _ _ _ _ _ _ _ _ LM5) as (IMG & (PF1 & PF2 & PF3 & PF4 & _) & (FD & FW & FSW & FLU & FLW) & _ & (SW & _) & (FB1 & FB2 & FB3 & FB4) & (ZOP & WOP & _) & _ & (AVSH & _));
    change (ff_bytes 1) with 128 in *; change (128 / 8) with 16 in *;
  destruct (Z.eq_dec dd kv) as [Edd|Ndd];
  [ subst dd;
    let P := fresh "P" in
    pose proof (LF2CBN( Roconc fx5 R5 (mrestrict (ahid Aw5 model5) M5) (fun j : nat => match j with 2%nat => spc | 50%nat => F | _ => 0 end) )) as P;
    L5SAR.feed P ltac:(first [assumption | unfold PQAGSP4.aligned; assumption | lia]);
    destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & _);
    eapply (PQAKRN.mk_piece L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e b 5 HH AM K0 ENT FRM FRS FOK RPRE INCS H5 spc (sp - 88) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf)
      with (W := fun a => F / 8 + gaddr <= a < F / 8 + gaddr + 1);
      [exact LM5| exact MS6| exact MG6| intros a Ha N; apply FRZ6; [exact Ha| intros X; apply N; lia]
      | intros a Wa; split; [unfold ocell; lia| right; right; change (ff_bytes 1 / 8) with 16; unfold SB; lia]|];
    intros M7 model7 LM7 _ _ _ _;
    eapply FIN; [exact LM7| regs_keep KS6 Q5| reflexivity|];
    right; split; [reflexivity|]; split; [exact INV|]; split; [reflexivity|]; split; [reflexivity|];
    exists (bvu (getr R6 (reg 10))), kv; split; [apply bvu_rng|]; split; [symmetry; apply Z_to_bv_bv_unsigned|]; split; [apply GC; apply bvu_rng| cbn [PQMA.with_src PQMA.p_src]; lia]
  | try (assert (Edd0 : dd = 0) by lia; rewrite Edd0 in Y10);
    let P := fresh "P" in
    pose proof (LF2CBN( Reconc fx5 R5 (mrestrict (ahid Aw5 model5) M5) (fun j : nat => match j with 2%nat => spc | 34%nat => oec | 37%nat => dd | _ => 0 end) )) as P;
    L5SAR.feed P ltac:(first [assumption | unfold PQAGSP4.aligned; assumption | lia]);
    destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & Z1 & Z10 & Z11);
    eapply (PQAKRN.mk_piece L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e b 5 HH AM K0 ENT FRM FRS FOK RPRE INCS H5 spc (sp - 88) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf)
      with (W := fun _ => False); [exact LM5| exact MS6| exact MG6| intros a Ha _; apply FRZ6; exact Ha| intros a []|];
    intros M6 model6 LM6 _ _ _ _;
    assert (Q6 : REGS R6) by (regs_keep KS6 Q5);
    pose proof Q6 as (Q2'' & _ & _ & _ & _ & _ & _ & QK'');
    eapply (PQAKRN.mk_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e b 5 HH AM K0 ENT FRM FRS FOK RPRE INCS H5 spc (sp - 88) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf)
      with (ra := pcm) (v := 1);
      [exact MKE| lia| exact LM6| exact Z1| split; [lia| reflexivity]| exact Q2''| rewrite (QK'' 3%nat) by inl; exact Rgp| rewrite (QK'' 4%nat) by inl; exact Rtp| exact Z10| exact Z11| lia|];
    intros fx7 R7 M7 model7 LK7 Aw7 RP7 LM7 _ _;
    assert (Q7 : REGS R7) by (regs_pres RP7 Q6);
    assert (Q19'' : getr R7 (reg 19) = Z_to_bv 64 op) by (rewrite (L5SAR.cs_of_preserved _ _ 19%nat RP7 ltac:(inl)); rewrite (KS6 19%nat) by inl; exact Q19');
    eapply ERR; [exact LM7| exact Q7| exact Q19''| reflexivity] ].


Lemma ERR1 M7 model7 LK7 Aw7 s5 sm5 (fx7 : FPState) R7 :
  MMF M7 model7 LK7 Aw7 s5 sa sm5 true cr true -> REGS R7 -> getr R7 (reg 19) = Z_to_bv 64 op ->
  PNRNA.pot_runA L ar s5 sa = PNRNA.pot_runA L ar s sa ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx7 R7 867188 M7 model7) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAGetSize ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_496 ())). Qed.
Lemma READ1 M4 model4 LK4 Aw4 (fx4 : FPState) R4 :
  MMF M4 model4 LK4 Aw4 s sa sm e cr b -> REGS R4 -> getr R4 (reg 19) = Z_to_bv 64 op -> getr R4 (reg 21) = Z_to_bv 64 (F + 32) -> getr R4 (reg 25) = Z_to_bv 64 1 ->
  getr R4 (reg 1) = Z_to_bv 64 867060 -> getr R4 (reg 10) = Z_to_bv 64 (fb + 592 + 24) -> getr R4 (reg 11) = Z_to_bv 64 (F + 32) -> getr R4 (reg 12) = Z_to_bv 64 1 ->
  (forall len, 0 <= len < 2 ^ 64 -> PNRNA.gs_class t len 1) -> L5.u8_at RSEGS M4 (F / 8 + 2147450884) 1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 (pa_src_read AD) M4 model4) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_497 ())). Qed.

Lemma ERR2 M7 model7 LK7 Aw7 s5 sm5 (fx7 : FPState) R7 :
  MMF M7 model7 LK7 Aw7 s5 sa sm5 true cr true -> REGS R7 -> getr R7 (reg 19) = Z_to_bv 64 op ->
  PNRNA.pot_runA L ar s5 sa = PNRNA.pot_runA L ar s sa ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx7 R7 867136 M7 model7) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAGetSize ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_498 ())). Qed.
Lemma READ2 M4 model4 LK4 Aw4 (fx4 : FPState) R4 :
  MMF M4 model4 LK4 Aw4 s sa sm e cr b -> REGS R4 -> getr R4 (reg 19) = Z_to_bv 64 op -> getr R4 (reg 21) = Z_to_bv 64 (F + 48) -> getr R4 (reg 25) = Z_to_bv 64 2 ->
  getr R4 (reg 1) = Z_to_bv 64 866908 -> getr R4 (reg 10) = Z_to_bv 64 (fb + 592 + 24) -> getr R4 (reg 11) = Z_to_bv 64 (F + 48) -> getr R4 (reg 12) = Z_to_bv 64 2 ->
  (forall len, 0 <= len < 2 ^ 64 -> PNRNA.gs_class t len 2) -> L5.u8_at RSEGS M4 (F / 8 + 2147450886) 2 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 (pa_src_read AD) M4 model4) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_499 ())). Qed.
Lemma ERR4 M7 model7 LK7 Aw7 s5 sm5 (fx7 : FPState) R7 :
  MMF M7 model7 LK7 Aw7 s5 sa sm5 true cr true -> REGS R7 -> getr R7 (reg 19) = Z_to_bv 64 op ->
  PNRNA.pot_runA L ar s5 sa = PNRNA.pot_runA L ar s sa ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx7 R7 867084 M7 model7) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAGetSize ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_500 ())). Qed.
Lemma READ4 M4 model4 LK4 Aw4 (fx4 : FPState) R4 :
  MMF M4 model4 LK4 Aw4 s sa sm e cr b -> REGS R4 -> getr R4 (reg 19) = Z_to_bv 64 op -> getr R4 (reg 21) = Z_to_bv 64 (F + 64) -> getr R4 (reg 25) = Z_to_bv 64 4 ->
  getr R4 (reg 1) = Z_to_bv 64 866968 -> getr R4 (reg 10) = Z_to_bv 64 (fb + 592 + 24) -> getr R4 (reg 11) = Z_to_bv 64 (F + 64) -> getr R4 (reg 12) = Z_to_bv 64 4 ->
  (forall len, 0 <= len < 2 ^ 64 -> PNRNA.gs_class t len 4) -> L5.u8_at RSEGS M4 (F / 8 + 2147450888) 4 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 (pa_src_read AD) M4 model4) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_501 ())). Qed.

(* [comment removed for export] *)
Ltac t_read Tconc READk kv gaddr :=
  lazymatch goal with LM : PQAKRN.m_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?M3 ?model3 _ ?Aw3 _ _ _ _ _ _, Q : REGS ?R3 |- srealizes _ _ (@PMSP.cfg _ ?fx3 ?R3 _ ?M3 ?model3) _ =>
    let P := fresh "P" in
    pose proof (LF2CBN( Tconc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j : nat => match j with 2%nat => spc | 33%nat => op | 50%nat => F | _ => 0 end) )) as P;
    pose proof Q as (Q2 & _ & _ & _ & Q22 & Q23 & _); pose proof sp_facts as (SP1 & SP2 & _); pose proof Hcls as HC;
    destruct (PQAKRN.mk_pfacts L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e b 5 HH AM K0 ENT FRM FRS FOK RPRE INCS H5 spc (sp - 88) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf
              _ _ _ _ _ _ _ _ _ _ LM) as (IMG & (PF1 & PF2 & PF3 & PF4 & _) & (FD & FW & FSW & FLU & FLW) & _ & _ & (FB1 & FB2 & _) & _ & _ & (AVSH & _));
    change (ff_bytes 1) with 128 in *; change (128 / 8) with 16 in *;
    L5SAR.feed P ltac:(first [assumption | unfold PQAGSP2.aligned; assumption | unfold PQAGSP3.aligned; assumption | lia]);
    destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & T1 & T10 & T11 & T12 & T21 & T25 & U8v);
    eapply (PQAKRN.mk_piece L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e b 5 HH AM K0 ENT FRM FRS FOK RPRE INCS H5 spc (sp - 88) sp OC OWN 1 F fl LK2 M2 model2 G APART HSPCf)
      with (W := fun a => F / 8 + gaddr <= a < F / 8 + gaddr + 1);
      [exact LM| exact MS4| exact MG4| intros a Ha N; apply FRZ4; [exact Ha| intros X; apply N; lia]
      | intros a Wa; split; [unfold ocell; lia| right; right; change (ff_bytes 1 / 8) with 16; unfold SB; lia]|];
    intros M5 model5 LM5 HID5 VIS5 _ _;
    eapply READk; [exact LM5| regs_keep KS4 Q| rewrite (KS4 19%nat) by inl; assumption| exact T21| exact T25| exact T1| exact T10| exact T11| exact T12| intros len Hlen; unfold PNRNA.gs_class; lia|];
    apply (proj1 (L5A.u8_at_vis (ahid Aw3 model3) M5 (F / 8 + gaddr) kv (L5A.avis_sub (ahid Aw3 model3) (F / 8 + SB) 16 (F / 8 + gaddr) 1 AVSH ltac:(unfold SB; lia) ltac:(unfold SB; lia)) ltac:(lia) ltac:(lia)));
    rewrite VIS5; exact U8v
  end.

Lemma WALK M3 model3 LK3 Aw3 (fx3 : FPState) R3 :
  MMF M3 model3 LK3 Aw3 s sa sm e cr b -> REGS R3 -> getr R3 (reg 19) = Z_to_bv 64 op -> getr R3 (reg 21) = Z_to_bv 64 t ->
  getr R3 (reg 10) = Z_to_bv 64 (t - 196) -> getr R3 (reg 11) = Z_to_bv 64 27 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xd3a1c M3 model3) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_502 ())). Qed.

(* [comment removed for export] *)
Lemma SETUP Mx modelx LKx Awx (fx2 : FPState) R2 :
  MMF Mx modelx LKx Awx s sa sm e cr b ->
  getr R2 (reg 2) = Z_to_bv 64 spc -> getr R2 (reg 8) = Z_to_bv 64 sp -> getr R2 (reg 9) = Z_to_bv 64 spc -> getr R2 (reg 10) = Z_to_bv 64 F ->
  getr R2 (reg 19) = Z_to_bv 64 op -> getr R2 (reg 20) = Z_to_bv 64 oec -> getr R2 (reg 21) = Z_to_bv 64 t -> getr R2 (reg 24) = Z_to_bv 64 2147450880 ->
  (forall j, In j [3; 4; 26; 27]%nat -> getr R2 (reg j) = getr R (reg j)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0xd3974 Mx modelx) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAGetSize ()) ["WithHeap"; "Run"; "Frame"] (Mh_0270_blobs2.kr_b_503 ())). Qed.

End Frame.

(* [comment removed for export] *)
Ltac enter_tac Aconc aligned_unf fxv MVv :=
  pose proof (LF2CBN( Aconc fxv R MVv (fun j : nat => match j with 2%nat => V2 | 33%nat => op | 34%nat => oec | 35%nat => t | _ => 0 end) )) as P;
  L5SAR.feed P ltac:(first [assumption | aligned_unf; assumption | lia]);
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T19 & T20 & T21 & T24 & C25 & C24 & C23 & C22 & C21 & C20 & C19 & C18 & C9 & C8 & C1 & C0);
  apply (PQAKRN.mk_enter L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat n s sa str sm e b 5 HH AM K0 ENT FRM FRS FOK RPRE INCS H5 spc (sp - 88) sp OC OWN 1 fxv fx1 R1 0xd38b4 866596 M1v);
  [ right; left; reflexivity | lia | exact (proj2 HSPCf) | lia | lia | lia | intros a Ha; unfold ocell in Ha; lia
  | intros Ma Mb OW AG; apply (own_agree sp R Ma Mb ltac:(lia) ltac:(lia) OW AG)
  | exact MS1 | exact MG1 | intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; lia]
  | intros M1 VIS1 AV; unfold own;
    repeat match goal with |- _ /\ _ => split end;
    (match goal with |- L5.u64_at _ _ ?a0 ?v0 => apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a0 v0 (AV a0 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))) end; rewrite VIS1;
     match goal with |- L5.u64_at _ _ ?a _ => first [ replace a with (V2 - 8) by lia; assumption | replace a with (V2 - 16) by lia; assumption | replace a with (V2 - 24) by lia; assumption
        | replace a with (V2 - 32) by lia; assumption | replace a with (V2 - 40) by lia; assumption | replace a with (V2 - 48) by lia; assumption | replace a with (V2 - 56) by lia; assumption
        | replace a with (V2 - 64) by lia; assumption | replace a with (V2 - 72) by lia; assumption | replace a with (V2 - 80) by lia; assumption | replace a with (V2 - 88) by lia; assumption
        | replace a with (V2 + 8) by lia; assumption | replace a with V2 by lia; assumption ] end)
  | exact T2 | apply KS1; inl | exact T1 | reflexivity | lia |];
  intros R2 M2 model2 F fl LK2 G APART LM2 G10 RP2 _;
  apply (SETUP F fl LK2 M2 model2 G APART M2 model2 LK2 Aw fx1 R2 LM2);
  [ rewrite (L5SAR.cs_of_preserved _ _ 2%nat RP2 ltac:(inl)); exact T2
  | rewrite (L5SAR.cs_of_preserved _ _ 8%nat RP2 ltac:(inl)); rewrite T8; f_equal; lia
  | rewrite (L5SAR.cs_of_preserved _ _ 9%nat RP2 ltac:(inl)); exact T9
  | exact G10
  | rewrite (L5SAR.cs_of_preserved _ _ 19%nat RP2 ltac:(inl)); exact T19
  | rewrite (L5SAR.cs_of_preserved _ _ 20%nat RP2 ltac:(inl)); exact T20
  | rewrite (L5SAR.cs_of_preserved _ _ 21%nat RP2 ltac:(inl)); exact T21
  | rewrite (L5SAR.cs_of_preserved _ _ 24%nat RP2 ltac:(inl)); exact T24
  | intros j Hj; destruct Hj as [<-|[<-|[<-|[<-|[]]]]]; (match goal with |- getr _ (reg ?j0) = _ => rewrite (L5SAR.cs_of_preserved R1 R2 j0 RP2 ltac:(inl)) end; apply KS1; inl) ].

Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xd3904 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"; "Run"] (Mh_0270_blobs2.kr_b_504 ())). Qed.

End Run.
Theorem get_size_ok : PNRNA.get_size_spec RSEGS AD AQ AAD AE L ar HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAGetSize ()) ["WithHeap"] (Mh_0270_blobs2.kr_b_505 ())). Qed.

End WithHeap.
End PQAGS.

End PnAGetSize.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0238. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0244.
Module PnARdDtor.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0238. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0244. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0009. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunHA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAIss1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnSpecsAXr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAEmbKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0238.PnAAnn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228.PnAAnnLv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0238.PnAAnnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0202.PnAVecDtor OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228.PnAVecDtorLv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0244.PnAVu8Dtor OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0228.PnARdDtorP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0009.Na0_code_rae6c4_ae6c8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnARdDtor () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_00909PmStatics4PMST3depC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS17dep_imgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive02C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib7Mh_00929PnStatics4PNST8dep_of_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA9ly_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_loC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib7Mh_00249PnLayoutA7NADDR_AC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C59OSSVerify5KrLib7Mh_00188PmLayout8pa_rw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A=aly_static_loC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib7Mh_02709PnARdDtor6PQARDD4dinvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3subC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA=aobj_of_aobjAC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4aobjC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8vis_packC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:aobj_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ<aior_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<asan_staticsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8aly_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A=statics_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC69OSSVerify5KrLib7Mh_02137PnStepA4PMKA>obj_shadow_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_canaryC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_00188PmLayout=pa_need_locksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_locale_lockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5ACimg_clear_mrestrictC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u64_at_visC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u32_at_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A<writable_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8avis_subC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9u8_at_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init5Logic4True00C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ff_capC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<ff_count_appC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARBnodup_of_map_app_rC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=ff_count_inclC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib5Lists4List2hdC69OSSVerify5KrLib7Mh_02138PnBrObjA5PNBOA5gspanC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201". Local Ltac lia := L5FastLia.plia.

Module PQARDD.
Import L5A L5SAR.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AQ := PnLayoutQA.QADDR_A.
Abbreviation bvu x := (bv_unsigned x).

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Lemma dep_std (op : Z) a : PMST.dep PMA.AD a -> 7036928 <= op ->
  hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside [(op, 504)] a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnARdDtor ()) ["WithHeap"] (Mh_0270_blobs2.kr_b_506 ())). Qed.
Lemma sro_std (op : Z) a : 65536 <= a < pa_rw_lo PMA.AD -> 7036928 <= op ->
  hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside [(op, 504)] a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnARdDtor ()) ["WithHeap"] (Mh_0270_blobs2.kr_b_507 ())). Qed.
Ltac a64 AG X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; lia| lia| lia| exact X].
Ltac a8 AG X Ms := apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; lia| lia| lia| exact X].

(* [comment removed for export] *)
Let ASH := PQAANN.ann_shrink_ok L ar C HI LY HIok EXT.
Let ADL := PQAANN.ann_delete_ok L ar C HI LY HIok EXT.
Let ASHL := PQAALN.ann_shrink_lv_ok L ar C HI LY HIok EXT.
Let ADLL := PQAALN.ann_delete_lv_ok L ar C HI LY HIok EXT.
Let ASH8 := PNAAV8.ann_shrink_v8_ok L ar C HI LY HIok EXT.
Let ADL8 := PNAAV8.ann_delete_v8_ok L ar C HI LY HIok EXT.
(* [comment removed for export] *)
Definition dinv (R : bvmap 5 word) (M : mem) (model : Model) (sp op : Z) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
                (LBc : list (Z * Z)) (LO : Z) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) : Prop :=
  ri_inv HI LBc FF LK' cr Aw' M' (vml_of model') /\ L5CA.amodel_ok Aw' model' /\ model_rt model model' /\ incl LK' LK /\ incl Aw Aw'
  /\ getr R' (reg 2) = Z_to_bv 64 (sp - 32) /\ getr R' (reg 8) = Z_to_bv 64 op /\ getr R' (reg 9) = Z_to_bv 64 2147450880
  /\ (forall k, In k [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg k) = getr R (reg k))
  /\ L5.u64_at RSEGS M' (sp - 8) (bvu (getr R (reg 1))) /\ L5.u64_at RSEGS M' (sp - 16) (bvu (getr R (reg 8))) /\ L5.u64_at RSEGS M' (sp - 24) (bvu (getr R (reg 9)))
  /\ L5SAR.ek L ar LBc FF sp 18432 [(op, 504)] M M' /\ L5SAR.dk L ar LBc FF sp 18432 M M'
  /\ L5CA.astk ar M' sp 18432 /\ shadow_zero M' (sp - 18432) 2304
  /\ PMSTA.base_okA RSEGS PMA.AD M' /\ PMSPA.accA M' op 504 /\ L5.defined M' op 496
  /\ (forall a, op + 8 <= a < op + LO -> ~ (op + 400 <= a < op + 408) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
(* [comment removed for export] *)
Lemma stage_facts R M model sp op FF LK Aw cr LBc LO R' M' model' LK' Aw' :
  dinv R M model sp op FF LK Aw cr LBc LO R' M' model' LK' Aw' -> PMSPA.aobjA FF op 504 -> op mod 8 = 0 ->
  (forall a n, ahl_ceil ar <= a -> a + n <= 2 ^ 64 -> avis (ahid Aw' model') a n)
  /\ (forall a n, 0 <= a -> a + n <= 7036928 -> avis (ahid Aw' model') a n)
  /\ avis (ahid Aw' model') op 504
  /\ L5KA.zeros_at (mrestrict (ahid Aw' model') M') (op / 8 + 2147450880) 63
  /\ L5.img_clear (mrestrict (ahid Aw' model') M') 65536 1409024
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw' model') M') 1440376 2147450880
  /\ L5.u32_at RSEGS (mrestrict (ahid Aw' model') M') 1440384 1
  /\ L5.writable RSEGS (mrestrict (ahid Aw' model') M') (sp - 32) 32
  /\ (forall a v, sp - 32 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M' a v -> L5.u64_at RSEGS (mrestrict (ahid Aw' model') M') a v)
  /\ (forall a n, op <= a -> a + n <= op + 496 -> 0 <= n -> L5.writable RSEGS (mrestrict (ahid Aw' model') M') a n)
  /\ (forall a v, op <= a -> a + 8 <= op + 504 -> L5.u64_at RSEGS M' a v -> L5.u64_at RSEGS (mrestrict (ahid Aw' model') M') a v)
  /\ (forall a v, op <= a -> a + 1 <= op + 504 -> L5.u8_at RSEGS M' a v -> L5.u8_at RSEGS (mrestrict (ahid Aw' model') M') a v).
Proof.
ltac2:(KReplay.run1 (kr_t_PnARdDtor ()) ["WithHeap"] (Mh_0270_blobs2.kr_b_508 ())). Qed.
Lemma ffroomB_lower FC h h' FF LK LK2 :
  PGSA.ffroomB FC h FF LK -> incl LK2 LK -> NoDup (map ff_addr (FF ++ LK2)) -> h' <= h -> PGSA.ffroomB FC h' FF LK2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnARdDtor ()) ["WithHeap"] (Mh_0270_blobs2.kr_b_509 ())). Qed.
Lemma gspan_S B m i : B mod 8 = 0 -> 0 <= m -> B <= i < B + PNBOA.gspan m -> in_shadow_of B m (S i).
Proof.
ltac2:(KReplay.run1 (kr_t_PnARdDtor ()) ["WithHeap"] (Mh_0270_blobs2.kr_b_510 ())). Qed.

Theorem reader_dtor_ok : PMA.opdel_spec L ar HI -> PMA.src_dtor_spec L ar HI -> PQRAa.reader_dtor_spec L ar HI.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0270 ()) ["WithHeap"] (Mh_0270_blobs2.kr_b_511 ())). Qed.

End WithHeap.
End PQARDD.

End PnARdDtor.
From Stdlib Require ZArith List Lia Bool. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0240.
Module PnARst.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0238. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0240. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0244. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0238.PnAAnnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0238.PnAAnn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAEmbR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0240.PnARstStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0244.PnARst1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0244.PnARst2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0244.PnARst3.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnARst () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA:opnew_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02447PnARst16PQARS14headC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02447PnARst26PQARS24midsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02447PnARst36PQARS34tailC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02388PnAAnnV86PNAAV8@ann_shrink_v8_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02386PnAAnn6PQAANN=ann_shrink_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02077PnAEmbR5PQAER<push_root_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0240;PnARstStmts6PQARSS?reset_of_stagesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PQARS.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.

Theorem reset_ok : PMA.opnew_spec L ar HI -> PQRAa.reset_spec L ar HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnARst ()) ["WithHeap"] (Mh_0270_blobs2.kr_b_512 ())). Qed.
End WithHeap.
End PQARS.

End PnARst.
