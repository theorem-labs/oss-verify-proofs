(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Mh_0207_blobs1 Mh_0207_blobs2.
(* [comment removed for export] *)
Set Warnings "-require-in-module".
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0169. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0207 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List9nth_errorC46Stdlib5Lists4List8map_consI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00C56Stdlib6ZArith6BinInt1Z3powK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04I46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega7EnvRing5PExpr07I46Stdlib9micromega7EnvRing5PExpr00C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3addK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC47Corelib4Init5Logic3notK46Stdlib9micromega6VarMap1t02C46Stdlib9micromega:ZMicromega=Zeval_formulaC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K46Stdlib9micromega:ZMicromega;ZArithProof02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3addC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE2<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z6of_natK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega6VarMap4findI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto7eval_bfK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega6VarMap1t03C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE23NX0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE29regs_out0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltc79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE26cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums8positive00K4ELinuxProcessSemantics5Riscv5Instr5aluop07I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K46Stdlib9micromega:ZMicromega;ZArithProof01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE25regs0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP8KS_azrE2C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP;KS_azrE2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF2<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP>u32_of_KWord4aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF29regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF26cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP8KS_azrF2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP;KS_azrF2_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_appC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclC46Stdlib5Lists4List8app_nth1C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~I46Stdlib9micromega7EnvRing3Pol00C56Stdlib5Arith8PeanoNat3Nat3eqbC59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8mvec_ownC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init3Nat3subC69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK4argpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK9blk_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRF6PQAERF5pow2kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA=aobj_of_aobjAC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4aobjC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:aobj_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK9arg_factsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8vis_packC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ<aior_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<asan_staticsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8aly_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A=statics_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5ACimg_clear_mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u64_at_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u32_at_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A<writable_visC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=astk_writableC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRF6PQAERF=stack_zeros12C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib7Mh_00368AsanAcctAmrestrict_visibleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA>obj_shadow_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8avis_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP:azrF1_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8aclientwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_rt_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A3cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ<aex_annotateC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ9ec_ann_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ:ec_ann_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ=annotate_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ:ann_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9astack_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRF6PQAERF:shadow_lowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK9ann_agreeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith6BinInt1Z7mod_addC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARAastack_ok_of_astkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ?model_rt_haltedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR>aclient_narrowC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<stack_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK?in_shadow_rangeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=astk_after_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRF6PQAERF6S_add8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRF6PQAERF7S_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK?stack_sh_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK8sh_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK?frame_sh_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA:accA_agreeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:obj_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK7arg_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK:arg_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRF6PQAERF4zsh1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS17vis_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=defined_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0024:PnAEmbKitQ6PQAEKQ4d24bC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib7Mh_0024:PnAEmbKitQ6PQAEKQ3d24C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK5sh_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK6sh_idxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS13bvuC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP:azrF2_concC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA5akeptC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_appbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK=own_notclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK@own_sh_notclientC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=aclient_casesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9ahpres_ofC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9ek_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK9base_keepC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARBpreserved_by_indexC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02147L5CoreB4L5CB<aacc_of_zeroC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesC69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO?mstate_at_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS17vis_u32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7ms_modeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6ms_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6ms_idxC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat8sub_diagC47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC46Stdlib5Lists4List8app_nth2C56Stdlib6ZArith4Znat5Nat2Z7inj_addC69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ>model_rt_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6apieceC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega;ZifyClasses6mkapp2C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7mvec_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9mstate_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP8KS_azrF1C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7ms_rootC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_geC59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3PSZC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA3EXTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rc2444_c24487W_cf38cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rc2444_c24487F_cf38cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rc2444_c24487D_cf38cC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204C46Stdlib5Lists4List8nil_consK59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP=word_of_zpolyC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE1<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP>u32_of_KWord4aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE19regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE16cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP8KS_azlE1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP;KS_azlE1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF29regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP8KS_azlF2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP;KS_azlF2_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lvec_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213:PnSpecsAXl6PQSAXL6lvl_eoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP:azlF1_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z9div_add_lc69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP:azlF2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO=alvl_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushF7PQALVPF6eo_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_tC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5lv_eoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lvec_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7alvl_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP8KS_azlF1C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lv_rootC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3LSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rb8880_b88847W_b873cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rb8880_b88847F_b873cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0014ENa0_code_rb8880_b88847D_b873cC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List9in_or_appC47Corelib9RelationsDRelation_Definitions8relationC47Corelib4Init5Logic3iffC59OSSVerify5KrLib7Mh_0089:HeapIfaceA>hl_asan_memcpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA:opnew_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_need_locksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_locale_lockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_rw_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6adebitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:acredit_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_canaryC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP:azlE0_concC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:astk_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8astk_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:shadow_blkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6afreshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_hiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:astk_afterC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK?arg_fresh_apartC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP:azlE1_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;aior_memcpyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<amemcpy_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:hl_scr_memC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z6to_natC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_memcpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A;aly_scr_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:aclient_00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP:azlE2_concC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indc69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP:azlE3_concC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR7rng_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic8iff_reflC59OSSVerify5KrLib7Mh_0089:HeapIfaceA9aclient_gC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=aclient_consbC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses3injc69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP8KS_azlE3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP8KS_azlE2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP8KS_azlE0C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA9OPNEW_SCRC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247?PnALvPushGStmts8PQALVPGS4gmidC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushG18PQALVPG17pow2k10C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushG18PQALVPG15pow2sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2:azlS0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2:azlS1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2:azlS2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2:azlS3_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2:azlS4_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2:azlS5_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2:azlS6_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2:azlS7_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2:azlS8_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2:azlS9_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2;azlS10_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z8add_commc69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP9azlG_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK;shadow_lowUC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP9azlH_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC46Stdlib9micromega;ZifyClasses6eq_iffC69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG8rdn_someC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAEmbKit5PNAEK7rdn_nthC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC69OSSVerify5KrLib7Mh_0247?PnALvPushGStmts8PQALVPGS9alvl_copyC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specc69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP7KS_azlHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP7KS_azlGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS0C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS6C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS7C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS9C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP29KS_azlS10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA:opdel_specC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP37alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbc69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3:azlI0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3:azlI1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3:azlI2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3:azlI3_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3:azlI4_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3:azlI5_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3:azlI6_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3:azlI7_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3:azlI8_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3:azlI9_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3;azlI10_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_mulc69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP9azlJ_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib7Mh_02137PnStepA4PMKAAastk_after_ahpresC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP9azlK_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP7KS_azlKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP7KS_azlJC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI6C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI7C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI9C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP39KS_azlI10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA9OPDEL_SCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP:azrE0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP:azrE1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP:azrE2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP:azrE3_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP8KS_azrE3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP8KS_azrE1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP8KS_azrE0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAl<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA?zeros_of_KZeroaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA>u32_of_KWord4aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA=u8_of_KWord1aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAl9regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAl6cells0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS09fill_specC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS09copy_specC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS08tls_specC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAl3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA8KS_qpcAlC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAl3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA;KS_qpcAl_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAh<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAh3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAh2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAh3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAh9regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAh6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAh5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAh3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA8KS_qpcAhC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAh3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA;KS_qpcAh_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA5PqpcB<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA5PqpcB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA5PqpcB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA5PqpcB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA5PqpcB9regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA5PqpcB6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA5PqpcB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA5PqpcB3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA7KS_qpcBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA5PqpcB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA:KS_qpcB_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA@locale_ctor_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS4costC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS2opC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_vp_issC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout:pa_vp_optsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA9frame_okMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS3preC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS5rmid1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS14sub8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z<divide_transC69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9u8_at_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS16d4cellC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtor16PQAPC14img1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtor16PQAPC14img2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA:qpcAl_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA:qpcAh_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA9wapp_consC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA;stksh_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST3depC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS17dep_imgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA9ly_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A=aly_static_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA=base_ok_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS1<loc_ok_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA?shadow_zero_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ff_capC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA7ffroomAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ff_rsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_classic_impC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9dk_calleeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout7pm_footC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS13brgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS1=base_ok_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA:acc_keepA'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA9qpcB_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS1;ffroom_inclC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_nullisC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout@pa_vp_nullis_iosC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS5rmidcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS9saves_nisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS6hcellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8dk_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA9u64_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS8saves_rdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS9saves_srcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_parserC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtor16PQAPC16vis_u8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02477PnAIss16PMAIS19vis_zerosC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF>zeros_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA9u32_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST6loc_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00929PnStatics4PNST8dep_of_jC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7NADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A@AS0_ALY_CELLS_D4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01508XIcptAs0=as0_icpt_fillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01508XIcptAs0=as0_icpt_copyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01508XIcptAs0<as0_icpt_tlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA:addrs_wf_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS3SCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnAPCtorKit6PQAPCK4fb16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnAPCtorKit6PQAPCK:frame_aobjC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS5rmid2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnAPCtorKit6PQAPCK6vfactsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnAPCtorKit6PQAPCK4svisC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP9qpcC_concC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?mem_eq_of_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnAPCtorKit6PQAPCK9mset_postC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnAPCtorKit6PQAPCK4fvisC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP9qpcD_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP9qpcE_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_nullbufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout?pa_errcat_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout?pa_syscat_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout;pa_loc_footC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_atexitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pm_initcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnAPCtorKit6PQAPCK5amsetC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9apiece_roC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcDC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5CHUNKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213:PnSpecsAXq6PQSAXQ=full_or_emptyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213:PnSpecsAXq6PQSAXQ>push_root_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS4kontC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnAPCtorKit6PQAPCK9rd_creditC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP9qpcF_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP9qpcG_concC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR5ek_tlC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR5dk_tlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP9qpcH_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213:PnSpecsAXq6PQSAXQ8arg_cellC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02147L5CoreB4L5CB8aacc_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG9zeros_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtor36PQAPC36shz_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213:PnSpecsAXq6PQSAXQ:cells_rootC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213:PnSpecsAXq6PQSAXQ6k_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213:PnSpecsAXq6PQSAXQ8push_outC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02147L5CoreB4L5CB;aacc_of_blkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP9qpcZ_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG;u8_of_zerosC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnAPCtorKit6PQAPCK?mparser_init_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnAPCtorKit6PQAPCK9ri_swap12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG<u64_of_zerosC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rc1d78_c1d7c7W_cecc0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rc1d78_c1d7c7F_cecc0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rc1d78_c1d7c7D_cecc0C1?~~~~~~~~~~~~~~~".
Module PnAEmbRP.
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0169. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0169.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAEmbRP () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP8KS_azrE0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP=word_of_zpolyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP;KS_azrE0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP8KS_azrE1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE1<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP>u32_of_KWord4aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP;KS_azrE1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP8KS_azrE2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP8KS_azrE3C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE33ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP;KS_azrE3_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrE36cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP8KS_azrF1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF16cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP;KS_azrF1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP6PazrF29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02078PnAEmbRP6PQAERP8KS_azrF2C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAERP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_001 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_002 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_003 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_004 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_005 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_006 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_007 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_008 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_009 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_010 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_011 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_012 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; byte_go.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
(* [comment removed for export] *)
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
(* [comment removed for export] *)
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          | |- L5KA.zeros_at _ ?a _ => lazymatch type of H with L5KA.zeros_at _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
(* [comment removed for export] *)
Local Ltac den_tac := first [reflexivity | lia | idtac].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.
(* [comment removed for export] *)
Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module PazrE0 := BndP_Na_045.LibSegNa_azrE0.
Definition KS_azrE0 : list nat := Eval vm_compute in (BG.kept_list 60 PazrE0.regs0 PazrE0.regs_out0).
Lemma KS_azrE0_ok : BG.kept_ok 60 PazrE0.regs0 PazrE0.regs_out0 KS_azrE0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_013 ())). Qed.
Lemma azrE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 65536 1409024 ->
  L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) ->
  L5.u64_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 16) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcf178 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azrE0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 850516
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 1
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 24
        /\ getr R' (reg 11) = Z_to_bv 64 32
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 848616
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_014 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrE1 := BndP_Na_045.LibSegNa_azrE1.
Definition KS_azrE1 : list nat := Eval vm_compute in (BG.kept_list 60 PazrE1.regs0 PazrE1.regs_out0).
Lemma KS_azrE1_ok : BG.kept_ok 60 PazrE1.regs0 PazrE1.regs_out0 KS_azrE1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_015 ())). Qed.
Lemma azrE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 1 -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 16) 0 ->
  7036928 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 ->
  L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 7036928 <= (V 35%nat) <= 140737488355324 ->
  aligned (V 35%nat) 4 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 35%nat) (V 39%nat) ->
  (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 2147483647 ->
  4096 <= (V 40%nat) <= 140737488355304 -> aligned (V 40%nat) 16 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450880) 3 ->
  L5.writable RSEGS M (V 40%nat) 24 -> (((V 2%nat) - 4096) + 4096 <= (V 40%nat) \/ (V 40%nat) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 40%nat) \/ (V 40%nat) + 24 <= (V 33%nat)) -> (65536 + 6971392 <= (V 40%nat) \/ (V 40%nat) + 24 <= 65536) ->
  ((V 34%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 24 <= (V 34%nat)) -> ((V 35%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 24 <= (V 35%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 848616 ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcfa54 M) (st fx' R' 0x7ebbc M')
        /\ (forall x, In x KS_azrE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 849964
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 18) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 848788
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 8) (V 39%nat)
        /\ L5.u32_at RSEGS M' (V 40%nat) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_016 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrE2 := BndP_Na_045.LibSegNa_azrE2.
Definition KS_azrE2 : list nat := Eval vm_compute in (BG.kept_list 60 PazrE2.regs0 PazrE2.regs_out0).
Lemma KS_azrE2_ok : BG.kept_ok 60 PazrE2.regs0 PazrE2.regs_out0 KS_azrE2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_017 ())). Qed.
Lemma azrE2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) 0 ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) 0 -> 4096 <= (V 40%nat) <= 140737488355304 -> aligned (V 40%nat) 16 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 40%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 40%nat) 24 -> (((V 2%nat) - 4096) + 4096 <= (V 40%nat) \/ (V 40%nat) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 40%nat) \/ (V 40%nat) + 24 <= (V 33%nat)) ->
  (65536 + 6971392 <= (V 40%nat) \/ (V 40%nat) + 24 <= 65536) -> ((V 34%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 24 <= (V 34%nat)) -> ((V 35%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 24 <= (V 35%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 848788 ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 24) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcf82c M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azrE2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 850644
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 24)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 24)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 24)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 848788
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 0
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) [] (Mh_0207_blobs1.kr_b_018 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrE3 := BndP_Na_045.LibSegNa_azrE3.
Definition KS_azrE3 : list nat := Eval vm_compute in (BG.kept_list 60 PazrE3.regs0 PazrE3.regs_out0).
Lemma KS_azrE3_ok : BG.kept_ok 60 PazrE3.regs0 PazrE3.regs_out0 KS_azrE3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_019 ())). Qed.
Lemma azrE3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 40%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 40%nat) + 24) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 40%nat) + 24) -> 4096 <= (V 40%nat) <= 140737488355280 -> aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 848788 ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 96) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 88) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcfad4 M) (st fx' R' 0xcf3dc M')
        /\ (forall x, In x KS_azrE3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 ((((V 2%nat) - 88) / 8) + 2147450880)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 24)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_020 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrF1 := BndP_Na_045.LibSegNa_azrF1.
Definition KS_azrF1 : list nat := Eval vm_compute in (BG.kept_list 60 PazrF1.regs0 PazrF1.regs_out0).
Lemma KS_azrF1_ok : BG.kept_ok 60 PazrF1.regs0 PazrF1.regs_out0 KS_azrF1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_021 ())). Qed.
Lemma azrF1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 41%nat) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 0 <= (V 37%nat) <= 49128 -> aligned (V 37%nat) 8 ->
  4120 <= (V 41%nat) <= 140737488355327 -> 24 <= ((V 41%nat) - ((V 36%nat) + (V 37%nat))) <= 49152 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcf178 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azrF1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 849780
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + (V 37%nat)) + 24)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 848372
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_022 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrF2 := BndP_Na_045.LibSegNa_azrF2.
Definition KS_azrF2 : list nat := Eval vm_compute in (BG.kept_list 60 PazrF2.regs0 PazrF2.regs_out0).
Lemma KS_azrF2_ok : BG.kept_ok 60 PazrF2.regs0 PazrF2.regs_out0 KS_azrF2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRP ()) [] (Mh_0207_blobs1.kr_b_023 ())). Qed.
Lemma azrF2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + (V 37%nat)) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (V 37%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) (V 41%nat) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 7036928 <= (V 34%nat) <= 140737488355324 ->
  aligned (V 34%nat) 4 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) ->
  (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 7036928 <= (V 35%nat) <= 140737488355324 -> aligned (V 35%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 848372 ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> 0 <= (V 37%nat) <= 49128 -> aligned (V 37%nat) 8 -> 4120 <= (V 41%nat) <= 140737488355327 ->
  24 <= ((V 41%nat) - ((V 36%nat) + (V 37%nat))) <= 49152 -> L5KA.zeros_at M ((((V 36%nat) + (V 37%nat)) / 8) + 2147450880) 3 -> L5.writable RSEGS M ((V 36%nat) + (V 37%nat)) 24 -> (2147446784 + 17592186048512 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 24 <= 2147446784) ->
  (65536 + 6971392 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 24 <= 65536) -> 4096 <= ((V 36%nat) + (V 37%nat)) <= 140737488355304 -> (((V 2%nat) - 4096) + 4096 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 24 <= (V 33%nat)) ->
  ((V 34%nat) + 4 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 24 <= (V 34%nat)) -> ((V 35%nat) + 4 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 24 <= (V 35%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 36%nat) + (V 37%nat)) + 0) <= bv_unsigned a < (((V 36%nat) + (V 37%nat)) + 0) + 24) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 36%nat) + (V 37%nat)) + 0) <= i < (((V 36%nat) + (V 37%nat)) + 0) + 24) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcf774 M) (st fx' R' 0xcf3dc M')
        /\ (forall x, In x KS_azrF2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 36%nat) + (V 37%nat)) + 24)
        /\ L5.u64_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 16) 0
        /\ L5.u64_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 8) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 36%nat) + (V 37%nat)) (V 38%nat)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) [] (Mh_0207_blobs1.kr_b_024 ())). Qed.
(* [comment removed for export] *)

End PQAERP.

End PnAEmbRP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed. From Stdlib Require ZArith List Lia Bool FunctionalExtensionality. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.
Module PnAEmbRF.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnAEmbKitQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAIss1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAEmbKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAEmbRP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012.Na0_code_rc2444_c2448.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5CoreB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAEmbRF () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula07I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr07I47Corelib4Init5Logic4True00C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9u8_at_visC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01".
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PQAERF.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Lemma stack_zeros12 M sp : shadow_zero M (sp - 12288) 1536 -> sp mod 16 = 0 -> L5KA.zeros_at M (sp / 8 + 2147450368) 512.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRF ()) [] (Mh_0207_blobs1.kr_b_025 ())). Qed.
Lemma zsh1 M p : byte_at M (S p) 0 -> L5KA.zeros_at M (p / 8 + 2147450880) 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRF ()) [] (Mh_0207_blobs1.kr_b_026 ())). Qed.
Lemma shadow_low b c j : 0 <= b -> b + c <= 2 ^ 47 -> 0 <= j < c / 8 -> 2147450880 <= S b + j < 2147450880 + 2 ^ 44.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRF ()) [] (Mh_0207_blobs1.kr_b_027 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma vis_u8 H M1 M1v a v : mrestrict H M1 = M1v -> L5A.avis H a 1 -> 0 <= a -> a < 2 ^ 63 -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRF ()) [] (Mh_0207_blobs1.kr_b_028 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma S_range x : 0 <= x < 2 ^ 47 -> 2147450880 <= S x < 2147450880 + 2 ^ 44.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRF ()) [] (Mh_0207_blobs1.kr_b_029 ())). Qed.
Lemma S_add8 a j : S a + j = S (a + 8 * j).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRF ()) [] (Mh_0207_blobs1.kr_b_030 ())). Qed.
Lemma stk_sh_idx sp i : sp mod 16 = 0 -> 0 <= i < 512 -> sp / 8 + 2147450368 + i = S (sp - 4096 + 8 * i).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRF ()) [] (Mh_0207_blobs1.kr_b_031 ())). Qed.
Lemma d32 x : (32 * x) / 8 = 4 * x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRF ()) [] (Mh_0207_blobs1.kr_b_032 ())). Qed.
Lemma d32b x : (32 * x + 32) / 8 = 4 * x + 4.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRF ()) [] (Mh_0207_blobs1.kr_b_033 ())). Qed.
Lemma pow2k k : 0 <= k <= 11 -> 1 <= 2 ^ k <= 2048.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEmbRF ()) [] (Mh_0207_blobs1.kr_b_034 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem fast : forall (fx : FPState) R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 m n,
    ri_inv HI (PQMA.mvec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PMA.AD L ar R M sp r 0 ->
    getr R (reg 10) = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    PQMA.mvec_at RSEGS PMSPA.accA PMSPA.annA M v b k stk -> Z.of_nat (length stk) < 2 ^ k ->
    getr R (reg 11) = Z_to_bv 64 p1 -> getr R (reg 12) = Z_to_bv 64 p2 -> p1 mod 4 = 0 -> p2 mod 4 = 0 ->
    byte_at M (S p1) 0 -> byte_at M (S p2) 0 ->
    PNAEK.argp (ar_sptop ar) FF sp v p1 4 -> PNAEK.argp (ar_sptop ar) FF sp v p2 4 ->
    L5.u32_at RSEGS M p1 m -> L5.u32_at RSEGS M p2 n -> 0 <= m < 2 ^ 31 -> 0 <= n < 2 ^ 31 ->
    PMSTA.base_okA RSEGS PMA.AD M ->
    (forall (fx' : FPState) R' M' model' LK' Aw', regs_preserved R R' -> PQMA.mvec_at RSEGS PMSPA.accA PMSPA.annA M' v b k (stk ++ [PQMA.MS m n 0]) ->
        PMSPA.accA M' v 24 -> PMSTA.base_okA RSEGS PMA.AD M' -> L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PQMA.mvec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xcf178 M model) K.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) ["Stage"] (Mh_0207_blobs1.kr_b_035 ())). Qed.
End Stage.
End PQAERF.

End PnAEmbRF.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan Require XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0224.
Module PnALocIslandP.
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan Require XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.XIcptAs0Kit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0224. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0224.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnALocIslandP () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP5PaliA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP5PaliA9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP7KS_aliAC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP5PaliA<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP5PaliA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP5PaliA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP5PaliA3NX0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS09fill_specC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS09copy_specC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS08tls_specC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP5PaliA3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP5PaliA3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP:KS_aliA_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207=PnALocIslandP6PMALIP5PaliA6cells0C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PMALIP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_036 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_037 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_038 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_039 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_040 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_041 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_042 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_043 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_044 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_045 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_046 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_047 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; byte_go.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
(* [comment removed for export] *)
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
(* [comment removed for export] *)
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          | |- L5KA.zeros_at _ ?a _ => lazymatch type of H with L5KA.zeros_at _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
(* [comment removed for export] *)
Local Ltac den_tac := first [reflexivity | lia | idtac].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.
(* [comment removed for export] *)
Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module PaliA := BndP_Na_143.LibSegNa_aliA.
Definition KS_aliA : list nat := Eval vm_compute in (BG.kept_list 48 PaliA.regs0 PaliA.regs_out0).
Lemma KS_aliA_ok : BG.kept_ok 48 PaliA.regs0 PaliA.regs_out0 KS_aliA = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_048 ())). Qed.
Lemma aliA_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> 7036928 <= (V 33%nat) <= 140737488355320 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 8 <= 2147446784) -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 8 <= ((V 2%nat) - 4096)) -> L5.writable RSEGS M (V 33%nat) 8 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> L5.img_clear M 6890290 6892144 ->
  L5.writable RSEGS M 6890290 1854 -> L5.img_clear M 6893976 6894064 -> L5.writable RSEGS M 6893976 88 -> L5.u8_at RSEGS M 7028115 0 ->
  L5.u32_at RSEGS M 7028336 0 -> L5.u64_at RSEGS M 7027520 (V 34%nat) -> L5.u64_at RSEGS M 1404312 1440376 -> L5.u64_at RSEGS M 1440376 2147450880 ->
  L5.u64_at RSEGS M 1404320 1443688 -> L5.u64_at RSEGS M 1443688 0 -> L5.u64_at RSEGS M 1404328 1443696 -> L5.u64_at RSEGS M 1443696 0 ->
  L5.u64_at RSEGS M 1404336 1443680 -> L5.u64_at RSEGS M 1443680 140737488355327 -> L5.u64_at RSEGS M 1407232 1443673 -> L5.u8_at RSEGS M 1443673 1 ->
  L5.u64_at RSEGS M 1412520 1347948 -> L5.u64_at RSEGS M 1412512 1346920 -> L5.u8_at RSEGS M 1443672 1 -> L5.u64_at RSEGS M 1412048 1346872 ->
  L5.u8_at RSEGS M 2037414 1 -> L5.u8_at RSEGS M 2037415 1 -> L5KA.zeros_at M 2148312158 248 -> L5KA.zeros_at M 2148312619 27 ->
  L5KA.zeros_at M 2147474905 65 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 4096) <= bv_unsigned a < ((V 2%nat) - 4096) + 4096) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 8) -> ~ ((0 + 6890290) <= bv_unsigned a < (0 + 6890290) + 1854) -> ~ ((0 + 6893976) <= bv_unsigned a < (0 + 6893976) + 88) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 4096) <= i < ((V 2%nat) - 4096) + 4096) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 8) -> ~ ((0 + 6890290) <= i < (0 + 6890290) + 1854) -> ~ ((0 + 6893976) <= i < (0 + 6893976) + 88) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x11e2b8 M) (st fx' R' 0x11e314 M')
        /\ (forall x, In x KS_aliA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 6891840
        /\ getr R' (reg 11) = Z_to_bv 64 6891840
        /\ L5.u64_at RSEGS M' (V 33%nat) 6891840
        /\ L5.u8_at RSEGS M' 6890800 1
        /\ L5.u64_at RSEGS M' 6890792 6891840).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALocIslandP ()) [] (Mh_0207_blobs1.kr_b_049 ())). Qed.
(* [comment removed for export] *)

End PMALIP.

End PnALocIslandP.
Module PnALvPushP.
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0169. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0169.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnALvPushP () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP8KS_azlE0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP=word_of_zpolyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP;KS_azlE0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP8KS_azlE1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP8KS_azlE2C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP;KS_azlE2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP8KS_azlE3C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE33ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP;KS_azlE3_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlE36cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP8KS_azlF1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF16cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP;KS_azlF1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP6PazlF29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP8KS_azlF2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlG9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP7KS_azlGC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlG<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP>u32_of_KWord4aC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlG6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlG3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP:KS_azlG_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlH5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlH9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP7KS_azlHC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlH<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlH3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlH2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlH3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlH6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlH3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlH3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP:KS_azlH_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlJ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlJ9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP7KS_azlJC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlJ<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlJ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlJ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlJ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlJ6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlJ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlJ3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP:KS_azlJ_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlK5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlK9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP7KS_azlKC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlK<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlK3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlK2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlK3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlK3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlK3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP:KS_azlK_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnALvPushP7PQALVPP5PazlK6cells0C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQALVPP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_050 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_051 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_052 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_053 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_054 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_055 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_056 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_057 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_058 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_059 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_060 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_061 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; byte_go.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
(* [comment removed for export] *)
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
(* [comment removed for export] *)
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          | |- L5KA.zeros_at _ ?a _ => lazymatch type of H with L5KA.zeros_at _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
(* [comment removed for export] *)
Local Ltac den_tac := first [reflexivity | lia | idtac].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.
(* [comment removed for export] *)
Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module PazlE0 := BndP_Na_043.LibSegNa_azlE0.
Definition KS_azlE0 : list nat := Eval vm_compute in (BG.kept_list 60 PazlE0.regs0 PazlE0.regs_out0).
Lemma KS_azlE0_ok : BG.kept_ok 60 PazlE0.regs0 PazlE0.regs_out0 KS_azlE0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_062 ())). Qed.
Lemma azlE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 65536 1409024 ->
  L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) ->
  L5.u64_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 16) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azlE0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756916
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 1
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 24
        /\ getr R' (reg 11) = Z_to_bv 64 32
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755320
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_063 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlE1 := BndP_Na_043.LibSegNa_azlE1.
Definition KS_azlE1 : list nat := Eval vm_compute in (BG.kept_list 60 PazlE1.regs0 PazlE1.regs_out0).
Lemma KS_azlE1_ok : BG.kept_ok 60 PazlE1.regs0 PazlE1.regs_out0 KS_azlE1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_064 ())). Qed.
Lemma azlE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 1 -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 16) 0 ->
  7036928 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 ->
  L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 7036928 <= (V 35%nat) <= 140737488355324 ->
  aligned (V 35%nat) 4 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 35%nat) (V 39%nat) ->
  (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 2147483647 ->
  4096 <= (V 40%nat) <= 140737488355304 -> aligned (V 40%nat) 16 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450880) 3 ->
  L5KA.zeros_at M ((((V 40%nat) + 4) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 40%nat) 24 -> (((V 2%nat) - 4096) + 4096 <= (V 40%nat) \/ (V 40%nat) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 40%nat) \/ (V 40%nat) + 24 <= (V 33%nat)) ->
  (65536 + 6971392 <= (V 40%nat) \/ (V 40%nat) + 24 <= 65536) -> ((V 34%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 24 <= (V 34%nat)) -> ((V 35%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 24 <= (V 35%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) 755320 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb8cb4 M) (st fx' R' 0x7ebbc M')
        /\ (forall x, In x KS_azlE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756180
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 18) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 16) 0
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 8) (if 0 <? (((V 39%nat) + 18446744073709551614) mod 2 ^ 64) then 1 else 0)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 4) (V 39%nat)
        /\ L5.u32_at RSEGS M' (V 40%nat) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) [] (Mh_0207_blobs1.kr_b_065 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlE2 := BndP_Na_043.LibSegNa_azlE2.
Definition KS_azlE2 : list nat := Eval vm_compute in (BG.kept_list 60 PazlE2.regs0 PazlE2.regs_out0).
Lemma KS_azlE2_ok : BG.kept_ok 60 PazlE2.regs0 PazlE2.regs_out0 KS_azlE2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_066 ())). Qed.
Lemma azlE2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) 0 ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) 0 -> 4096 <= (V 40%nat) <= 140737488355304 -> aligned (V 40%nat) 16 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 40%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 40%nat) 24 -> (((V 2%nat) - 4096) + 4096 <= (V 40%nat) \/ (V 40%nat) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 40%nat) \/ (V 40%nat) + 24 <= (V 33%nat)) ->
  (65536 + 6971392 <= (V 40%nat) \/ (V 40%nat) + 24 <= 65536) -> ((V 34%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 24 <= (V 34%nat)) -> ((V 35%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 24 <= (V 35%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 24) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb89d4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlE2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 757100
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 24)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 24)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 24)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 0
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_067 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlE3 := BndP_Na_043.LibSegNa_azlE3.
Definition KS_azlE3 : list nat := Eval vm_compute in (BG.kept_list 60 PazlE3.regs0 PazlE3.regs_out0).
Lemma KS_azlE3_ok : BG.kept_ok 60 PazlE3.regs0 PazlE3.regs_out0 KS_azlE3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_068 ())). Qed.
Lemma azlE3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 40%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 40%nat) + 24) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 40%nat) + 24) -> 4096 <= (V 40%nat) <= 140737488355280 -> aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 96) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 88) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb8d6c M) (st fx' R' 0xb878c M')
        /\ (forall x, In x KS_azlE3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 ((((V 2%nat) - 88) / 8) + 2147450880)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 24)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_069 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlF1 := BndP_Na_043.LibSegNa_azlF1.
Definition KS_azlF1 : list nat := Eval vm_compute in (BG.kept_list 60 PazlF1.regs0 PazlF1.regs_out0).
Lemma KS_azlF1_ok : BG.kept_ok 60 PazlF1.regs0 PazlF1.regs_out0 KS_azlF1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_070 ())). Qed.
Lemma azlF1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 41%nat) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 0 <= (V 37%nat) <= 49128 -> aligned (V 37%nat) 8 ->
  4120 <= (V 41%nat) <= 140737488355327 -> 24 <= ((V 41%nat) - ((V 36%nat) + (V 37%nat))) <= 49152 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlF1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 755996
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + (V 37%nat)) + 24)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755044
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_071 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlF2 := BndP_Na_043.LibSegNa_azlF2.
Definition KS_azlF2 : list nat := Eval vm_compute in (BG.kept_list 60 PazlF2.regs0 PazlF2.regs_out0).
Lemma KS_azlF2_ok : BG.kept_ok 60 PazlF2.regs0 PazlF2.regs_out0 KS_azlF2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_072 ())). Qed.
Lemma azlF2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + (V 37%nat)) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (V 37%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) (V 41%nat) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 7036928 <= (V 34%nat) <= 140737488355324 ->
  aligned (V 34%nat) 4 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) ->
  (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 7036928 <= (V 35%nat) <= 140737488355324 -> aligned (V 35%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755044 ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> 0 <= (V 37%nat) <= 49128 -> aligned (V 37%nat) 8 -> 4120 <= (V 41%nat) <= 140737488355327 ->
  24 <= ((V 41%nat) - ((V 36%nat) + (V 37%nat))) <= 49152 -> L5KA.zeros_at M ((((V 36%nat) + (V 37%nat)) / 8) + 2147450880) 3 -> L5KA.zeros_at M (((((V 36%nat) + (V 37%nat)) + 4) / 8) + 2147450880) 1 -> L5.writable RSEGS M ((V 36%nat) + (V 37%nat)) 24 ->
  (2147446784 + 17592186048512 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 24 <= 2147446784) -> (65536 + 6971392 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 24 <= 65536) -> 4096 <= ((V 36%nat) + (V 37%nat)) <= 140737488355304 -> (((V 2%nat) - 4096) + 4096 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 24 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 24 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 24 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 24 <= (V 34%nat)) -> ((V 35%nat) + 4 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 24 <= (V 35%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 36%nat) + (V 37%nat)) + 0) <= bv_unsigned a < (((V 36%nat) + (V 37%nat)) + 0) + 24) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 36%nat) + (V 37%nat)) + 0) <= i < (((V 36%nat) + (V 37%nat)) + 0) + 24) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb891c M) (st fx' R' 0xb878c M')
        /\ (forall x, In x KS_azlF2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 36%nat) + (V 37%nat)) + 24)
        /\ L5.u64_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 16) 0
        /\ L5.u32_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 8) (if 0 <? (((V 39%nat) + 18446744073709551614) mod 2 ^ 64) then 1 else 0)
        /\ L5.u32_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 4) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 36%nat) + (V 37%nat)) (V 38%nat)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) [] (Mh_0207_blobs1.kr_b_073 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlG := BndP_Na_043.LibSegNa_azlG.
Definition KS_azlG : list nat := Eval vm_compute in (BG.kept_list 60 PazlG.regs0 PazlG.regs_out0).
Lemma KS_azlG_ok : BG.kept_ok 60 PazlG.regs0 PazlG.regs_out0 KS_azlG = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_074 ())). Qed.
Lemma azlG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 42%nat) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 (V 37%nat) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + (V 37%nat)) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 24 <= (V 37%nat) <= 24576 -> aligned (V 37%nat) 8 ->
  2 <= (V 42%nat) <= 2048 -> 7036928 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) ->
  L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) ->
  7036928 <= (V 35%nat) <= 140737488355324 -> aligned (V 35%nat) 4 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u32_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 2147483647 ->
  0 <= (V 39%nat) <= 2147483647 -> 4096 <= (V 40%nat) <= 140737488355280 -> aligned (V 40%nat) 16 -> L5.writable RSEGS M ((V 40%nat) + (V 37%nat)) 24 ->
  L5KA.zeros_at M ((((V 40%nat) + (V 37%nat)) / 8) + 2147450880) 3 -> L5KA.zeros_at M (((((V 40%nat) + (V 37%nat)) + 4) / 8) + 2147450880) 1 -> L5KA.zeros_at M (((((V 37%nat) + (V 40%nat)) + 4) / 8) + 2147450880) 1 -> 4096 <= ((V 37%nat) + (V 40%nat)) <= 140737488355304 ->
  aligned ((V 37%nat) + (V 40%nat)) 8 -> L5KA.zeros_at M ((((V 37%nat) + (V 40%nat)) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + (V 37%nat)) \/ ((V 40%nat) + (V 37%nat)) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + (V 37%nat)) <= 140737488355304 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + (V 37%nat)) \/ ((V 40%nat) + (V 37%nat)) + 24 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + (V 37%nat)) \/ ((V 40%nat) + (V 37%nat)) + 24 <= (V 33%nat)) -> (65536 + 6971392 <= ((V 40%nat) + (V 37%nat)) \/ ((V 40%nat) + (V 37%nat)) + 24 <= 65536) -> ((V 34%nat) + 4 <= ((V 40%nat) + (V 37%nat)) \/ ((V 40%nat) + (V 37%nat)) + 24 <= (V 34%nat)) ->
  ((V 35%nat) + 4 <= ((V 40%nat) + (V 37%nat)) \/ ((V 40%nat) + (V 37%nat)) + 24 <= (V 35%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755320 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ ((((V 40%nat) + (V 37%nat)) + 0) <= bv_unsigned a < (((V 40%nat) + (V 37%nat)) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ ((((V 40%nat) + (V 37%nat)) + 0) <= i < (((V 40%nat) + (V 37%nat)) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb8cb4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 754692
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 8) / 8)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 756096
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (((V 37%nat) + (V 40%nat)) + 24)
        /\ L5.u64_at RSEGS M' (((V 37%nat) + (V 40%nat)) + 16) 0
        /\ L5.u32_at RSEGS M' (((V 37%nat) + (V 40%nat)) + 8) (if 0 <? (((V 39%nat) + 18446744073709551614) mod 2 ^ 64) then 1 else 0)
        /\ L5.u32_at RSEGS M' (((V 37%nat) + (V 40%nat)) + 4) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 37%nat) + (V 40%nat)) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + (24 * (V 42%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 37%nat) + (V 40%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_075 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlH := BndP_Na_043.LibSegNa_azlH.
Definition KS_azlH : list nat := Eval vm_compute in (BG.kept_list 60 PazlH.regs0 PazlH.regs_out0).
Lemma KS_azlH_ok : BG.kept_ok 60 PazlH.regs0 PazlH.regs_out0 KS_azlH = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_076 ())). Qed.
Lemma azlH_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + (V 37%nat)) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 24 <= (V 37%nat) <= 24576 -> aligned (V 37%nat) 8 ->
  2 <= (V 42%nat) <= 2048 -> 4096 <= (V 40%nat) <= 140737488355280 -> aligned (V 40%nat) 16 -> L5.writable RSEGS M ((V 40%nat) + (V 37%nat)) 24 ->
  L5KA.zeros_at M ((((V 40%nat) + (V 37%nat)) / 8) + 2147450880) 3 -> (2147446784 + 17592186048512 <= ((V 40%nat) + (V 37%nat)) \/ ((V 40%nat) + (V 37%nat)) + 24 <= 2147446784) -> 4096 <= ((V 40%nat) + (V 37%nat)) <= 140737488355304 -> (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + (V 37%nat)) \/ ((V 40%nat) + (V 37%nat)) + 24 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 24 <= ((V 40%nat) + (V 37%nat)) \/ ((V 40%nat) + (V 37%nat)) + 24 <= (V 33%nat)) -> (65536 + 6971392 <= ((V 40%nat) + (V 37%nat)) \/ ((V 40%nat) + (V 37%nat)) + 24 <= 65536) -> ((V 34%nat) + 4 <= ((V 40%nat) + (V 37%nat)) \/ ((V 40%nat) + (V 37%nat)) + 24 <= (V 34%nat)) -> ((V 35%nat) + 4 <= ((V 40%nat) + (V 37%nat)) \/ ((V 40%nat) + (V 37%nat)) + 24 <= (V 35%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (((V 40%nat) + (V 37%nat)) + 24) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + (24 * (V 42%nat))) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 756096 -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 2%nat) - 104) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb8404 M) (st fx' R' 0x7ebbc M')
        /\ (forall x, In x KS_azlH -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756180
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + (V 37%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (((V 40%nat) + (V 37%nat)) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + (24 * (V 42%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_077 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlJ := BndP_Na_044.LibSegNa_azlJ.
Definition KS_azlJ : list nat := Eval vm_compute in (BG.kept_list 60 PazlJ.regs0 PazlJ.regs_out0).
Lemma KS_azlJ_ok : BG.kept_ok 60 PazlJ.regs0 PazlJ.regs_out0 KS_azlJ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_078 ())). Qed.
Lemma azlJ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 (V 37%nat) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 40%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) (((V 40%nat) + (V 37%nat)) + 24) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 40%nat) + (24 * (V 42%nat))) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355280 ->
  aligned (V 40%nat) 16 -> 24 <= (V 37%nat) <= 24576 -> aligned (V 37%nat) 8 -> 2 <= (V 42%nat) <= 2048 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 36%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb8d6c M) (st fx' R' 0xf1fc0 M')
        /\ (forall x, In x KS_azlJ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 755544
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 ((((V 2%nat) - 88) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 (((V 40%nat) + (V 37%nat)) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + (V 37%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_079 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlK := BndP_Na_044.LibSegNa_azlK.
Definition KS_azlK : list nat := Eval vm_compute in (BG.kept_list 60 PazlK.regs0 PazlK.regs_out0).
Lemma KS_azlK_ok : BG.kept_ok 60 PazlK.regs0 PazlK.regs_out0 KS_azlK = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_080 ())). Qed.
Lemma azlK_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 20) = Z_to_bv 64 (V 41%nat) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb8758 M) (st fx' R' 0xb878c M')
        /\ (forall x, In x KS_azlK -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 41%nat) - 24)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (V 41%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP ()) [] (Mh_0207_blobs1.kr_b_081 ())). Qed.
(* [comment removed for export] *)

End PQALVPP.

End PnALvPushP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014.
Module PnALvPushF.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnAEmbKitQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAIss1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAEmbKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnALvPushP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAEmbRF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014.Na0_code_rb8880_b8884.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5CoreB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnALvPushF () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic3notC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic5proj2K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_0213:PnSpecsAXl6PQSAXL6lvl_eoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3ltbK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op204".
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PQALVPF.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
(* [comment removed for export] *)
Lemma eo_val n : 0 <= n < 2 ^ 31 -> (if 0 <? ((n + 18446744073709551614) mod 2 ^ 64) then 1 else 0) = PQSAXL.lvl_eo n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushF ()) [] (Mh_0207_blobs1.kr_b_082 ())). Qed.

Import PQAERF.
Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem fast : forall (fx : FPState) R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 m n,
    ri_inv HI (PQMA.lvec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PMA.AD L ar R M sp r 0 ->
    getr R (reg 10) = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    PQMA.lvec_at RSEGS PMSPA.accA PMSPA.annA M v b k stk -> Z.of_nat (length stk) < 2 ^ k ->
    getr R (reg 11) = Z_to_bv 64 p1 -> getr R (reg 12) = Z_to_bv 64 p2 -> p1 mod 4 = 0 -> p2 mod 4 = 0 ->
    byte_at M (S p1) 0 -> byte_at M (S p2) 0 ->
    PNAEK.argp (ar_sptop ar) FF sp v p1 4 -> PNAEK.argp (ar_sptop ar) FF sp v p2 4 ->
    L5.u32_at RSEGS M p1 m -> L5.u32_at RSEGS M p2 n -> 0 <= m < 2 ^ 31 -> 0 <= n < 2 ^ 31 ->
    PMSTA.base_okA RSEGS PMA.AD M ->
    (forall (fx' : FPState) R' M' model' LK' Aw', regs_preserved R R' -> PQMA.lvec_at RSEGS PMSPA.accA PMSPA.annA M' v b k (stk ++ [PQMA.AL m n (PQSAXL.lvl_eo n)]) ->
        PMSPA.accA M' v 24 -> PMSTA.base_okA RSEGS PMA.AD M' -> L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PQMA.lvec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb84e8 M model) K.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) ["Stage"] (Mh_0207_blobs1.kr_b_083 ())). Qed.
End Stage.
End PQALVPF.

End PnALvPushF.
Module PnALvPushE.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnAEmbKitQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAIss1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAEmbKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnALvPushP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnALvPushF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAEmbRF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014.Na0_code_rb8880_b8884.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5CoreB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PQALVPE.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem empty : PMA.opnew_spec L ar HI -> forall (fx : FPState) R M model K LBX FF LK Aw cr v sp r p1 p2 m n,
    ri_inv HI LBX FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PMA.AD L ar R M sp r 0 ->
    getr R (reg 10) = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    L5.u64_at RSEGS M v 0 -> L5.u64_at RSEGS M (v + 8) 0 -> L5.u64_at RSEGS M (v + 16) 0 ->
    getr R (reg 11) = Z_to_bv 64 p1 -> getr R (reg 12) = Z_to_bv 64 p2 -> p1 mod 4 = 0 -> p2 mod 4 = 0 ->
    byte_at M (S p1) 0 -> byte_at M (S p2) 0 ->
    PNAEK.argp (ar_sptop ar) FF sp v p1 4 -> PNAEK.argp (ar_sptop ar) FF sp v p2 4 ->
    L5.u32_at RSEGS M p1 m -> L5.u32_at RSEGS M p2 n -> 0 <= m < 2 ^ 31 -> 0 <= n < 2 ^ 31 -> acredit_ok L cr 24 ->
    PMSTA.base_okA RSEGS PMA.AD M ->
    (forall (fx' : FPState) R' M' model' LK' Aw' b', regs_preserved R R' -> PQMA.lvec_at RSEGS PMSPA.accA PMSPA.annA M' v b' 0 [PQMA.AL m n (PQSAXL.lvl_eo n)] ->
        PMSPA.accA M' v 24 -> PMSTA.base_okA RSEGS PMA.AD M' -> L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PQMA.lvec_own b' 0 ++ LBX) FF LK' (adebit L cr 24) Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb84e8 M model) K.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) ["Stage"] (Mh_0207_blobs1.kr_b_084 ())). Qed.
End Stage.
End PQALVPE.

End PnALvPushE.
Module PnALvPushP2.
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0169. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0169.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnALvPushP2 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP27alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2=word_of_zpolyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2;KS_azlS0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2;KS_azlS1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2;KS_azlS2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS3C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS36cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS33ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2;KS_azlS3_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS49regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS4C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS4<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS46cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS43ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2;KS_azlS4_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS59regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS5C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS5<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS56cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS53ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2;KS_azlS5_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS69regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS6C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS6<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS66cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS63ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2;KS_azlS6_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS79regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS7C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS7<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS76cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS73ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2;KS_azlS7_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS89regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS8<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS86cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS83ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2;KS_azlS8_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS95regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS99regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP28KS_azlS9C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS9<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS93PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS92F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS93NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS96cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS93kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP26PazlS93ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2;KS_azlS9_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP27PazlS105regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP27PazlS109regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP29KS_azlS10C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP27PazlS10<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP27PazlS103PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP27PazlS102F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP27PazlS103NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP27PazlS106cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP27PazlS103kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP27PazlS103ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP28PQALVPP2<KS_azlS10_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQALVPP2.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_085 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_086 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_087 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_088 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_089 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_090 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_091 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_092 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_093 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_094 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_095 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_096 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; byte_go.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
(* [comment removed for export] *)
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
(* [comment removed for export] *)
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          | |- L5KA.zeros_at _ ?a _ => lazymatch type of H with L5KA.zeros_at _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
(* [comment removed for export] *)
Local Ltac den_tac := first [reflexivity | lia | idtac].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.
(* [comment removed for export] *)
Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module PazlS0 := BndP_Na_044.LibSegNa_azlS0.
Definition KS_azlS0 : list nat := Eval vm_compute in (BG.kept_list 60 PazlS0.regs0 PazlS0.regs_out0).
Lemma KS_azlS0_ok : BG.kept_ok 60 PazlS0.regs0 PazlS0.regs_out0 KS_azlS0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_097 ())). Qed.
Lemma azlS0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 24) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 24) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azlS0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756916
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 2
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 48
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 24
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755320
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_098 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlS1 := BndP_Na_044.LibSegNa_azlS1.
Definition KS_azlS1 : list nat := Eval vm_compute in (BG.kept_list 60 PazlS1.regs0 PazlS1.regs_out0).
Lemma KS_azlS1_ok : BG.kept_ok 60 PazlS1.regs0 PazlS1.regs_out0 KS_azlS1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_099 ())). Qed.
Lemma azlS1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 48) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 48) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azlS1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756916
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 4
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 96
        /\ getr R' (reg 11) = Z_to_bv 64 128
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 48
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755320
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_100 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlS2 := BndP_Na_045.LibSegNa_azlS2.
Definition KS_azlS2 : list nat := Eval vm_compute in (BG.kept_list 60 PazlS2.regs0 PazlS2.regs_out0).
Lemma KS_azlS2_ok : BG.kept_ok 60 PazlS2.regs0 PazlS2.regs_out0 KS_azlS2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_101 ())). Qed.
Lemma azlS2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 96) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 96) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azlS2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756916
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 8
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 192
        /\ getr R' (reg 11) = Z_to_bv 64 256
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 96
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755320
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_102 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlS3 := BndP_Na_045.LibSegNa_azlS3.
Definition KS_azlS3 : list nat := Eval vm_compute in (BG.kept_list 60 PazlS3.regs0 PazlS3.regs_out0).
Lemma KS_azlS3_ok : BG.kept_ok 60 PazlS3.regs0 PazlS3.regs_out0 KS_azlS3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_103 ())). Qed.
Lemma azlS3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 192) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 192) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azlS3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756916
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 16
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 384
        /\ getr R' (reg 11) = Z_to_bv 64 512
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 192
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755320
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_104 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlS4 := BndP_Na_045.LibSegNa_azlS4.
Definition KS_azlS4 : list nat := Eval vm_compute in (BG.kept_list 60 PazlS4.regs0 PazlS4.regs_out0).
Lemma KS_azlS4_ok : BG.kept_ok 60 PazlS4.regs0 PazlS4.regs_out0 KS_azlS4 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_105 ())). Qed.
Lemma azlS4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 384) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 384) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azlS4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756916
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 32
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 768
        /\ getr R' (reg 11) = Z_to_bv 64 1024
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 384
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755320
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_106 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlS5 := BndP_Na_045.LibSegNa_azlS5.
Definition KS_azlS5 : list nat := Eval vm_compute in (BG.kept_list 60 PazlS5.regs0 PazlS5.regs_out0).
Lemma KS_azlS5_ok : BG.kept_ok 60 PazlS5.regs0 PazlS5.regs_out0 KS_azlS5 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_107 ())). Qed.
Lemma azlS5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 768) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 768) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azlS5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756916
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 64
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1536
        /\ getr R' (reg 11) = Z_to_bv 64 2048
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 768
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755320
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_108 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlS6 := BndP_Na_045.LibSegNa_azlS6.
Definition KS_azlS6 : list nat := Eval vm_compute in (BG.kept_list 60 PazlS6.regs0 PazlS6.regs_out0).
Lemma KS_azlS6_ok : BG.kept_ok 60 PazlS6.regs0 PazlS6.regs_out0 KS_azlS6 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_109 ())). Qed.
Lemma azlS6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 1536) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 1536) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azlS6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756916
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 128
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 3072
        /\ getr R' (reg 11) = Z_to_bv 64 4096
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 1536
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755320
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_110 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlS7 := BndP_Na_045.LibSegNa_azlS7.
Definition KS_azlS7 : list nat := Eval vm_compute in (BG.kept_list 60 PazlS7.regs0 PazlS7.regs_out0).
Lemma KS_azlS7_ok : BG.kept_ok 60 PazlS7.regs0 PazlS7.regs_out0 KS_azlS7 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_111 ())). Qed.
Lemma azlS7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 3072) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 3072) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azlS7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756916
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 256
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 6144
        /\ getr R' (reg 11) = Z_to_bv 64 8192
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 3072
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755320
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_112 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlS8 := BndP_Na_045.LibSegNa_azlS8.
Definition KS_azlS8 : list nat := Eval vm_compute in (BG.kept_list 60 PazlS8.regs0 PazlS8.regs_out0).
Lemma KS_azlS8_ok : BG.kept_ok 60 PazlS8.regs0 PazlS8.regs_out0 KS_azlS8 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_113 ())). Qed.
Lemma azlS8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 6144) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 6144) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azlS8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756916
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 512
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 12288
        /\ getr R' (reg 11) = Z_to_bv 64 16384
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 6144
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755320
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_114 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlS9 := BndP_Na_045.LibSegNa_azlS9.
Definition KS_azlS9 : list nat := Eval vm_compute in (BG.kept_list 60 PazlS9.regs0 PazlS9.regs_out0).
Lemma KS_azlS9_ok : BG.kept_ok 60 PazlS9.regs0 PazlS9.regs_out0 KS_azlS9 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_115 ())). Qed.
Lemma azlS9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 12288) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 12288) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azlS9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756916
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 1024
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 24576
        /\ getr R' (reg 11) = Z_to_bv 64 32768
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 12288
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755320
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_116 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlS10 := BndP_Na_044.LibSegNa_azlS10.
Definition KS_azlS10 : list nat := Eval vm_compute in (BG.kept_list 60 PazlS10.regs0 PazlS10.regs_out0).
Lemma KS_azlS10_ok : BG.kept_ok 60 PazlS10.regs0 PazlS10.regs_out0 KS_azlS10 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_117 ())). Qed.
Lemma azlS10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 24576) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 24576) ->
  4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb84e8 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_azlS10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 756916
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 2048
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 49152
        /\ getr R' (reg 11) = Z_to_bv 64 65536
        /\ getr R' (reg 12) = Z_to_bv 64 384307168202282325
        /\ getr R' (reg 13) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 24576
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755320
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP2 ()) [] (Mh_0207_blobs1.kr_b_118 ())). Qed.
(* [comment removed for export] *)

End PQALVPP2.

End PnALvPushP2.
Module PnALvPushG1.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnAEmbKitQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAEmbKitQ2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAIss1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAEmbKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnALvPushP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnALvPushP2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAEmbRF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnALvPushF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnALvPushGStmts.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5CoreB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnALvPushG1 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00C56Stdlib6ZArith6BinInt1Z3mulK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega=RingMicromega3Op201".
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PQALVPG1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac amod := match goal with H : ?x mod ?m = 0 |- ?x mod ?m = 0 => exact H end.
Ltac ftac := lazymatch goal with |- PQALVPP.aligned _ _ => unfold PQALVPP.aligned; first [amod | lia] | |- PQALVPP2.aligned _ _ => unfold PQALVPP2.aligned; first [amod | lia] end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma pow2k10 k : 0 <= k <= 10 -> 1 <= 2 ^ k <= 1024.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushG1 ()) [] (Mh_0207_blobs1.kr_b_119 ())). Qed.
Lemma pow2s k : 0 <= k -> 2 ^ (k + 1) = 2 * 2 ^ k.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushG1 ()) [] (Mh_0207_blobs1.kr_b_120 ())). Qed.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem grow1 : PMA.opnew_spec L ar HI -> forall (fx : FPState) R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 m n,
    ri_inv HI (PQMA.lvec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PMA.AD L ar R M sp r 0 ->
    getr R (reg 10) = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    PQMA.lvec_at RSEGS PMSPA.accA PMSPA.annA M v b k stk -> Z.of_nat (length stk) = 2 ^ k -> k <= 10 ->
    getr R (reg 11) = Z_to_bv 64 p1 -> getr R (reg 12) = Z_to_bv 64 p2 -> p1 mod 4 = 0 -> p2 mod 4 = 0 ->
    byte_at M (S p1) 0 -> byte_at M (S p2) 0 ->
    PNAEK.argp (ar_sptop ar) FF sp v p1 4 -> PNAEK.argp (ar_sptop ar) FF sp v p2 4 ->
    L5.u32_at RSEGS M p1 m -> L5.u32_at RSEGS M p2 n -> 0 <= m < 2 ^ 31 -> 0 <= n < 2 ^ 31 -> acredit_ok L cr (24 * 2 ^ (k + 1)) ->
    PMSTA.base_okA RSEGS PMA.AD M ->
    (forall (fx6 : FPState) R6 M6 model6 Aw6 B, PQALVPGS.gmid L ar HI R M model LBX FF LK Aw cr v b k stk sp p1 p2 m n B R6 M6 model6 Aw6 ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx6 R6 0xb89d4 M6 model6) K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb84e8 M model) K.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) ["Stage"] (Mh_0207_blobs1.kr_b_121 ())). Qed.
End Stage.
End PQALVPG1.

End PnALvPushG1.
Module PnALvPushP3.
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0169. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0169.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnALvPushP3 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP37alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3;KS_azlI0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3;KS_azlI1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3;KS_azlI2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI3C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI36cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI33ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3;KS_azlI3_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI49regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI4C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI4<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI46cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI43ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3;KS_azlI4_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI59regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI5C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI5<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI56cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI53ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3;KS_azlI5_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI69regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI6C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI6<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI66cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI63ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3;KS_azlI6_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI79regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI7C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI7<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI76cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI73ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3;KS_azlI7_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI89regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI8<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI86cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI83ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3;KS_azlI8_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI95regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI99regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP38KS_azlI9C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI9<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI93PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI92F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI93NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI96cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI93kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP36PazlI93ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3;KS_azlI9_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP37PazlI105regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP37PazlI109regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP39KS_azlI10C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP37PazlI10<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP37PazlI103PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP37PazlI102F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP37PazlI103NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP37PazlI106cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP37PazlI103kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP37PazlI103ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnALvPushP38PQALVPP3<KS_azlI10_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQALVPP3.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_122 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_123 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_124 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_125 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_126 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_127 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_128 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_129 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_130 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_131 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_132 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_133 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; byte_go.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
(* [comment removed for export] *)
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
(* [comment removed for export] *)
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          | |- L5KA.zeros_at _ ?a _ => lazymatch type of H with L5KA.zeros_at _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
(* [comment removed for export] *)
Local Ltac den_tac := first [reflexivity | lia | idtac].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.
(* [comment removed for export] *)
Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module PazlI0 := BndP_Na_043.LibSegNa_azlI0.
Definition KS_azlI0 : list nat := Eval vm_compute in (BG.kept_list 60 PazlI0.regs0 PazlI0.regs_out0).
Lemma KS_azlI0_ok : BG.kept_ok 60 PazlI0.regs0 PazlI0.regs_out0 KS_azlI0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_134 ())). Qed.
Lemma azlI0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 24) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 24) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355280 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 24) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb89d4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlI0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 757100
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 48)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 48)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 48)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_135 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlI1 := BndP_Na_043.LibSegNa_azlI1.
Definition KS_azlI1 : list nat := Eval vm_compute in (BG.kept_list 60 PazlI1.regs0 PazlI1.regs_out0).
Lemma KS_azlI1_ok : BG.kept_ok 60 PazlI1.regs0 PazlI1.regs_out0 KS_azlI1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_136 ())). Qed.
Lemma azlI1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 48) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 48) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355280 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 48) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 72) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 96) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb89d4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlI1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 757100
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 72)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 48)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 96)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 72)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_137 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlI2 := BndP_Na_044.LibSegNa_azlI2.
Definition KS_azlI2 : list nat := Eval vm_compute in (BG.kept_list 60 PazlI2.regs0 PazlI2.regs_out0).
Lemma KS_azlI2_ok : BG.kept_ok 60 PazlI2.regs0 PazlI2.regs_out0 KS_azlI2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_138 ())). Qed.
Lemma azlI2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 96) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 96) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355280 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 96) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 120) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 192) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb89d4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlI2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 757100
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 192)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 192)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 120)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 96)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 192)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_139 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlI3 := BndP_Na_044.LibSegNa_azlI3.
Definition KS_azlI3 : list nat := Eval vm_compute in (BG.kept_list 60 PazlI3.regs0 PazlI3.regs_out0).
Lemma KS_azlI3_ok : BG.kept_ok 60 PazlI3.regs0 PazlI3.regs_out0 KS_azlI3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_140 ())). Qed.
Lemma azlI3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 192) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 192) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355280 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 192) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 216) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 384) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb89d4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlI3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 757100
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 384)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 384)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 216)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 192)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 384)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 216)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_141 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlI4 := BndP_Na_044.LibSegNa_azlI4.
Definition KS_azlI4 : list nat := Eval vm_compute in (BG.kept_list 60 PazlI4.regs0 PazlI4.regs_out0).
Lemma KS_azlI4_ok : BG.kept_ok 60 PazlI4.regs0 PazlI4.regs_out0 KS_azlI4 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_142 ())). Qed.
Lemma azlI4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 384) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 384) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355280 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 384) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 408) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 768) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb89d4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlI4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 757100
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 768)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 768)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 408)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 384)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 768)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 408)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_143 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlI5 := BndP_Na_044.LibSegNa_azlI5.
Definition KS_azlI5 : list nat := Eval vm_compute in (BG.kept_list 60 PazlI5.regs0 PazlI5.regs_out0).
Lemma KS_azlI5_ok : BG.kept_ok 60 PazlI5.regs0 PazlI5.regs_out0 KS_azlI5 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_144 ())). Qed.
Lemma azlI5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 768) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 768) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355280 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 768) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 792) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 1536) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb89d4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlI5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 757100
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 1536)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 1536)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 792)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 768)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 1536)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 792)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_145 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlI6 := BndP_Na_044.LibSegNa_azlI6.
Definition KS_azlI6 : list nat := Eval vm_compute in (BG.kept_list 60 PazlI6.regs0 PazlI6.regs_out0).
Lemma KS_azlI6_ok : BG.kept_ok 60 PazlI6.regs0 PazlI6.regs_out0 KS_azlI6 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_146 ())). Qed.
Lemma azlI6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 1536) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 1536) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355280 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 1536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 1560) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 3072) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb89d4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlI6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 757100
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 3072)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 3072)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 1560)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 1536)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 3072)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 1560)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_147 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlI7 := BndP_Na_044.LibSegNa_azlI7.
Definition KS_azlI7 : list nat := Eval vm_compute in (BG.kept_list 60 PazlI7.regs0 PazlI7.regs_out0).
Lemma KS_azlI7_ok : BG.kept_ok 60 PazlI7.regs0 PazlI7.regs_out0 KS_azlI7 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_148 ())). Qed.
Lemma azlI7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 3072) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 3072) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355280 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 3072) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 3096) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 6144) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb89d4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlI7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 757100
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 6144)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 6144)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 3096)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 3072)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 6144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 3096)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_149 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlI8 := BndP_Na_044.LibSegNa_azlI8.
Definition KS_azlI8 : list nat := Eval vm_compute in (BG.kept_list 60 PazlI8.regs0 PazlI8.regs_out0).
Lemma KS_azlI8_ok : BG.kept_ok 60 PazlI8.regs0 PazlI8.regs_out0 KS_azlI8 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_150 ())). Qed.
Lemma azlI8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 6144) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 6144) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355280 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 6144) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 6168) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 12288) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb89d4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlI8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 757100
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 12288)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 12288)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 6168)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 6144)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 12288)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 6168)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_151 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlI9 := BndP_Na_044.LibSegNa_azlI9.
Definition KS_azlI9 : list nat := Eval vm_compute in (BG.kept_list 60 PazlI9.regs0 PazlI9.regs_out0).
Lemma KS_azlI9_ok : BG.kept_ok 60 PazlI9.regs0 PazlI9.regs_out0 KS_azlI9 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_152 ())). Qed.
Lemma azlI9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 12288) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 12288) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355280 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 12288) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 12312) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 24576) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb89d4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlI9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 757100
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 24576)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 24576)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 12312)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 12288)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 24576)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 12312)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_153 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazlI10 := BndP_Na_044.LibSegNa_azlI10.
Definition KS_azlI10 : list nat := Eval vm_compute in (BG.kept_list 60 PazlI10.regs0 PazlI10.regs_out0).
Lemma KS_azlI10_ok : BG.kept_ok 60 PazlI10.regs0 PazlI10.regs_out0 KS_azlI10 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_154 ())). Qed.
Lemma azlI10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 24576) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 24576) -> 4096 <= (V 36%nat) <= 140737488355304 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355280 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 755524 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 24576) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 24600) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 49152) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb89d4 M) (st fx' R' 0x829a4 M')
        /\ (forall x, In x KS_azlI10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 757100
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 49152)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 49152)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 24600)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 755524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 24576)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 49152)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 24600)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnALvPushP3 ()) [] (Mh_0207_blobs1.kr_b_155 ())). Qed.
(* [comment removed for export] *)

End PQALVPP3.

End PnALvPushP3.
Module PnALvPushG2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnAEmbKitQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAIss1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAEmbKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnALvPushP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnALvPushP3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAEmbRF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnALvPushF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnALvPushG1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnALvPushGStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0014.Na0_code_rb8880_b8884.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5CoreB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PQALVPG2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac amod := match goal with H : ?x mod ?m = 0 |- ?x mod ?m = 0 => exact H end.
Ltac ftac := lazymatch goal with |- PQALVPP.aligned _ _ => unfold PQALVPP.aligned; first [amod | lia] | |- PQALVPP3.aligned _ _ => unfold PQALVPP3.aligned; first [amod | lia] end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem grow2 : PMA.opdel_spec L ar HI -> forall (fx6 : FPState) R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 m n B R6 M6 model6 Aw6,
    ri_inv HI (PQMA.lvec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> K [] -> PMSPA.entryA PMA.AD L ar R M sp r 0 ->
    PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> Z.of_nat (length stk) = 2 ^ k -> 0 <= k <= 10 -> 0 <= p1 < 2 ^ 47 -> 0 <= p2 < 2 ^ 47 ->
    PMSTA.base_okA RSEGS PMA.AD M ->
    PQALVPGS.gmid L ar HI R M model LBX FF LK Aw cr v b k stk sp p1 p2 m n B R6 M6 model6 Aw6 ->
    (forall (fx' : FPState) R' M' model' LK' Aw' b', regs_preserved R R' -> PQMA.lvec_at RSEGS PMSPA.accA PMSPA.annA M' v b' (k + 1) (stk ++ [PQMA.AL m n (PQSAXL.lvl_eo n)]) ->
        PMSPA.accA M' v 24 -> PMSTA.base_okA RSEGS PMA.AD M' -> L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PQMA.lvec_own b' (k + 1) ++ LBX) FF LK' (adebit L cr (24 * 2 ^ (k + 1))) Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx6 R6 0xb89d4 M6 model6) K.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) ["Stage"] (Mh_0207_blobs1.kr_b_156 ())). Qed.
End Stage.
End PQALVPG2.

End PnALvPushG2.
Module PnAEmbRE.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnAEmbKitQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAIss1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAEmbKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAEmbRP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAEmbRF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012.Na0_code_rc2444_c2448.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5CoreB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PQAERE.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem empty : PMA.opnew_spec L ar HI -> forall (fx : FPState) R M model K LBX FF LK Aw cr v sp r p1 p2 m n,
    ri_inv HI LBX FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PMA.AD L ar R M sp r 0 ->
    getr R (reg 10) = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    L5.u64_at RSEGS M v 0 -> L5.u64_at RSEGS M (v + 8) 0 -> L5.u64_at RSEGS M (v + 16) 0 ->
    getr R (reg 11) = Z_to_bv 64 p1 -> getr R (reg 12) = Z_to_bv 64 p2 -> p1 mod 4 = 0 -> p2 mod 4 = 0 ->
    byte_at M (S p1) 0 -> byte_at M (S p2) 0 ->
    PNAEK.argp (ar_sptop ar) FF sp v p1 4 -> PNAEK.argp (ar_sptop ar) FF sp v p2 4 ->
    L5.u32_at RSEGS M p1 m -> L5.u32_at RSEGS M p2 n -> 0 <= m < 2 ^ 31 -> 0 <= n < 2 ^ 31 -> acredit_ok L cr 24 ->
    PMSTA.base_okA RSEGS PMA.AD M ->
    (forall (fx' : FPState) R' M' model' LK' Aw' b', regs_preserved R R' -> PQMA.mvec_at RSEGS PMSPA.accA PMSPA.annA M' v b' 0 [PQMA.MS m n 0] ->
        PMSPA.accA M' v 24 -> PMSTA.base_okA RSEGS PMA.AD M' -> L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PQMA.mvec_own b' 0 ++ LBX) FF LK' (adebit L cr 24) Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xcf178 M model) K.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) ["Stage"] (Mh_0207_blobs1.kr_b_157 ())). Qed.
End Stage.
End PQAERE.

End PnAEmbRE.
Module PnAEmbR.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAEmbKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAEmbRF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAEmbRE.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PQAER.
Abbreviation RSEGS := Asan.M.loaded_segments.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.

Theorem push_root_ok : PMA.opnew_spec L ar HI -> PQSAXQ.push_root_spec RSEGS PMA.AD L ar HI 0xcf178.
Proof.
  intros NEW. unfold PQSAXQ.push_root_spec, PQSAXQ.push_spec_at.
  intros fx R M model K LBX FF LK Aw cr v b k stk own c sp r HH AM K0 ENT FRS A10 AOV V8 ACCV PRE DOM K10 BASE CELLS CRED KONT.
  destruct c as [m n ix].
  destruct CELLS as (p1 & p2 & A11 & A12 & (P14 & AC1 & AG1 & SB1) & (P24 & AC2 & AG2 & SB2) & U1 & U2 & IX & RM & RN).
  cbn [PQMA.ms_mode PQMA.ms_len PQMA.ms_idx] in U1, U2, IX, RM, RN. subst ix.
  destruct PRE as [(V0 & V8' & V16 & -> & -> & -> & ->) | (VEC & ->)].
  - (* [comment removed for export] *)
    cbn [app] in HH.
    assert (CR : acredit_ok L cr 24).
    { pose proof (CRED (or_introl eq_refl)) as X. unfold PQSAXQ.k_next in X. cbn in X. exact X. }
    apply (PQAERE.empty L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr v sp r p1 p2 m n HH AM K0 ENT A10 AOV V8 ACCV V0 V8' V16
             A11 A12 P14 P24 SB1 SB2 AG1 AG2 U1 U2 RM RN CR BASE).
    intros fx' R' M' model' LK' Aw' b' RP VEC' ACC' BASE' HP MRT INC IA AM' HH'.
    apply (KONT fx' R' M' model' LK' Aw' b' 0 (adebit L cr 24) RP VEC' ACC' BASE'); try assumption.
    right. split; [left; reflexivity|]. split; reflexivity.
  - (* [comment removed for export] *)
    destruct DOM as [X | LT]; [unfold PQMA.mvec_own in X; discriminate X|].
    apply (PQAERF.fast L ar C HI LY HIok EXT fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 m n HH AM K0 ENT A10 AOV V8 ACCV VEC LT
             A11 A12 P14 P24 SB1 SB2 AG1 AG2 U1 U2 RM RN BASE).
    intros fx' R' M' model' LK' Aw' RP VEC' ACC' BASE' HP MRT INC IA AM' HH'.
    apply (KONT fx' R' M' model' LK' Aw' b k cr RP VEC' ACC' BASE'); try assumption.
    left. split; [unfold PQMA.mvec_own; discriminate|]. split; [exact LT|]. split; [reflexivity|]. split; reflexivity.
Qed.
End WithHeap.
End PQAER.

End PnAEmbR.
Module PnAPCtorPA.
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan Require XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.XIcptAs0Kit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0224. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0224.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAPCtorPA () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAl9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA8KS_qpcAlC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAh5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA6PqpcAh9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA8KS_qpcAhC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA5PqpcB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA5PqpcB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207:PnAPCtorPA7PQAPCPA7KS_qpcBC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAPCPA.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_158 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_159 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_160 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_161 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_162 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_163 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_164 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_165 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_166 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_167 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_168 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_169 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; byte_go.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
(* [comment removed for export] *)
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
(* [comment removed for export] *)
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          | |- L5KA.zeros_at _ ?a _ => lazymatch type of H with L5KA.zeros_at _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
(* [comment removed for export] *)
Local Ltac den_tac := first [reflexivity | lia | idtac].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.
(* [comment removed for export] *)
Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module PqpcAl := BndP_Na_143.LibSegNa_qpcAl.
Definition KS_qpcAl : list nat := Eval vm_compute in (BG.kept_list 60 PqpcAl.regs0 PqpcAl.regs_out0).
Lemma KS_qpcAl_ok : BG.kept_ok 60 PqpcAl.regs0 PqpcAl.regs_out0 KS_qpcAl = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_170 ())). Qed.
Lemma qpcAl_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 33%nat) - 496) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1376256 1409024 ->
  L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= ((V 33%nat) - 496) <= 2147445888 -> aligned ((V 33%nat) - 496) 8 ->
  (2147446784 + 17592186048512 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 2147446784) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= ((V 2%nat) - 4096)) -> (65536 + 6971392 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 65536) -> L5KA.zeros_at M ((((V 33%nat) - 496) / 8) + 2147450880) 34 ->
  aligned (V 33%nat) 8 -> L5.writable RSEGS M (V 33%nat) 400 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 50 -> 7036928 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 34%nat) \/ (V 34%nat) + 24 <= 65536) -> ((V 33%nat) + 400 <= (V 34%nat) \/ (V 34%nat) + 24 <= (V 33%nat)) -> L5.u64_at RSEGS M 1404312 1440376 -> L5.u64_at RSEGS M 1440376 2147450880 ->
  L5.u64_at RSEGS M 1404320 1443688 -> L5.u64_at RSEGS M 1443688 0 -> L5.u64_at RSEGS M 1404328 1443696 -> L5.u64_at RSEGS M 1443696 0 ->
  L5.u64_at RSEGS M 1404336 1443680 -> L5.u64_at RSEGS M 1443680 140737488355327 -> L5.u64_at RSEGS M 1407232 1443673 -> L5.u8_at RSEGS M 1443673 1 ->
  L5.u64_at RSEGS M 1412520 1347948 -> L5.u64_at RSEGS M 1412512 1346920 -> L5KA.zeros_at M 2147623322 64 -> L5KA.zeros_at M 2147625272 32 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 4096) <= bv_unsigned a < ((V 2%nat) - 4096) + 4096) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 400) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 4096) <= i < ((V 2%nat) - 4096) + 4096) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 400) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xceb7c M) (st fx' R' 0x11e2b8 M')
        /\ (forall x, In x KS_qpcAl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 849248
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 48)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 160)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 112)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 112) / 8) + 2147450880)
        /\ L5KA.zeros_at M' ((V 33%nat) + 168) 80
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 144) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 136) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 128) 6
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 120) 4098
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 152) ((V 33%nat) + 48)
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 148) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 40) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 112) 1380600
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 32) 1380560
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 160) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) - 496)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 33%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 847912
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) 846940
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 20) 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 16) 0
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 12) 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 9) 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ L5.u64_at RSEGS M' (V 33%nat) 1380328
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) [] (Mh_0207_blobs1.kr_b_171 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqpcAh := BndP_Na_143.LibSegNa_qpcAh.
Definition KS_qpcAh : list nat := Eval vm_compute in (BG.kept_list 60 PqpcAh.regs0 PqpcAh.regs_out0).
Lemma KS_qpcAh_ok : BG.kept_ok 60 PqpcAh.regs0 PqpcAh.regs_out0 KS_qpcAh = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_172 ())). Qed.
Lemma qpcAh_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 33%nat) - 496) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1376256 1409024 ->
  L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 17594333495296 <= ((V 33%nat) - 496) <= 140737488354423 -> aligned ((V 33%nat) - 496) 8 ->
  (2147446784 + 17592186048512 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 2147446784) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= ((V 2%nat) - 4096)) -> (65536 + 6971392 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 65536) -> L5KA.zeros_at M ((((V 33%nat) - 496) / 8) + 2147450880) 34 ->
  aligned (V 33%nat) 8 -> L5.writable RSEGS M (V 33%nat) 400 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 50 -> 7036928 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 34%nat) \/ (V 34%nat) + 24 <= 65536) -> ((V 33%nat) + 400 <= (V 34%nat) \/ (V 34%nat) + 24 <= (V 33%nat)) -> L5.u64_at RSEGS M 1404312 1440376 -> L5.u64_at RSEGS M 1440376 2147450880 ->
  L5.u64_at RSEGS M 1404320 1443688 -> L5.u64_at RSEGS M 1443688 0 -> L5.u64_at RSEGS M 1404328 1443696 -> L5.u64_at RSEGS M 1443696 0 ->
  L5.u64_at RSEGS M 1404336 1443680 -> L5.u64_at RSEGS M 1443680 140737488355327 -> L5.u64_at RSEGS M 1407232 1443673 -> L5.u8_at RSEGS M 1443673 1 ->
  L5.u64_at RSEGS M 1412520 1347948 -> L5.u64_at RSEGS M 1412512 1346920 -> L5KA.zeros_at M 2147623322 64 -> L5KA.zeros_at M 2147625272 32 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 4096) <= bv_unsigned a < ((V 2%nat) - 4096) + 4096) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 400) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 4096) <= i < ((V 2%nat) - 4096) + 4096) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 400) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xceb7c M) (st fx' R' 0x11e2b8 M')
        /\ (forall x, In x KS_qpcAh -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 849248
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 48)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 160)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 112)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 112) / 8) + 2147450880)
        /\ L5KA.zeros_at M' ((V 33%nat) + 168) 80
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 144) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 136) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 128) 6
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 120) 4098
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 152) ((V 33%nat) + 48)
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 148) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 40) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 112) 1380600
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 32) 1380560
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 160) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) - 496)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 33%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 847912
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) 846940
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 20) 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 16) 0
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 12) 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 9) 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ L5.u64_at RSEGS M' (V 33%nat) 1380328
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) [] (Mh_0207_blobs1.kr_b_173 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqpcB := BndP_Na_144.LibSegNa_qpcB.
Definition KS_qpcB : list nat := Eval vm_compute in (BG.kept_list 60 PqpcB.regs0 PqpcB.regs_out0).
Lemma KS_qpcB_ok : BG.kept_ok 60 PqpcB.regs0 PqpcB.regs_out0 KS_qpcB = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorPA ()) [] (Mh_0207_blobs1.kr_b_174 ())). Qed.
Lemma qpcB_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 48) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 112) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 112) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1376256 1409024 ->
  L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= ((V 33%nat) - 496) <= 140737488354424 -> aligned ((V 33%nat) - 496) 8 ->
  (2147446784 + 17592186048512 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 2147446784) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= ((V 2%nat) - 4096)) -> (65536 + 6971392 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 65536) -> L5KA.zeros_at M ((((V 33%nat) - 496) / 8) + 2147450880) 34 ->
  aligned (V 33%nat) 8 -> L5.writable RSEGS M (V 33%nat) 400 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 50 -> 7036928 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 34%nat) \/ (V 34%nat) + 24 <= 65536) -> ((V 33%nat) + 400 <= (V 34%nat) \/ (V 34%nat) + 24 <= (V 33%nat)) -> L5KA.zeros_at M 2147623322 64 -> L5KA.zeros_at M 2147625272 32 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) 846940 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) 847912 -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 33%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 24) ->
  L5.u64_at RSEGS M ((V 2%nat) - 160) ((V 33%nat) - 496) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) 2147450880 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 32) <= bv_unsigned a < ((V 33%nat) + 32) + 8) -> ~ (((V 33%nat) + 48) <= bv_unsigned a < ((V 33%nat) + 48) + 8) -> ~ (((V 33%nat) + 112) <= bv_unsigned a < ((V 33%nat) + 112) + 8) -> ~ (((V 33%nat) + 248) <= bv_unsigned a < ((V 33%nat) + 248) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 32) <= i < ((V 33%nat) + 32) + 8) -> ~ (((V 33%nat) + 48) <= i < ((V 33%nat) + 48) + 8) -> ~ (((V 33%nat) + 112) <= i < ((V 33%nat) + 112) + 8) -> ~ (((V 33%nat) + 248) <= i < ((V 33%nat) + 248) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcf560 M) (st fx' R' 0x11e2b8 M')
        /\ (forall x, In x KS_qpcB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 849380
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 56)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 33%nat) + 48) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 48) 1394840
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 112) 1380488
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 32) 1380448
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 256) 18446744073709551615
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 248) 0).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) [] (Mh_0207_blobs1.kr_b_175 ())). Qed.
(* [comment removed for export] *)

End PQAPCPA.

End PnAPCtorPA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require LeanFeed2. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0150.
Module PnAPCtor1.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0150. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0150.XIcptAs0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAPCtorStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAPCtorPA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAIss1.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan Require XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.XIcptAs0Kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAPCtor1 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula07I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9u8_at_visC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic2or00I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA:icl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA;aicl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA>aic_img_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5AFavis_of_shadow_allowedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib7Mh_00368AsanAcctAmrestrict_visibleC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02c69OSSVerify5KrLib7Mh_02079PnAPCtor16PQAPC1:img_sh_visC1?~~~~~~~~~~~~~~~".
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PQAPC1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma stack_zeros6 M sp : shadow_zero M (sp - 24576) 3072 -> sp mod 16 = 0 -> L5KA.zeros_at M (sp / 8 + 2147450368) 512.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtor1 ()) [] (Mh_0207_blobs1.kr_b_176 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma vis_u8 H M1 M1v a v : mrestrict H M1 = M1v -> L5A.avis H a 1 -> 0 <= a -> a < 2 ^ 63 -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtor1 ()) [] (Mh_0207_blobs1.kr_b_177 ())). Qed.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
(* [comment removed for export] *)
Let VPP : pa_vp_parser PMA.AD = 0x150fe8 := eq_refl.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma img_sh_vis LB FF LK cr Aw M model a n : ri_inv HI LB FF LK cr Aw M (vml_of model) ->
  0x10000 <= a -> a + n <= 0x6b6000 -> 0 < n -> a mod 8 = 0 -> n mod 8 = 0 ->
  Forall (fun r => a + n <= fst r \/ snd r <= a) [(0x23a40, 0x272a0); (0x151520, 0x1515a0); (0x15b8a0, 0x15c3a0)] ->
  L5KA.zeros_at (mrestrict (ahid Aw model) M) (a / 8 + 2147450880) (n / 8).
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_PnAPCtor1 ()) ["Stage"] (Mh_0207_blobs1.kr_b_178 ())). Qed.

Lemma img1 LB FF LK cr Aw M model : ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5KA.zeros_at (mrestrict (ahid Aw model) M) 2147623322 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtor1 ()) ["Stage"] (Mh_0207_blobs1.kr_b_179 ())). Qed.
Lemma img2 LB FF LK cr Aw M model : ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5KA.zeros_at (mrestrict (ahid Aw model) M) 2147625272 32.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtor1 ()) ["Stage"] (Mh_0207_blobs1.kr_b_180 ())). Qed.

Theorem head : PMA.locale_ctor_spec L ar HI ->
  forall (fx : FPState) R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo,
    PQAPCS.pre L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo ->
    (forall (fx1 : FPState) R1 M1 model1 LK1 Aw1, PQAPCS.rmid1 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr sp fb oo R1 M1 model1 LK1 Aw1 ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx1) R1 0xcf5e4 M1 model1) K) ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R0 0xceb7c M0 model0) K.
Proof.
Ltac t64 AG V VIS X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")|];
                            apply (PMAIS1.vis_u64 _ _ _ _ _ VIS); [apply V; (lia || fail 1 "V") | (lia || fail 1 "B3") | (lia || fail 1 "B4") | exact X].
Ltac t32 AG V VIS X Ms := apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG32")| (lia || fail 1 "C1")| (lia || fail 1 "C2")|];
                            apply (PMAIS1.vis_u32 _ _ _ _ _ VIS); [apply V; (lia || fail 1 "V32") | (lia || fail 1 "C3") | (lia || fail 1 "C4") | exact X].
Ltac t8 AG V VIS X Ms := apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG8")| (lia || fail 1 "E1")| (lia || fail 1 "E2")|];
                           apply (vis_u8 _ _ _ _ _ VIS); [apply V; (lia || fail 1 "V8") | (lia || fail 1 "E3") | (lia || fail 1 "E4") | exact X].
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) ["Stage"] (Mh_0207_blobs2.kr_b_181 ())). Qed.

End Stage.
End PQAPC1.

End PnAPCtor1.
From stdpp Require base list.
Module PnAPCtorKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0150. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunHA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0150.XIcptAs0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAIss1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAPCtorStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAPCtor1.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan Require XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.XIcptAs0Kit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5CoreB.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAPCtorKit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA9frame_okMC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z<divide_transK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8vis_packC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u64_at_visC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib5Lists4List2hdc69OSSVerify5KrLib7Mh_0207;PnAPCtorKit6PQAPCK4fb16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0207;PnAPCtorKit6PQAPCK:frame_aobjC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA=aobj_of_aobjAC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:aobj_factsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8avis_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4aobjC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM8zeros_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;aior_memsetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<amemset_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_segsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:hl_scr_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9astack_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8aclientwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>hl_asan_memsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8aly_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_memsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A;aly_scr_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib7Mh_00385Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARAastack_ok_of_astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_rt_roC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:obj_clientC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<app_rng_aobjC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ?model_rt_haltedC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6ek_memC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR7rng_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or02C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6dk_memC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<stack_clientC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=astk_after_eqC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List7map_appC35stdpp4base7elem_ofC47Corelib4Init5Logic3iffC47Corelib4Init5Logic6or_indC47Corelib4Init9Datatypes8prod_indK46Stdlib7Sorting;Permutation;Permutation03I46Stdlib7Sorting;Permutation;Permutation00C45stdpp>list_relations4listHNoDup_Permutation_properC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9MorphismsFsubrelation_respectfulC45stdpp>list_relations4list9NoDup_appC69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ9aior_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5cost1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6adebitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA7ly_costC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_b_linC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=hl_b_overheadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:acredit_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA@hl_aligned_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_K0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_B0C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00849HeapIface;heap_layout01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS4costC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5CHUNKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_parserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_nullisC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_nullbufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_classic_impC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout@pa_vp_nullis_iosC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02147L5CoreB4L5CB8aacc_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM5srcst01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_qcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_deC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6sr_remC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6p_moreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6p_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7p_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5p_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_tbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_bbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4PgV84PGV85v8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_sbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4p_skC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5p_stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7mvec_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnRunHA5PQRHA<mparser_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0247=PnAPCtorStmts6PQAPCS:mparser_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM9nullis_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM=src_fields_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vstr_atC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4mpst01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4PgV84PGV82v801C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6mstate00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7ms_rootC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5PSIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7OFF_SRCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8OFF_MAXDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6OFF_TBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6OFF_BBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7OFF_STKC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PQAPCK.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.

Section Kit.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma frame_aobj FF fb a n : PQRA.frame_okM FF fb -> fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorKit ()) ["Kit"] (Mh_0207_blobs2.kr_b_182 ())). Qed.
Lemma fb16 FF fb : PQRA.frame_okM FF fb -> fb mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorKit ()) ["Kit"] (Mh_0207_blobs2.kr_b_183 ())). Qed.

(* [comment removed for export] *)
Lemma vfacts LB FF LK cr Aw M model sp fb oo :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PQRA.frame_okM FF fb -> L5CA.astk ar M sp 24576 -> PMSPA.aobjA FF oo 24 -> oo mod 8 = 0 ->
  PMSPA.accA M (fb + 592) 400 -> PMSPA.accA M (fb + 96) 272 -> PMSPA.accA M oo 24 -> L5.defined M (fb + 592) 400 ->
  let MV := mrestrict (ahid Aw model) M in
  L5.writable RSEGS MV (sp - 4096) 4096 /\ L5.img_clear MV 1376256 1409024 /\ L5.u64_at RSEGS MV 1440376 2147450880 /\ L5.u32_at RSEGS MV 1440384 1
  /\ L5KA.zeros_at MV ((fb + 592 - 496) / 8 + 2147450880) 34 /\ L5KA.zeros_at MV (oo / 8 + 2147450880) 3
  /\ L5.writable RSEGS MV (fb + 592) 400 /\ L5KA.zeros_at MV ((fb + 592) / 8 + 2147450880) 50
  /\ L5KA.zeros_at MV 2147623322 64 /\ L5KA.zeros_at MV 2147625272 32
  /\ 7036928 <= fb + 96 /\ fb + 2048 + 4096 + 24576 <= sp /\ (2147446784 + 17592186048512 <= fb + 96 \/ fb + 992 <= 2147446784)
  /\ fb mod 16 = 0 /\ fb + 2048 <= 2 ^ 47
  /\ 7036928 <= oo /\ oo + 24 + 4096 + 24576 <= sp /\ (2147446784 + 17592186048512 <= oo \/ oo + 24 <= 2147446784) /\ oo + 32 <= 2 ^ 47.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) ["Kit"] (Mh_0207_blobs2.kr_b_184 ())). Qed.

(* [comment removed for export] *)
Lemma svis LB FF LK cr Aw M model sp a v :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.astk ar M sp 24576 -> sp - 4096 <= a -> a + 8 <= sp ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS (mrestrict (ahid Aw model) M) a v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorKit ()) ["Kit"] (Mh_0207_blobs2.kr_b_185 ())). Qed.
Lemma fvis LB FF LK cr Aw M model fb a v :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PQRA.frame_okM FF fb -> fb + 32 <= a -> a + 8 <= fb + 2040 ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS (mrestrict (ahid Aw model) M) a v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorKit ()) ["Kit"] (Mh_0207_blobs2.kr_b_186 ())). Qed.

(* [comment removed for export] *)
Lemma amset LB FF LK cr Aw sp fr o sz (fx0 : FPState) Ra Ma modela Kc d n ra :
  L5CA.aobj FF o sz -> 0 <= d -> d + n <= sz -> 0 < n <= 96 ->
  ri_inv HI LB FF LK cr Aw Ma (vml_of modela) -> L5CA.amodel_ok Aw modela -> L5CA.astk ar Ma sp 24576 -> PMSPA.accA Ma o sz -> L5.defined Ma o sz ->
  0 <= fr -> fr + 2560 <= 24576 -> (sp - fr) mod 16 = 0 ->
  getr Ra (reg 10) = Z_to_bv 64 (o + d) -> getr Ra (reg 11) = Z_to_bv 64 0 -> getr Ra (reg 12) = Z_to_bv 64 n -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr Ra (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 -> getr Ra (reg 2) = Z_to_bv 64 (sp - fr) -> Kc [] ->
  (forall Rb Mb modelb, getr Rb (reg 10) = Z_to_bv 64 (o + d) -> regs_preserved Ra Rb -> PM.zeros_at Mb (o + d) n ->
     (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - fr) 2560 a -> ~ (o + d <= a < o + d + n) -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
     (forall a, sp - fr - 2560 <= a < sp - fr -> Mb (Z_to_bv 64 a) <> None) ->
     L5.defined Mb (o + d) n -> model_rt modela modelb -> L5CA.amodel_ok Aw modelb -> ri_inv HI LB FF LK cr Aw Mb (vml_of modelb) ->
     srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx0) Rb ra Mb modelb) Kc) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx0) Ra 0x7f058 Ma modela) Kc.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorKit ()) ["Kit"] (Mh_0207_blobs2.kr_b_187 ())). Qed.

(* [comment removed for export] *)
Lemma mset_post LB FF LK cr Aw sp fr o sz Ma Mb modela d n :
  ri_inv HI LB FF LK cr Aw Ma (vml_of modela) -> L5CA.astk ar Ma sp 24576 -> L5CA.aobj FF o sz -> 0 <= fr -> fr + 2560 <= 24576 -> 0 <= d -> d + n <= sz ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - fr) 2560 a -> ~ (o + d <= a < o + d + n) -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  (forall a, sp - fr - 2560 <= a < sp - fr -> Mb (Z_to_bv 64 a) <> None) -> L5.defined Mb (o + d) n ->
  L5SAR.ek L ar LB FF sp 24576 [(o, sz)] Ma Mb /\ L5SAR.dk L ar LB FF sp 24576 Ma Mb /\ L5CA.astk ar Mb sp 24576.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorKit ()) ["Kit"] (Mh_0207_blobs2.kr_b_188 ())). Qed.
(* [comment removed for export] *)
Lemma ri_swap12 x y l FF LK cr Aw M V : ri_inv HI (x :: y :: l) FF LK cr Aw M V -> ri_inv HI (y :: x :: l) FF LK cr Aw M V.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorKit ()) ["Kit"] (Mh_0207_blobs2.kr_b_189 ())). Qed.

(* [comment removed for export] *)
Lemma rd_credit cr : PMSP.credit_le (PQAPCS.cost L ar) cr ->
  acredit_ok L cr 16384 /\ acredit_ok L (adebit L cr 16384) 24 /\ PMSP.credit_keep cr (adebit L (adebit L cr 16384) 24) (PQAPCS.cost L ar) (PMSPA.scA L PMSP.cr0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorKit ()) ["Kit"] (Mh_0207_blobs2.kr_b_190 ())). Qed.

(* [comment removed for export] *)
Lemma mparser_init_at M op ois q b :
  L5.u64_at RSEGS M op (pa_vp_parser PMA.AD) -> L5.defined M op 400 -> PMSPA.accA M op 400 ->
  L5.u8_at RSEGS M (op + 8) 1 -> L5.u8_at RSEGS M (op + 9) 0 -> L5.u32_at RSEGS M (op + 12) 0 -> L5.u8_at RSEGS M (op + 16) 0 -> L5.u32_at RSEGS M (op + 20) 0 ->
  L5.u64_at RSEGS M (op + 32) (pa_vp_nullis PMA.AD) -> L5.u64_at RSEGS M (op + 48) (pa_vp_nullbuf PMA.AD) -> L5.u64_at RSEGS M (op + 56) (pa_classic_imp PMA.AD) ->
  L5.u64_at RSEGS M (op + 112) (pa_vp_nullis_ios PMA.AD) -> L5.u32_at RSEGS M (op + 144) 0 -> L5.u32_at RSEGS M (op + 148) 0 -> L5.u64_at RSEGS M (op + 152) (op + 48) ->
  L5.u64_at RSEGS M (op + 160) (pa_classic_imp PMA.AD) -> PM.zeros_at M (op + 168) 80 ->
  L5.u64_at RSEGS M (op + 264) ois -> L5.u64_at RSEGS M (op + 272) (ois + 16) -> L5.u64_at RSEGS M (op + 288) q -> L5.u64_at RSEGS M (op + 296) PM.CHUNK ->
  L5.u64_at RSEGS M (op + 304) q -> L5.u64_at RSEGS M (op + 312) 0 ->
  q mod 16 = 0 -> L5.defined M q PM.CHUNK -> PMSPA.accA M q PM.CHUNK ->
  L5.u32_at RSEGS M (op + 320) 1024 ->
  L5.u8_at RSEGS M (op + 328) 0 ->
  L5.u64_at RSEGS M (op + 352) 0 -> L5.u64_at RSEGS M (op + 360) 0 -> L5.u64_at RSEGS M (op + 368) 0 ->
  PQMA.mvec_at RSEGS PMSPA.accA PMSPA.annA M (op + 376) b 0 [PQMA.ms_root] -> 0 <= op -> op + 400 <= 2 ^ 64 ->
  PQAPCS.mparser_at M op ois (PQRHA.mparser_init q b).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorKit ()) ["Kit"] (Mh_0207_blobs2.kr_b_191 ())). Qed.
End Kit.
End PQAPCK.

End PnAPCtorKit.
Module PnAPCtorP.
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan Require XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.XIcptAs0Kit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0224. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0224.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAPCtorP () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcC9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcCC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transK46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcC<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcC3NX0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS09fill_specC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS09copy_specC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS08tls_specC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcC3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcC3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP:KS_qpcC_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcD9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcDC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcD<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcD3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP:KS_qpcD_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcD6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcE9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcEC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcE<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcE3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP:KS_qpcE_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcE6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcF9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcF<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcF3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP:KS_qpcF_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcG9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcGC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcG<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP>u32_of_KWord4aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcG3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP:KS_qpcG_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcG6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcH5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcH9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcHC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcH<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcH3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcH2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcH3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcH3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcH3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP:KS_qpcH_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcH6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcZ9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP7KS_qpcZC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcZ<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcZ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP5PqpcZ3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02079PnAPCtorP6PQAPCP:KS_qpcZ_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAPCP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_192 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_193 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_194 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_195 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_196 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_197 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_198 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_199 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_200 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_201 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_202 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_203 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; byte_go.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
(* [comment removed for export] *)
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
(* [comment removed for export] *)
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          | |- L5KA.zeros_at _ ?a _ => lazymatch type of H with L5KA.zeros_at _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
(* [comment removed for export] *)
Local Ltac den_tac := first [reflexivity | lia | idtac].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.
(* [comment removed for export] *)
Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module PqpcC := BndP_Na_144.LibSegNa_qpcC.
Definition KS_qpcC : list nat := Eval vm_compute in (BG.kept_list 60 PqpcC.regs0 PqpcC.regs_out0).
Lemma KS_qpcC_ok : BG.kept_ok 60 PqpcC.regs0 PqpcC.regs_out0 KS_qpcC = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_204 ())). Qed.
Lemma qpcC_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 48) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 112) -> getr R (reg 19) = Z_to_bv 64 ((((V 33%nat) + 48) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 112) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1376256 1409024 ->
  L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= ((V 33%nat) - 496) <= 140737488354424 -> aligned ((V 33%nat) - 496) 8 ->
  (2147446784 + 17592186048512 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 2147446784) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= ((V 2%nat) - 4096)) -> (65536 + 6971392 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 65536) -> L5KA.zeros_at M ((((V 33%nat) - 496) / 8) + 2147450880) 34 ->
  aligned (V 33%nat) 8 -> L5.writable RSEGS M (V 33%nat) 400 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 50 -> 7036928 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 34%nat) \/ (V 34%nat) + 24 <= 65536) -> ((V 33%nat) + 400 <= (V 34%nat) \/ (V 34%nat) + 24 <= (V 33%nat)) -> L5KA.zeros_at M 2147623322 64 -> L5KA.zeros_at M 2147625272 32 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) 846940 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) 847912 -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 33%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 24) ->
  L5.u64_at RSEGS M ((V 2%nat) - 160) ((V 33%nat) - 496) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) 2147450880 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcf5e4 M) (st fx' R' 0x7f058 M')
        /\ (forall x, In x KS_qpcC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 849396
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 64)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 48).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_205 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqpcD := BndP_Na_144.LibSegNa_qpcD.
Definition KS_qpcD : list nat := Eval vm_compute in (BG.kept_list 60 PqpcD.regs0 PqpcD.regs_out0).
Lemma KS_qpcD_ok : BG.kept_ok 60 PqpcD.regs0 PqpcD.regs_out0 KS_qpcD = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_206 ())). Qed.
Lemma qpcD_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 48) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 112) -> getr R (reg 19) = Z_to_bv 64 ((((V 33%nat) + 48) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 112) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1376256 1409024 ->
  L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= ((V 33%nat) - 496) <= 140737488354424 -> aligned ((V 33%nat) - 496) 8 ->
  (2147446784 + 17592186048512 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 2147446784) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= ((V 2%nat) - 4096)) -> (65536 + 6971392 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 65536) -> L5KA.zeros_at M ((((V 33%nat) - 496) / 8) + 2147450880) 34 ->
  aligned (V 33%nat) 8 -> L5.writable RSEGS M (V 33%nat) 400 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 50 -> 7036928 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 34%nat) \/ (V 34%nat) + 24 <= 65536) -> ((V 33%nat) + 400 <= (V 34%nat) \/ (V 34%nat) + 24 <= (V 33%nat)) -> L5KA.zeros_at M 2147623322 64 -> L5KA.zeros_at M 2147625272 32 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) 846940 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) 847912 -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 33%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 24) ->
  L5.u64_at RSEGS M ((V 2%nat) - 160) ((V 33%nat) - 496) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) 2147450880 ->
  L5.u64_at RSEGS M ((V 33%nat) - 496) 1395208 -> L5.u64_at RSEGS M ((V 33%nat) - 336) ((V 33%nat) - 480) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 48) <= bv_unsigned a < ((V 33%nat) + 48) + 8) -> ~ (((V 33%nat) + 264) <= bv_unsigned a < ((V 33%nat) + 264) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 48) <= i < ((V 33%nat) + 48) + 8) -> ~ (((V 33%nat) + 264) <= i < ((V 33%nat) + 264) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcf5f4 M) (st fx' R' 0x7f058 M')
        /\ (forall x, In x KS_qpcD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 848052
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 280)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 296)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 272) ((V 33%nat) - 480)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 264) ((V 33%nat) - 496)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 48) 1381232).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_207 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqpcE := BndP_Na_144.LibSegNa_qpcE.
Definition KS_qpcE : list nat := Eval vm_compute in (BG.kept_list 60 PqpcE.regs0 PqpcE.regs_out0).
Lemma KS_qpcE_ok : BG.kept_ok 60 PqpcE.regs0 PqpcE.regs_out0 KS_qpcE = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_208 ())). Qed.
Lemma qpcE_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 296) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1376256 1409024 ->
  L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= ((V 33%nat) - 496) <= 140737488354424 -> aligned ((V 33%nat) - 496) 8 ->
  (2147446784 + 17592186048512 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 2147446784) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= ((V 2%nat) - 4096)) -> (65536 + 6971392 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 65536) -> L5KA.zeros_at M ((((V 33%nat) - 496) / 8) + 2147450880) 34 ->
  aligned (V 33%nat) 8 -> L5.writable RSEGS M (V 33%nat) 400 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 50 -> 7036928 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 34%nat) \/ (V 34%nat) + 24 <= 65536) -> ((V 33%nat) + 400 <= (V 34%nat) \/ (V 34%nat) + 24 <= (V 33%nat)) -> L5KA.zeros_at M 2147623322 64 -> L5KA.zeros_at M 2147625272 32 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) 846940 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 47%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 296) <= bv_unsigned a < ((V 33%nat) + 296) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 296) <= i < ((V 33%nat) + 296) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcf0b4 M) (st fx' R' 0x7f058 M')
        /\ (forall x, In x KS_qpcE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 848096
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 304)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 304)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 296) 16384).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_209 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqpcF := BndP_Na_145.LibSegNa_qpcF.
Definition KS_qpcF : list nat := Eval vm_compute in (BG.kept_list 60 PqpcF.regs0 PqpcF.regs_out0).
Lemma KS_qpcF_ok : BG.kept_ok 60 PqpcF.regs0 PqpcF.regs_out0 KS_qpcF = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_210 ())). Qed.
Lemma qpcF_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 304) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcf0e0 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_qpcF -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 848104
        /\ getr R' (reg 10) = Z_to_bv 64 16384).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_211 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqpcG := BndP_Na_145.LibSegNa_qpcG.
Definition KS_qpcG : list nat := Eval vm_compute in (BG.kept_list 60 PqpcG.regs0 PqpcG.regs_out0).
Lemma KS_qpcG_ok : BG.kept_ok 60 PqpcG.regs0 PqpcG.regs_out0 KS_qpcG = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_212 ())). Qed.
Lemma qpcG_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 304) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1376256 1409024 ->
  L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= ((V 33%nat) - 496) <= 140737488354424 -> aligned ((V 33%nat) - 496) 8 ->
  (2147446784 + 17592186048512 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 2147446784) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= ((V 2%nat) - 4096)) -> (65536 + 6971392 <= ((V 33%nat) - 496) \/ ((V 33%nat) - 496) + 896 <= 65536) -> L5KA.zeros_at M ((((V 33%nat) - 496) / 8) + 2147450880) 34 ->
  aligned (V 33%nat) 8 -> L5.writable RSEGS M (V 33%nat) 400 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 50 -> 7036928 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6971392 <= (V 34%nat) \/ (V 34%nat) + 24 <= 65536) -> ((V 33%nat) + 400 <= (V 34%nat) \/ (V 34%nat) + 24 <= (V 33%nat)) -> L5KA.zeros_at M 2147623322 64 -> L5KA.zeros_at M 2147625272 32 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) 846940 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 47%nat) -> L5.u64_at RSEGS M (V 34%nat) 1379592 -> L5.u32_at RSEGS M ((V 34%nat) + 16) 1024 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 288) <= bv_unsigned a < ((V 33%nat) + 288) + 8) -> ~ (((V 33%nat) + 304) <= bv_unsigned a < ((V 33%nat) + 304) + 8) -> ~ (((V 33%nat) + 320) <= bv_unsigned a < ((V 33%nat) + 320) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 288) <= i < ((V 33%nat) + 288) + 8) -> ~ (((V 33%nat) + 304) <= i < ((V 33%nat) + 304) + 8) -> ~ (((V 33%nat) + 320) <= i < ((V 33%nat) + 320) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcf0e8 M) (st fx' R' 0x7f058 M')
        /\ (forall x, In x KS_qpcG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 847060
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 328)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 72
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 328)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 33%nat) + 376)
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 320) 1024
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 304) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 288) (V 35%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_213 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqpcH := BndP_Na_145.LibSegNa_qpcH.
Definition KS_qpcH : list nat := Eval vm_compute in (BG.kept_list 60 PqpcH.regs0 PqpcH.regs_out0).
Lemma KS_qpcH_ok : BG.kept_ok 60 PqpcH.regs0 PqpcH.regs_out0 KS_qpcH = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_214 ())). Qed.
Lemma qpcH_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 328) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 376) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 76) <= bv_unsigned a < ((V 2%nat) - 76) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 76) <= i < ((V 2%nat) - 76) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcecd4 M) (st fx' R' 0xcf178 M')
        /\ (forall x, In x KS_qpcH -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 847084
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 376)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 72)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 76)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 76) 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 72) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_215 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqpcZ := BndP_Na_145.LibSegNa_qpcZ.
Definition KS_qpcZ : list nat := Eval vm_compute in (BG.kept_list 60 PqpcZ.regs0 PqpcZ.regs_out0).
Lemma KS_qpcZ_ok : BG.kept_ok 60 PqpcZ.regs0 PqpcZ.regs_out0 KS_qpcZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_216 ())). Qed.
Lemma qpcZ_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xcecec M) (st fx' R' 0xced10 M')
        /\ (forall x, In x KS_qpcZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtorP ()) [] (Mh_0207_blobs2.kr_b_217 ())). Qed.
(* [comment removed for export] *)

End PQAPCP.

End PnAPCtorP.
Module PnAPCtor2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0150. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0150.XIcptAs0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAPCtorStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAPCtorP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAIss1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAPCtor1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAPCtorKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan Require XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.XIcptAs0Kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PQAPC2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Theorem memsets : forall (fx : FPState) R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo R1 M1 model1 LK1 Aw1,
    PQAPCS.pre L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo ->
    PQAPCS.rmid1 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr sp fb oo R1 M1 model1 LK1 Aw1 ->
    (forall (fx2 : FPState) R2 M2 model2 LK2 Aw2, PQAPCS.rmid2 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr sp fb oo R2 M2 model2 LK2 Aw2 ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xcf0e0 M2 model2) K) ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R1 0xcf5e4 M1 model1) K.
Proof.
Ltac a64 AG X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
Ltac a32 AG X Ms := apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
Ltac a8 AG X Ms := apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) ["Stage"] (Mh_0207_blobs2.kr_b_218 ())). Qed.
End Stage.
End PQAPC2.

End PnAPCtor2.
Module PnAPCtor3.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0150. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunHA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAXq OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0150.XIcptAs0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAPCtorStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAPCtorP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnAIss1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAPCtor1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0207.PnAPCtorKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012.Na0_code_rc1d78_c1d7c.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan Require XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.XIcptAs0Kit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0214.L5CoreB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAPCtor3 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00".
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PQAPC3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma shz_at (M : word -> option byte) lo g p : shadow_zero M lo g -> lo mod 8 = 0 -> lo <= p -> p < lo + 8 * g -> byte_at M (S p) 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAPCtor3 ()) [] (Mh_0207_blobs2.kr_b_219 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Theorem tail : PMA.opnew_spec L ar HI -> PQSAXQ.push_root_spec RSEGS PMA.AD L ar HI 0xcf178 ->
  forall (fx : FPState) R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo R1 M1 model1 LK1 Aw1,
    PQAPCS.pre L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb oo ->
    PQAPCS.rmid2 L ar HI R0 M0 model0 LB FF LK0 Aw0 cr sp fb oo R1 M1 model1 LK1 Aw1 ->
    PQAPCS.kont L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr sp r fb ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R1 0xcf0e0 M1 model1) K.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac a64 AG X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
Ltac a32 AG X Ms := apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
Ltac a8 AG X Ms := apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")| exact X].
ltac2:(KReplay.run1 (kr_tL_Mh_0207 ()) ["Stage"] (Mh_0207_blobs2.kr_b_220 ())). Qed.
End Stage.
End PQAPC3.

End PnAPCtor3.
