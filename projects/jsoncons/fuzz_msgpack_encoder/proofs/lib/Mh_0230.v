(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Mh_0230_blobs1.
(* [comment removed for export] *)
Set Warnings "-require-in-module".
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0175. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0230 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2tlC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums1Z03I46Stdlib9micromega7EnvRing5PExpr00I46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init5Peano2ltK46Stdlib9micromega=RingMicromega5Psatz02C56Stdlib6ZArith6BinInt1Z3addK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing5PExpr05C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z6moduloK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00I46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega:ZMicromega=Zeval_formulaC46Stdlib9micromega5Tauto7eval_bfC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC47Corelib4Init5Logic3notK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega6VarMap1t01I47Corelib4Init5Logic3and00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z9mod_smallC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2eq00c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3addC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrQ<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z<eq_decidableC69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1>u8_of_KWord1maC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C56Stdlib6ZArith6BinInt1Z6of_natK46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega6VarMap1t02C46Stdlib9micromega6VarMap4findK46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I46Stdlib9micromega:ZMicromega;ZArithProof00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrQ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrQ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrQ3NX0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrQ9regs_out0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltc79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrQ6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums8positive00K4ELinuxProcessSemantics5Riscv5Instr5aluop07I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrQ5regs0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrQ3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17KS_qvrQC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrQ3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1:KS_qvrQ_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7=word_of_zpolyC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77PqvrDb2<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77PqvrDb23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77PqvrDb22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77PqvrDb23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77PqvrDb29regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77PqvrDb26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77PqvrDb25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77PqvrDb23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP79KS_qvrDb2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77PqvrDb23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7<KS_qvrDb2_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdL2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdL23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdL22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdL23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdL29regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdL26cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdL25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdL23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7:KS_qvrKdL2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdL23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7=KS_qvrKdL2_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA4PMEAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8pot_encAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA6b64lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;pot_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbK69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6kbsizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxK45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6kbsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5wappWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_WAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4EVISC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR4OWNEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5own13C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3nlvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ndestC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7pot_aeAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5a_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_applC69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6edepthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5xinvGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3ESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_pfactsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR4valsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG37bvu_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP19qvrQ_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02567PmAUarK5PMAUK5WretXC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7enc_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8sink_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ec_stateAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092;PnQStaticsA5PQSTA7err_okAC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6frb_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6brb_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38aobj_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA8xinv_ekFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5zsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3phiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR9pot_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_finC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3IXAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5VIS_HC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR4QENNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5V2_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3Hh3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3OCEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5HSPCfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb6494_b64987W_b6350C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb6494_b64987F_b6350C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb6494_b64987D_b6350C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_KBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR7oa_lo96C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP68PQAABRP67alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4ea_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_binC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5lv_eoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_tC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_kC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR2XVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_oaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7alvl_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA3agAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275<PnAKSlotA3bN8PQAKS3BN4s_pvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N7s_oa_shC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP68PQAABRP6:qvrDa_concC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7;qvrDb2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG38regl_subC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8view_okAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3xvFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8avis_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u64_at_visC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9u8_at_visC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02567PmAUarK5PMAUK4gctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7cell_isC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan;L5ADetailHR6L5ADHR:byte_of_u8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02568PnAKRunF6PQAKRF:aacc_localC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR9aacc_joinC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK=blk_obj_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK7blk_imgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA7agA_subC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA:accA_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02566PmAUar6PMAUAR:aobjA_pushC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA?v_bstr_raw_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA:aargs_bstrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR;hdr_bin_le5C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8pre_viewC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9step_viewC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1:qvrJ1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR:b64len_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3ADVC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA:fobj_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA8s_xpieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7s_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ENC_SLOTAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR2IXC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ENC_HC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR7oec_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR8ov_rng56C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR6tg_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP68PQAABRP68KS_qvrDaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR4VOKfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR8DKB_DPHIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP18KS_qvrJ1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR9DKB_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP47alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_visitorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lvec_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5asciiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO7aown_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO8aown_keyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR:mem_eq_frzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR8INS_CALLC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4<qvrIVSS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR6div2_2C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4<qvrIVSL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4<qvrIVLS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4<qvrIVLL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4<qvrIKSS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4<qvrIKSL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4<qvrIKLS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4<qvrIKLL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_kstrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3IXBC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_DVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA9AOFF_DESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8AOFF_KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_LVC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIVSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIVSLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIVLSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIVLLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIKSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIKSLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIKLSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIKLLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ea_bsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA8s_kpieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR8aacc_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA:v_key_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA9aargs_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC:ascii_utf8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pre_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8step_keyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1:qvrKr_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7<qvrKdS2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7<qvrKdL2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ENC_HSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4KCAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP18KS_qvrKrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7:KS_qvrKdS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N4kclrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_restC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N9s_own_neqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7src_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_kbgC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5s_xkwC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N9kclr_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR6xv_ptwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275<PnAKSlotA3bN8PQAKS3BN:s_view_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275<PnAKSlotA3bN8PQAKS3BN9b64_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275<PnAKSlotA3bN8PQAKS3BN7b64_scEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_xcallC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5DISP2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N7s_kclrXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2<qvrKe0S_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A<writable_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2<qvrKe0L_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2<qvrKe1S_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2<qvrKe1L_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_setC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0275<PnAKSlotA3bN8PQAKS3BN9s_call_sEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;s_own_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5B64_HC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR6pv_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2:KS_qvrKe0SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2:KS_qvrKe0LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2:KS_qvrKe1SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2:KS_qvrKe1LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK8mach_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR39stk_w_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1:qvrA0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5xv_ekC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5SETUPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8s_enterXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1;qvrA16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5xinv0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR2CRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5GOWNEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP18KS_qvrA0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP19KS_qvrA16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3xv0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_rt_roC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP7alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6pot_ksC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC14stokC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC15kept0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC15savesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC16mem_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC16bfactsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC16vfactsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC19saves_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA=aobj_of_aobjAC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4aobjC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=astk_writableC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangec69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP:qspTS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC16sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP9qspT_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8aclientwC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:obj_clientC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<block_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC19regs_backC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02478PnARzKit6PMARZK:agsh_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC17kc_snocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAReset16PMARS1?own_not_aclientC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_pieceC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:astk_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8dk_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8dk_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9ahpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ>model_rt_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6apieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP8KS_qspTSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP7KS_qspTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rd36f8_d36fc7W_f4720C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rd36f8_d36fc7F_f4720C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_rd36f8_d36fc7D_f4720C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC13KCFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6adebitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP9qspD_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib6ZArith6BinInt1Z7mod_addC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8astk_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA:opdel_specC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9ek_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA9wapp_consC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<stack_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC1:saves_keepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9dk_calleeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=astk_after_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA:acc_keepA'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02478PnARzKit6PMARZK;agsh_ahpresC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC14tailC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9apiece_roC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA5akeptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP7KS_qspDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA9OPDEL_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P7alignedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8ks_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_b_linC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P:qspS2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9even_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=aclient_casesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP:qspGS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC18saves_ofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC1<mem_ok_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC1:grow_shortC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF8odd_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowc69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC17wrap_neC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP:qspLI_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8add_commC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_appbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC17wrap_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP:qspLG_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv=Z_div_exact_2C56Stdlib6ZArith6BinInt1Z9div_add_lC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF4lor7C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5max_lc69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC16newcntC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC15half2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA6gcountC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC19grow_longC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4GMAXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP8KS_qspGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00c69OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P8KS_qspS2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP8KS_qspLIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP8KS_qspLGC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op206c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P67alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdS2<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdS23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdS29regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdS26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdS23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6:KS_qvuKdS2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdS23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6=KS_qvuKdS2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdL2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdL23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdL22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdL23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdL29regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdL26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdL25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdL23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6:KS_qvuKdL2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdL23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6=KS_qvuKdL2_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA4ndigC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU64OWNEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU63ESTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU64valsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P19qvuQ_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU69pot_splitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU63OCEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU65HSPCfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU63IXAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8TAG_ESECC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU64QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU68sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU65V2_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17KS_qvuQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb1aac_b1ab07W_b1968C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb1aac_b1ab07F_b1968C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0016ENa0_code_rb1aac_b1ab07D_b1968C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU67oa_lo96C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P47alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU6:mem_eq_frzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU68INS_CALLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4<qvuIVSS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU66div2_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4<qvuIVSL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4<qvuIVLS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4<qvuIVLL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4<qvuIKSS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4<qvuIKSL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4<qvuIKLS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4<qvuIKLL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU62IXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIVSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIVSLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIVLSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIVLLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIKSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIKSLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIKLSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIKLLC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8leb_specC69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF38ndig_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU69aacc_joinC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU68aacc_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1:qvuKr_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU63ADVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6<qvuKdS2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6<qvuKdL2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU67oec_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU68ov_rng56C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU67DU_DPHIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P18KS_qvuKrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P27alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA;from_argsCQC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9from_scCQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU65DISP2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2<qvuKe0S_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2<qvuKe0L_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2<qvuKe1S_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2<qvuKe1L_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA:s_call_sCQC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA6FROM_HC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2:KS_qvuKe0SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2:KS_qvuKe0LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2:KS_qvuKe1SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2:KS_qvuKe1LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P19qvuB_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU65DISP1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17KS_qvuBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1:qvuA0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU65SETUPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1;qvuA16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU65xinv0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU62CRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU65GOWNEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P18KS_qvuA0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P19KS_qvuA16C1?~~~~~~~~~~~~~~~".
Module PnAAdBrP1.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0175. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0175 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdBrP1 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrA09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP18KS_qvrA0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrA0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrA03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrA06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrA03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrA03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1;KS_qvrA0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17PqvrA165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17PqvrA169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP19KS_qvrA16C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17PqvrA16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17PqvrA163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17PqvrA162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17PqvrA163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17PqvrA166cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17PqvrA163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17PqvrA163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1<KS_qvrA16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17KS_qvrBC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z<eq_decidableK46Stdlib9micromega=RingMicromega5Psatz07C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrB<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1>u8_of_KWord1maC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrB6cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1:KS_qvrB_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrQ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP15PqvrQ9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17KS_qvrQC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrJ15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrJ19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP18KS_qvrJ1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrJ1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrJ13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrJ12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrJ13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrJ13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrJ13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1;KS_qvrJ1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrJ16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrKr5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrKr9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP18KS_qvrKrC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrKr<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrKr3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrKr2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrKr3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrKr3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrKr3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP1;KS_qvrKr_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP16PqvrKr6cells0C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAABRP1.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_001 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_002 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_003 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_004 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_005 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_006 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_007 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_008 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_009 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_010 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_011 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_012 ())). Qed.
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
Module PqvrA0 := BndP_Na_113.LibSegNa_qvrA0.
Definition KS_qvrA0 : list nat := Eval vm_compute in (BG.kept_list 80 PqvrA0.regs0 PqvrA0.regs_out0).
Lemma KS_qvrA0_ok : BG.kept_ok 80 PqvrA0.regs0 PqvrA0.regs_out0 KS_qvrA0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_013 ())). Qed.
Lemma qvrA0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5c20 M) (st fx' R' 0x64960 M')
        /\ (forall x, In x KS_qvrA0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 744608
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 96
        /\ getr R' (reg 11) = Z_to_bv 64 1440376
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 20) = getr R (reg 10)
        /\ getr R' (reg 21) = getr R (reg 13)
        /\ getr R' (reg 23) = getr R (reg 12)
        /\ getr R' (reg 24) = getr R (reg 11)
        /\ getr R' (reg 27) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (bv_unsigned (getr R (reg 14)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_014 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrA16 := BndP_Na_113.LibSegNa_qvrA16.
Definition KS_qvrA16 : list nat := Eval vm_compute in (BG.kept_list 80 PqvrA16.regs0 PqvrA16.regs_out0).
Lemma KS_qvrA16_ok : BG.kept_ok 80 PqvrA16.regs0 PqvrA16.regs_out0 KS_qvrA16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_015 ())). Qed.
Lemma qvrA16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) + 16) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487328 <= (V 2%nat) <= 140737488355312 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 176 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5c20 M) (st fx' R' 0x64960 M')
        /\ (forall x, In x KS_qvrA16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 744608
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) + 16)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 96
        /\ getr R' (reg 11) = Z_to_bv 64 1440376
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 20) = getr R (reg 10)
        /\ getr R' (reg 21) = getr R (reg 13)
        /\ getr R' (reg 23) = getr R (reg 12)
        /\ getr R' (reg 24) = getr R (reg 11)
        /\ getr R' (reg 27) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (bv_unsigned (getr R (reg 14)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' (V 2%nat) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_016 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrB := BndP_Na_114.LibSegNa_qvrB.
Definition KS_qvrB : list nat := Eval vm_compute in (BG.kept_list 80 PqvrB.regs0 PqvrB.regs_out0).
Lemma KS_qvrB_ok : BG.kept_ok 80 PqvrB.regs0 PqvrB.regs_out0 KS_qvrB = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_017 ())). Qed.
Lemma qvrB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 112) 8 -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 160)) ->
  7036928 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (V 50%nat) 24 ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 12 -> 7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) ->
  L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 -> (((((V 36%nat) + 80) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= ((((V 36%nat) + 80) / 8) + 2147450880)) -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 160)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5ca0 M) (st fx' R' 0xb5d54 M')
        /\ (forall x, In x KS_qvrB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 114794
        /\ getr R' (reg 12) = Z_to_bv 64 744480
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551602
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + 80)
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 744480
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 114794
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_018 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrQ := BndP_Na_116.LibSegNa_qvrQ.
Definition KS_qvrQ : list nat := Eval vm_compute in (BG.kept_list 80 PqvrQ.regs0 PqvrQ.regs_out0).
Lemma KS_qvrQ_ok : BG.kept_ok 80 PqvrQ.regs0 PqvrQ.regs_out0 KS_qvrQ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_019 ())). Qed.
Lemma qvrQ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  7036928 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (V 50%nat) 8 ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> 140735332487328 <= (V 52%nat) <= 140737488355328 -> aligned (V 52%nat) 16 ->
  L5.u64_at RSEGS M ((V 52%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 32) (V 63%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 64) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 96) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 104) (V 72%nat) -> (((V 52%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 52%nat) - 160)) -> (((V 52%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 52%nat) - 160)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb62d0 M) (st fx' R' 0xb63a0 M')
        /\ (forall x, In x KS_qvrQ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 72%nat)
        /\ L5.u8_at RSEGS M' (V 51%nat) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) [] (Mh_0230_blobs1.kr_b_020 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrJ1 := BndP_Na_115.LibSegNa_qvrJ1.
Definition KS_qvrJ1 : list nat := Eval vm_compute in (BG.kept_list 80 PqvrJ1.regs0 PqvrJ1.regs_out0).
Lemma KS_qvrJ1_ok : BG.kept_ok 80 PqvrJ1.regs0 PqvrJ1.regs_out0 KS_qvrJ1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_021 ())). Qed.
Lemma qvrJ1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) ->
  7036928 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450884) 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 4) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= i < ((((V 50%nat) / 8) + 2147450880) + 4) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6020 M) (st fx' R' 0xb6258 M')
        /\ (forall x, In x KS_qvrJ1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_022 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrKr := BndP_Na_116.LibSegNa_qvrKr.
Definition KS_qvrKr : list nat := Eval vm_compute in (BG.kept_list 80 PqvrKr.regs0 PqvrKr.regs_out0).
Lemma KS_qvrKr_ok : BG.kept_ok 80 PqvrKr.regs0 PqvrKr.regs_out0 KS_qvrKr = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_023 ())). Qed.
Lemma qvrKr_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) ->
  7036928 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450888) 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 8) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 8) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 8) <= i < ((((V 50%nat) / 8) + 2147450880) + 8) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb61f0 M) (st fx' R' 0xb6258 M')
        /\ (forall x, In x KS_qvrKr -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 248).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP1 ()) [] (Mh_0230_blobs1.kr_b_024 ())). Qed.
(* [comment removed for export] *)

End PQAABRP1.

End PnAAdBrP1.
Module PnAAdBrP2.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0175. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0175.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdBrP2 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0S9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2:KS_qvrKe0SC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0S<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2=u8_of_KWord1aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0S3NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0S3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0S3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2=KS_qvrKe0S_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0S6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0L9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2:KS_qvrKe0LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0L<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0L3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2=KS_qvrKe0L_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe0L6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1S9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2:KS_qvrKe1SC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1S<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1S3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1S3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2=KS_qvrKe1S_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1S6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1L9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2:KS_qvrKe1LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1L<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1L3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2=KS_qvrKe1L_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28PqvrKe1L6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQV5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQV9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28KS_qvrQVC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQV<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQV3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQV2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQV3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQV3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQV3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2;KS_qvrQV_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQK5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQK9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28KS_qvrQKC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQK<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQK3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQK2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQK3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQK3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP26PqvrQK3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2;KS_qvrQK_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqV5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqV9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP29KS_qvrCqVC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqV<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqV3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqV2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqV3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqV3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqV3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2<KS_qvrCqV_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqK5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqK9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP29KS_qvrCqKC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqK<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqK3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqK2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqK3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqK3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27PqvrCqK3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2<KS_qvrCqK_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP25PqvrC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP25PqvrC9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27KS_qvrCC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP25PqvrC<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP25PqvrC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP25PqvrC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP25PqvrC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP25PqvrC3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP25PqvrC3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2:KS_qvrC_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAABRP2.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_025 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_026 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_027 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_028 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_029 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_030 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_031 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_032 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_033 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_034 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_035 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_036 ())). Qed.
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
Module PqvrKe0S := BndP_Na_115.LibSegNa_qvrKe0S.
Definition KS_qvrKe0S : list nat := Eval vm_compute in (BG.kept_list 80 PqvrKe0S.regs0 PqvrKe0S.regs_out0).
Lemma KS_qvrKe0S_ok : BG.kept_ok 80 PqvrKe0S.regs0 PqvrKe0S.regs_out0 KS_qvrKe0S = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_037 ())). Qed.
Lemma qvrKe0S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 25) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) ->
  0 <= (V 40%nat) <= 44 -> Z.testbit (V 40%nat) 0 = false -> L5.writable RSEGS M ((V 36%nat) + 24) 2 -> 7036928 <= (V 33%nat) <= 140737488355312 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 33%nat) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) (V 49%nat) -> 0 <= (V 48%nat) <= 140737488355328 -> 0 <= (V 49%nat) <= 67108864 -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + 96 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 24) <= bv_unsigned a < ((V 36%nat) + 24) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 24) <= i < ((V 36%nat) + 24) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5d54 M) (st fx' R' 0xbebe4 M')
        /\ (forall x, In x KS_qvrKe0S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745052
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 48%nat) + (V 49%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 157203
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 24) 0
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 25) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_038 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrKe0L := BndP_Na_115.LibSegNa_qvrKe0L.
Definition KS_qvrKe0L : list nat := Eval vm_compute in (BG.kept_list 80 PqvrKe0L.regs0 PqvrKe0L.regs_out0).
Lemma KS_qvrKe0L_ok : BG.kept_ok 80 PqvrKe0L.regs0 PqvrKe0L.regs_out0 KS_qvrKe0L = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_039 ())). Qed.
Lemma qvrKe0L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 ->
  aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) ->
  0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) -> 4096 <= (V 42%nat) <= 140737488355328 -> L5.writable RSEGS M ((V 36%nat) + 32) 8 ->
  L5.writable RSEGS M (V 42%nat) 1 -> (2147446784 + 17592186048512 <= (V 42%nat) \/ (V 42%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 42%nat) / 8) + 2147450880) 1 -> ((V 42%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 96 <= (V 42%nat)) ->
  ((V 42%nat) + 1 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 42%nat)) -> 7036928 <= (V 33%nat) <= 140737488355312 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 33%nat) (V 48%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 49%nat) -> 0 <= (V 48%nat) <= 140737488355328 ->
  0 <= (V 49%nat) <= 67108864 -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + 96 <= (V 33%nat)) -> ((V 33%nat) + 16 <= (V 42%nat) \/ (V 42%nat) + 1 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 32) <= bv_unsigned a < ((V 36%nat) + 32) + 8) -> ~ (((V 42%nat) + 0) <= bv_unsigned a < ((V 42%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 32) <= i < ((V 36%nat) + 32) + 8) -> ~ (((V 42%nat) + 0) <= i < ((V 42%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5d54 M) (st fx' R' 0xbebe4 M')
        /\ (forall x, In x KS_qvrKe0L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745052
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 48%nat) + (V 49%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 157203
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 32) 0
        /\ L5.u8_at RSEGS M' (V 42%nat) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_040 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrKe1S := BndP_Na_116.LibSegNa_qvrKe1S.
Definition KS_qvrKe1S : list nat := Eval vm_compute in (BG.kept_list 80 PqvrKe1S.regs0 PqvrKe1S.regs_out0).
Lemma KS_qvrKe1S_ok : BG.kept_ok 80 PqvrKe1S.regs0 PqvrKe1S.regs_out0 KS_qvrKe1S = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_041 ())). Qed.
Lemma qvrKe1S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 25) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 44 -> Z.testbit (V 40%nat) 0 = false ->
  L5.writable RSEGS M ((V 36%nat) + 24) 2 -> 7036928 <= (V 33%nat) <= 140737488355312 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 33%nat) (V 48%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 49%nat) -> 0 <= (V 48%nat) <= 140737488355328 ->
  0 <= (V 49%nat) <= 67108864 -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + 96 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 24) <= bv_unsigned a < ((V 36%nat) + 24) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 24) <= i < ((V 36%nat) + 24) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5d54 M) (st fx' R' 0xbebe4 M')
        /\ (forall x, In x KS_qvrKe1S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745052
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 48%nat) + (V 49%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 157203
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 24) 0
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 25) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_042 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrKe1L := BndP_Na_115.LibSegNa_qvrKe1L.
Definition KS_qvrKe1L : list nat := Eval vm_compute in (BG.kept_list 80 PqvrKe1L.regs0 PqvrKe1L.regs_out0).
Lemma KS_qvrKe1L_ok : BG.kept_ok 80 PqvrKe1L.regs0 PqvrKe1L.regs_out0 KS_qvrKe1L = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_043 ())). Qed.
Lemma qvrKe1L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 ->
  aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 ->
  Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) -> 0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) ->
  4096 <= (V 42%nat) <= 140737488355328 -> L5.writable RSEGS M ((V 36%nat) + 32) 8 -> L5.writable RSEGS M (V 42%nat) 1 -> (2147446784 + 17592186048512 <= (V 42%nat) \/ (V 42%nat) + 1 <= 2147446784) ->
  L5KA.zeros_at M (((V 42%nat) / 8) + 2147450880) 1 -> ((V 42%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 96 <= (V 42%nat)) -> ((V 42%nat) + 1 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 42%nat)) -> 7036928 <= (V 33%nat) <= 140737488355312 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 33%nat) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) (V 49%nat) -> 0 <= (V 48%nat) <= 140737488355328 -> 0 <= (V 49%nat) <= 67108864 -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + 96 <= (V 33%nat)) ->
  ((V 33%nat) + 16 <= (V 42%nat) \/ (V 42%nat) + 1 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 32) <= bv_unsigned a < ((V 36%nat) + 32) + 8) -> ~ (((V 42%nat) + 0) <= bv_unsigned a < ((V 42%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 32) <= i < ((V 36%nat) + 32) + 8) -> ~ (((V 42%nat) + 0) <= i < ((V 42%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5d54 M) (st fx' R' 0xbebe4 M')
        /\ (forall x, In x KS_qvrKe1L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745052
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 48%nat) + (V 49%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 157203
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 32) 0
        /\ L5.u8_at RSEGS M' (V 42%nat) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_044 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrQV := BndP_Na_116.LibSegNa_qvrQV.
Definition KS_qvrQV : list nat := Eval vm_compute in (BG.kept_list 80 PqvrQV.regs0 PqvrQV.regs_out0).
Lemma KS_qvrQV_ok : BG.kept_ok 80 PqvrQV.regs0 PqvrQV.regs_out0 KS_qvrQV = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_045 ())). Qed.
Lemma qvrQV_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5ef0 M) (st fx' R' 0xf4640 M')
        /\ (forall x, In x KS_qvrQV -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745212
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 34).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_046 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrQK := BndP_Na_116.LibSegNa_qvrQK.
Definition KS_qvrQK : list nat := Eval vm_compute in (BG.kept_list 80 PqvrQK.regs0 PqvrQK.regs_out0).
Lemma KS_qvrQK_ok : BG.kept_ok 80 PqvrQK.regs0 PqvrQK.regs_out0 KS_qvrQK = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_047 ())). Qed.
Lemma qvrQK_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5f54 M) (st fx' R' 0xf4640 M')
        /\ (forall x, In x KS_qvrQK -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745316
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 34
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_048 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrCqV := BndP_Na_114.LibSegNa_qvrCqV.
Definition KS_qvrCqV : list nat := Eval vm_compute in (BG.kept_list 80 PqvrCqV.regs0 PqvrCqV.regs_out0).
Lemma KS_qvrCqV_ok : BG.kept_ok 80 PqvrCqV.regs0 PqvrCqV.regs_out0 KS_qvrCqV = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_049 ())). Qed.
Lemma qvrCqV_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6118 M) (st fx' R' 0xf4640 M')
        /\ (forall x, In x KS_qvrCqV -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 746072
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 34).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_050 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrCqK := BndP_Na_114.LibSegNa_qvrCqK.
Definition KS_qvrCqK : list nat := Eval vm_compute in (BG.kept_list 80 PqvrCqK.regs0 PqvrCqK.regs_out0).
Lemma KS_qvrCqK_ok : BG.kept_ok 80 PqvrCqK.regs0 PqvrCqK.regs_out0 KS_qvrCqK = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_051 ())). Qed.
Lemma qvrCqK_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6240 M) (st fx' R' 0xf4640 M')
        /\ (forall x, In x KS_qvrCqK -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 746060
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 34).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_052 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrC := BndP_Na_114.LibSegNa_qvrC.
Definition KS_qvrC : list nat := Eval vm_compute in (BG.kept_list 80 PqvrC.regs0 PqvrC.regs_out0).
Lemma KS_qvrC_ok : BG.kept_ok 80 PqvrC.regs0 PqvrC.regs_out0 KS_qvrC = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_053 ())). Qed.
Lemma qvrC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb624c M) (st fx' R' 0xf4640 M')
        /\ (forall x, In x KS_qvrC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 746072
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 58).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP2 ()) [] (Mh_0230_blobs1.kr_b_054 ())). Qed.
(* [comment removed for export] *)

End PQAABRP2.

End PnAAdBrP2.
Module PnAAdBrP3.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdBrP3 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDV25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDV29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP39KS_qvrDV2C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDV2<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDV23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDV22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDV23NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDV23kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDV23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3<KS_qvrDV2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1z9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3:KS_qvrDV1zC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1z<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1z3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3=KS_qvrDV1z_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1n9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3:KS_qvrDV1nC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1n<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP38PqvrDV1n3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3=KS_qvrDV1n_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKz5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKz9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP39KS_qvrDKzC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKz<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKz3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKz2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKz3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKz3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKz3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3<KS_qvrDKz_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKn9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP39KS_qvrDKnC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKn<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKn3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37PqvrDKn3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3<KS_qvrDKn_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAABRP3.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_055 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_056 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_057 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_058 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_059 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_060 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_061 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_062 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_063 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_064 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_065 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_066 ())). Qed.
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
Module PqvrDV2 := BndP_Na_114.LibSegNa_qvrDV2.
Definition KS_qvrDV2 : list nat := Eval vm_compute in (BG.kept_list 80 PqvrDV2.regs0 PqvrDV2.regs_out0).
Lemma KS_qvrDV2_ok : BG.kept_ok 80 PqvrDV2.regs0 PqvrDV2.regs_out0 KS_qvrDV2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_067 ())). Qed.
Lemma qvrDV2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 20) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 20) 2 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5e5c M) (st fx' R' 0xb5ef0 M')
        /\ (forall x, In x KS_qvrDV2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 2
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_068 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrDV1z := BndP_Na_114.LibSegNa_qvrDV1z.
Definition KS_qvrDV1z : list nat := Eval vm_compute in (BG.kept_list 80 PqvrDV1z.regs0 PqvrDV1z.regs_out0).
Lemma KS_qvrDV1z_ok : BG.kept_ok 80 PqvrDV1z.regs0 PqvrDV1z.regs_out0 KS_qvrDV1z = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_069 ())). Qed.
Lemma qvrDV1z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 20) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 8) / 8) + 2147450880) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u64_at RSEGS M ((V 37%nat) - 8) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5e5c M) (st fx' R' 0xb5ef0 M')
        /\ (forall x, In x KS_qvrDV1z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_070 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrDV1n := BndP_Na_114.LibSegNa_qvrDV1n.
Definition KS_qvrDV1n : list nat := Eval vm_compute in (BG.kept_list 80 PqvrDV1n.regs0 PqvrDV1n.regs_out0).
Lemma KS_qvrDV1n_ok : BG.kept_ok 80 PqvrDV1n.regs0 PqvrDV1n.regs_out0 KS_qvrDV1n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_071 ())). Qed.
Lemma qvrDV1n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 20) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 8) / 8) + 2147450880) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u64_at RSEGS M ((V 37%nat) - 8) (V 43%nat) ->
  1 <= (V 43%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5e5c M) (st fx' R' 0xf4640 M')
        /\ (forall x, In x KS_qvrDV1n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745200
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 44
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_072 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrDKz := BndP_Na_114.LibSegNa_qvrDKz.
Definition KS_qvrDKz : list nat := Eval vm_compute in (BG.kept_list 80 PqvrDKz.regs0 PqvrDKz.regs_out0).
Lemma KS_qvrDKz_ok : BG.kept_ok 80 PqvrDKz.regs0 PqvrDKz.regs_out0 KS_qvrDKz = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_073 ())). Qed.
Lemma qvrDKz_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 8) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> L5.u64_at RSEGS M ((V 37%nat) - 8) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5e5c M) (st fx' R' 0xb5f54 M')
        /\ (forall x, In x KS_qvrDKz -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_074 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrDKn := BndP_Na_114.LibSegNa_qvrDKn.
Definition KS_qvrDKn : list nat := Eval vm_compute in (BG.kept_list 80 PqvrDKn.regs0 PqvrDKn.regs_out0).
Lemma KS_qvrDKn_ok : BG.kept_ok 80 PqvrDKn.regs0 PqvrDKn.regs_out0 KS_qvrDKn = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_075 ())). Qed.
Lemma qvrDKn_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 8) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> L5.u64_at RSEGS M ((V 37%nat) - 8) (V 43%nat) -> 1 <= (V 43%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5e5c M) (st fx' R' 0xf4640 M')
        /\ (forall x, In x KS_qvrDKn -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745300
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 44
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP3 ()) [] (Mh_0230_blobs1.kr_b_076 ())). Qed.
(* [comment removed for export] *)

End PQAABRP3.

End PnAAdBrP3.
Module PnAAdBrP4.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdBrP4 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIVSSC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP47alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSS<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSS3NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSS3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4=KS_qvrIVSS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIVSLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVSL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4=KS_qvrIVSL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIVLSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4=KS_qvrIVLS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIVLLC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIVLL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4=KS_qvrIVLL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIKSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4=KS_qvrIKSS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIKSLC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKSL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4=KS_qvrIKSL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIKLSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4=KS_qvrIKLS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4:KS_qvrIKLLC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP48PqvrIKLL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP48PQAABRP4=KS_qvrIKLL_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAABRP4.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_077 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_078 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_079 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_080 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_081 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_082 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_083 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_084 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_085 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_086 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_087 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_088 ())). Qed.
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
Module PqvrIVSS := BndP_Na_115.LibSegNa_qvrIVSS.
Definition KS_qvrIVSS : list nat := Eval vm_compute in (BG.kept_list 80 PqvrIVSS.regs0 PqvrIVSS.regs_out0).
Lemma KS_qvrIVSS_ok : BG.kept_ok 80 PqvrIVSS.regs0 PqvrIVSS.regs_out0 KS_qvrIVSS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_089 ())). Qed.
Lemma qvrIVSS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) -> 0 <= (V 44%nat) <= 44 -> Z.testbit (V 44%nat) 0 = false ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 44 -> Z.testbit (V 40%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5efc M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvrIVSS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745752
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + ((V 44%nat) / 2)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + ((V 40%nat) / 2)) + 25)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 40%nat) / 2)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_090 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrIVSL := BndP_Na_115.LibSegNa_qvrIVSL.
Definition KS_qvrIVSL : list nat := Eval vm_compute in (BG.kept_list 80 PqvrIVSL.regs0 PqvrIVSL.regs_out0).
Lemma KS_qvrIVSL_ok : BG.kept_ok 80 PqvrIVSL.regs0 PqvrIVSL.regs_out0 KS_qvrIVSL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_091 ())). Qed.
Lemma qvrIVSL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) ->
  0 <= (V 44%nat) <= 44 -> Z.testbit (V 44%nat) 0 = false -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 ->
  Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) -> 0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) ->
  4096 <= (V 42%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5efc M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvrIVSL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745752
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + ((V 44%nat) / 2)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 41%nat) + (V 42%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 41%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_092 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrIVLS := BndP_Na_115.LibSegNa_qvrIVLS.
Definition KS_qvrIVLS : list nat := Eval vm_compute in (BG.kept_list 80 PqvrIVLS.regs0 PqvrIVLS.regs_out0).
Lemma KS_qvrIVLS_ok : BG.kept_ok 80 PqvrIVLS.regs0 PqvrIVLS.regs_out0 KS_qvrIVLS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_093 ())). Qed.
Lemma qvrIVLS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 64) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 56) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) ->
  0 <= (V 44%nat) <= 255 -> Z.testbit (V 44%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 56) (V 45%nat) -> 0 <= (V 45%nat) <= 2147483648 ->
  L5.u64_at RSEGS M ((V 36%nat) + 64) (V 46%nat) -> 4096 <= (V 46%nat) <= 140737488355328 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 44 ->
  Z.testbit (V 40%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5efc M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvrIVLS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745752
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 45%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + ((V 40%nat) / 2)) + 25)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 40%nat) / 2)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_094 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrIVLL := BndP_Na_115.LibSegNa_qvrIVLL.
Definition KS_qvrIVLL : list nat := Eval vm_compute in (BG.kept_list 80 PqvrIVLL.regs0 PqvrIVLL.regs_out0).
Lemma KS_qvrIVLL_ok : BG.kept_ok 80 PqvrIVLL.regs0 PqvrIVLL.regs_out0 KS_qvrIVLL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_095 ())). Qed.
Lemma qvrIVLL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 64) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 56) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) -> 0 <= (V 44%nat) <= 255 -> Z.testbit (V 44%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 36%nat) + 56) (V 45%nat) -> 0 <= (V 45%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 64) (V 46%nat) -> 4096 <= (V 46%nat) <= 140737488355328 ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) ->
  0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) -> 4096 <= (V 42%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5efc M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvrIVLL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745752
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 45%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 41%nat) + (V 42%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 41%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_096 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrIKSS := BndP_Na_115.LibSegNa_qvrIKSS.
Definition KS_qvrIKSS : list nat := Eval vm_compute in (BG.kept_list 80 PqvrIKSS.regs0 PqvrIKSS.regs_out0).
Lemma KS_qvrIKSS_ok : BG.kept_ok 80 PqvrIKSS.regs0 PqvrIKSS.regs_out0 KS_qvrIKSS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_097 ())). Qed.
Lemma qvrIKSS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) -> 0 <= (V 44%nat) <= 44 -> Z.testbit (V 44%nat) 0 = false ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 44 -> Z.testbit (V 40%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5f64 M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvrIKSS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 746048
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + ((V 44%nat) / 2)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + ((V 40%nat) / 2)) + 25)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 40%nat) / 2)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_098 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrIKSL := BndP_Na_115.LibSegNa_qvrIKSL.
Definition KS_qvrIKSL : list nat := Eval vm_compute in (BG.kept_list 80 PqvrIKSL.regs0 PqvrIKSL.regs_out0).
Lemma KS_qvrIKSL_ok : BG.kept_ok 80 PqvrIKSL.regs0 PqvrIKSL.regs_out0 KS_qvrIKSL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_099 ())). Qed.
Lemma qvrIKSL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) ->
  0 <= (V 44%nat) <= 44 -> Z.testbit (V 44%nat) 0 = false -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 ->
  Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) -> 0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) ->
  4096 <= (V 42%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5f64 M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvrIKSL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 746048
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + ((V 44%nat) / 2)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 41%nat) + (V 42%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 41%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_100 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrIKLS := BndP_Na_115.LibSegNa_qvrIKLS.
Definition KS_qvrIKLS : list nat := Eval vm_compute in (BG.kept_list 80 PqvrIKLS.regs0 PqvrIKLS.regs_out0).
Lemma KS_qvrIKLS_ok : BG.kept_ok 80 PqvrIKLS.regs0 PqvrIKLS.regs_out0 KS_qvrIKLS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_101 ())). Qed.
Lemma qvrIKLS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 64) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 56) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) ->
  0 <= (V 44%nat) <= 255 -> Z.testbit (V 44%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 56) (V 45%nat) -> 0 <= (V 45%nat) <= 2147483648 ->
  L5.u64_at RSEGS M ((V 36%nat) + 64) (V 46%nat) -> 4096 <= (V 46%nat) <= 140737488355328 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 44 ->
  Z.testbit (V 40%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5f64 M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvrIKLS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 746048
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 45%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + ((V 40%nat) / 2)) + 25)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 40%nat) / 2)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_102 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrIKLL := BndP_Na_115.LibSegNa_qvrIKLL.
Definition KS_qvrIKLL : list nat := Eval vm_compute in (BG.kept_list 80 PqvrIKLL.regs0 PqvrIKLL.regs_out0).
Lemma KS_qvrIKLL_ok : BG.kept_ok 80 PqvrIKLL.regs0 PqvrIKLL.regs_out0 KS_qvrIKLL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_103 ())). Qed.
Lemma qvrIKLL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 64) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 56) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) -> 0 <= (V 44%nat) <= 255 -> Z.testbit (V 44%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 36%nat) + 56) (V 45%nat) -> 0 <= (V 45%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 64) (V 46%nat) -> 4096 <= (V 46%nat) <= 140737488355328 ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) ->
  0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) -> 4096 <= (V 42%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5f64 M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvrIKLL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 746048
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 45%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 41%nat) + (V 42%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 41%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP4 ()) [] (Mh_0230_blobs1.kr_b_104 ())). Qed.
(* [comment removed for export] *)

End PQAABRP4.

End PnAAdBrP4.
Module PnAAdBrP5.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdBrP5 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5;KS_qvrAk2e0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP57alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5>u32_of_KWord4aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e03NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5>KS_qvrAk2e0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e06cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5;KS_qvrAk2e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5>KS_qvrAk2e1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk2e16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk1e15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk1e19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5;KS_qvrAk1e1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk1e1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk1e13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk1e12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk1e13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk1e13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP59PqvrAk1e13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5>KS_qvrAk1e1_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAABRP5.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_105 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_106 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_107 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_108 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_109 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_110 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_111 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_112 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_113 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_114 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_115 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_116 ())). Qed.
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
Module PqvrAk2e0 := BndP_Na_114.LibSegNa_qvrAk2e0.
Definition KS_qvrAk2e0 : list nat := Eval vm_compute in (BG.kept_list 80 PqvrAk2e0.regs0 PqvrAk2e0.regs_out0).
Lemma KS_qvrAk2e0_ok : BG.kept_ok 80 PqvrAk2e0.regs0 PqvrAk2e0.regs_out0 KS_qvrAk2e0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_117 ())). Qed.
Lemma qvrAk2e0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 20) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 2 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 ->
  L5.writable RSEGS M ((V 37%nat) - 16) 4 -> (((V 37%nat) - 24) + 24 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 37%nat) - 24)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 16) <= bv_unsigned a < ((V 37%nat) - 16) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 16) <= i < ((V 37%nat) - 16) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6258 M) (st fx' R' 0xb62d0 M')
        /\ (forall x, In x KS_qvrAk2e0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) - 16)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((((V 37%nat) - 16) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 2
        /\ L5.u32_at RSEGS M' ((V 37%nat) - 16) 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_118 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrAk2e1 := BndP_Na_114.LibSegNa_qvrAk2e1.
Definition KS_qvrAk2e1 : list nat := Eval vm_compute in (BG.kept_list 80 PqvrAk2e1.regs0 PqvrAk2e1.regs_out0).
Lemma KS_qvrAk2e1_ok : BG.kept_ok 80 PqvrAk2e1.regs0 PqvrAk2e1.regs_out0 KS_qvrAk2e1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_119 ())). Qed.
Lemma qvrAk2e1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 20) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 8) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 2 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.defined M ((V 37%nat) - 8) 8 -> L5.writable RSEGS M ((V 37%nat) - 16) 4 -> L5.writable RSEGS M ((V 37%nat) - 8) 8 ->
  (((V 37%nat) - 24) + 24 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 37%nat) - 24)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 16) <= bv_unsigned a < ((V 37%nat) - 16) + 4) -> ~ (((V 37%nat) - 8) <= bv_unsigned a < ((V 37%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 16) <= i < ((V 37%nat) - 16) + 4) -> ~ (((V 37%nat) - 8) <= i < ((V 37%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6258 M) (st fx' R' 0xb62d0 M')
        /\ (forall x, In x KS_qvrAk2e1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) - 16)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((((V 37%nat) - 16) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 2
        /\ L5.u32_at RSEGS M' ((V 37%nat) - 16) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_120 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrAk1e1 := BndP_Na_114.LibSegNa_qvrAk1e1.
Definition KS_qvrAk1e1 : list nat := Eval vm_compute in (BG.kept_list 80 PqvrAk1e1.regs0 PqvrAk1e1.regs_out0).
Lemma KS_qvrAk1e1_ok : BG.kept_ok 80 PqvrAk1e1.regs0 PqvrAk1e1.regs_out0 KS_qvrAk1e1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_121 ())). Qed.
Lemma qvrAk1e1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 20) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 8) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) (V 45%nat) ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.defined M ((V 37%nat) - 8) 8 -> 0 <= (V 45%nat) <= 1 -> L5.writable RSEGS M ((V 37%nat) - 8) 8 ->
  (((V 37%nat) - 24) + 24 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 37%nat) - 24)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 8) <= bv_unsigned a < ((V 37%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 8) <= i < ((V 37%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6258 M) (st fx' R' 0xb62d0 M')
        /\ (forall x, In x KS_qvrAk1e1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) - 16)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((((V 37%nat) - 16) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 2).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP5 ()) [] (Mh_0230_blobs1.kr_b_122 ())). Qed.
(* [comment removed for export] *)

End PQAABRP5.

End PnAAdBrP5.
Module PnAAdBrP6.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.

Module PQAABRP6.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5KA.zpolyA_sound E Vz e z A Pz)).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, BL.MM. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u64_of_KWord8; eauto. Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u32_of_KWord4; eauto. Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof. intros K Ha Hv Hr ->. eapply L5K.u8_of_KWord1; eauto. Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
  intros K Ha Hv -> -> ->. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd).
  rewrite L5K.adenot_e, Ha in Rd. rewrite (BG.word_of_unsigned _ _ Hv) in Rd.
  pose proof (bv_unsigned_in_range 64 (edenot E e)) as Rg. rewrite Hv in Rg. change (bv_modulus 64) with (2 ^ 64) in Rg.
  unfold word_to_le_bytes in Rd. rewrite Z_to_bv_unsigned in Rd. unfold bv_wrap in Rd. change (bv_modulus 64) with (2 ^ 64) in Rd.
  rewrite (Z.mod_small v (2 ^ 64)) in Rd by (clear - Rg; lia). cbn [Z_to_le_bytes rdn] in Rd. unfold L5.u8_at.
  assert (E1 : (Z_to_bv 64 (a + off) + 1 = Z_to_bv 64 (a + off + 1))%bv).
  { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    change (bv_unsigned (1 : bv 64)) with 1. apply Z.add_mod_idemp_l. clear; lia. }
  rewrite E1 in Rd.
  destruct (match M (Z_to_bv 64 (a + off)) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 (a + off)) end) as [x|] eqn:X; [|discriminate].
  destruct (match M (Z_to_bv 64 (a + off + 1)) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 (a + off + 1)) end) as [y|] eqn:Y; [|discriminate].
  injection Rd as Ex Ey. split.
  - cbn [rdn]. rewrite X. subst x. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_mod by (clear; lia). reflexivity.
  - cbn [rdn]. rewrite Y. subst y. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 8) with 256. rewrite Z.mod_mod by (clear; lia). reflexivity.
Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof. intros K Ha Hn ->. eapply L5K.defined_of_KUnk; eauto. Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof. intros K Ha Hv -> ->. eapply L5KA.u8_of_KWord1_mod; eauto. Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof. intros K Ha Hn ->. eapply L5KA.zeros_of_KZero; eauto. Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof. intros Ha Hm. pose proof (L5K.land_le_r a m Ha ltac:(lia)). lia. Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
  intros Ha Hb. split. apply Z.lor_nonneg; lia.
  destruct (Z.eq_dec a 0) as [->|Na]. rewrite Z.lor_0_l. lia. destruct (Z.eq_dec b 0) as [->|Nb]. rewrite Z.lor_0_r. lia.
  apply (Z.log2_lt_cancel). rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; try lia; change (2 ^ Z.log2 256) with 256; lia.
Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof. intros Ha Hm. rewrite Z.land_comm. exact (proj2 (L5K.land_le_r m a Hm Ha)). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
  intros Ha. assert (E : forallb (fun i => let x := Z.of_nat i in (0 <=? (Z.land x 18446744073709551613 + 2) mod 2 ^ 64) && ((Z.land x 18446744073709551613 + 2) mod 2 ^ 64 <? 256)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in E. specialize (E (Z.to_nat a) ltac:(apply in_seq; lia)). cbn zeta in E. rewrite Z2Nat.id in E by lia. apply andb_prop in E as [E1 E2]. lia.
Qed.
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
Module PqvrDa := BndP_Na_114.LibSegNa_qvrDa.
Definition KS_qvrDa : list nat := Eval vm_compute in (BG.kept_list 80 PqvrDa.regs0 PqvrDa.regs_out0).
Lemma KS_qvrDa_ok : BG.kept_ok 80 PqvrDa.regs0 PqvrDa.regs_out0 KS_qvrDa = true. Proof. vm_compute. reflexivity. Qed.
Lemma qvrDa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 16) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 16) (V 38%nat) -> 7036928 <= (V 38%nat) <= 140737488355320 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5d54 M) (st fx' R' 0xb5fa4 M')
        /\ (forall x, In x KS_qvrDa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G19 G20 G22 G27 pvzI5 K1 K2 K3 K4 K5 pvzI6 K7 K8 K9 K10 K11 K12 K13 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K14l; move K14l before pvzI7; pose proof (proj2 pvzI7) as K14r; move K14r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PqvrDa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PqvrDa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PqvrDa.kn0).
  { unfold know_ok, PqvrDa.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K0l K0r K2) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K0l K0r K2) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K0l K0r K2) | evalEk ZA ltac:(clear) | generalize K2; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K0l K0r K2) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K0l K0r K2; lia | clear - HV36l HV36r K0l K0r K2; lia | clear - HV36l HV36r K0l K0r K2; lia | exactA K3]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K0l K0r K2) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K0l K0r K2; lia | clear - HV36l HV36r K0l K0r K2; lia | clear - HV36l HV36r K0l K0r K2; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K0l K0r K2) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8) | clear - HV36l HV36r K0l K0r K2; lia | clear - HV36l HV36r K0l K0r K2; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8; lia | clear - HV37l HV37r K6l K6r K8; lia | clear - HV37l HV37r K6l K6r K8; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8; lia | clear - HV37l HV37r K6l K6r K8; lia | clear - HV37l HV37r K6l K6r K8; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8; lia | clear - HV37l HV37r K6l K6r K8; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8; lia | clear - HV37l HV37r K6l K6r K8; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K0l K0r K2) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear - HV36l HV36r K0l K0r K2; lia | clear - HV36l HV36r K0l K0r K2; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PqvrDa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PqvrDa.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PqvrDa.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PqvrDa.ps0) with 0xb5fa4 in Hms. change (SR.ps_regs PqvrDa.ps0) with (map (fun i => (i, nth i PqvrDa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PqvrDa.ps0) with PqvrDa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PqvrDa.regs0 PqvrDa.regs_out0 80 KS_qvrDa KS_qvrDa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PqvrDa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PqvrDa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PqvrDa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PqvrDa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PqvrDa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PqvrDa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PqvrDa.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PqvrDa.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End PQAABRP6.

End PnAAdBrP6.
Module PnAAdBrP7.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdBrP7 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77PqvrDb25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77PqvrDb29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP79KS_qvrDb2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdS29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7:KS_qvrKdS2C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP77alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z<eq_decidableC69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdS2<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7=u8_of_KWord1aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdS23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdS26cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdS23kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdS23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7=KS_qvrKdS2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdL25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP78PqvrKdL29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP78PQAABRP7:KS_qvrKdL2C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAABRP7.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_123 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_124 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_125 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_126 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_127 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_128 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_129 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_130 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_131 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_132 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_133 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_134 ())). Qed.
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
Module PqvrDb2 := BndP_Na_114.LibSegNa_qvrDb2.
Definition KS_qvrDb2 : list nat := Eval vm_compute in (BG.kept_list 80 PqvrDb2.regs0 PqvrDb2.regs_out0).
Lemma KS_qvrDb2_ok : BG.kept_ok 80 PqvrDb2.regs0 PqvrDb2.regs_out0 KS_qvrDb2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_135 ())). Qed.
Lemma qvrDb2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 35%nat) -> getr R (reg 23) = Z_to_bv 64 (V 34%nat) -> getr R (reg 24) = Z_to_bv 64 (V 33%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1409024 -> 7036928 <= (V 38%nat) <= 140737488355272 -> (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 38%nat) 1380656 -> ((V 50%nat) + 128 <= (V 38%nat) \/ (V 38%nat) + 56 <= (V 50%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 38%nat) / 8) + 2147450880)) -> L5KA.zeros_at M 2147623479 1 ->
  (2147618933 + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= 2147618933) -> 7036928 <= (V 33%nat) <= 140737488355312 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 33%nat) (V 48%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 49%nat) -> 0 <= (V 48%nat) <= 140737488355328 ->
  0 <= (V 49%nat) <= 67108864 -> ((((V 33%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> (((((V 33%nat) + 8) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= ((((V 33%nat) + 8) / 8) + 2147450880)) -> 7036928 <= (V 50%nat) <= 140737488355200 ->
  aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M ((V 50%nat) + 32) 16 -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450884) 2 ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 60%nat) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 160)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 32) <= bv_unsigned a < ((V 50%nat) + 32) + 16) -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 4) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 32) <= i < ((V 50%nat) + 32) + 16) -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= i < ((((V 50%nat) / 8) + 2147450880) + 4) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5fa4 M) (st fx' R' 0xc3ee0 M')
        /\ (forall x, In x KS_qvrDb2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745504
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 802528
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 40) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 32) (V 48%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 0).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) [] (Mh_0230_blobs1.kr_b_136 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrKdS2 := BndP_Na_115.LibSegNa_qvrKdS2.
Definition KS_qvrKdS2 : list nat := Eval vm_compute in (BG.kept_list 80 PqvrKdS2.regs0 PqvrKdS2.regs_out0).
Lemma KS_qvrKdS2_ok : BG.kept_ok 80 PqvrKdS2.regs0 PqvrKdS2.regs_out0 KS_qvrKdS2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_137 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma qvrKdS2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 35%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1409024 -> 7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) ->
  L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) ->
  4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 0 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 16) (V 38%nat) ->
  7036928 <= (V 38%nat) <= 140737488355272 -> (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 38%nat) 1380656 ->
  L5KA.zeros_at M 2147623474 1 -> ((V 50%nat) + 128 <= (V 38%nat) \/ (V 38%nat) + 56 <= (V 50%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 38%nat) / 8) + 2147450880)) -> (2147618928 + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= 2147618928) ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 44 -> Z.testbit (V 40%nat) 0 = false -> 7036928 <= (V 50%nat) <= 140737488355200 ->
  aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M ((V 50%nat) + 64) 16 -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450888) 2 ->
  ((V 50%nat) + 128 <= (V 36%nat) \/ (V 36%nat) + 96 <= (V 50%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 12 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) -> 140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 60%nat) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 160)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 64) <= bv_unsigned a < ((V 50%nat) + 64) + 16) -> ~ (((((V 50%nat) / 8) + 2147450880) + 8) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 8) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 64) <= i < ((V 50%nat) + 64) + 16) -> ~ (((((V 50%nat) / 8) + 2147450880) + 8) <= i < ((((V 50%nat) / 8) + 2147450880) + 8) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5e5c M) (st fx' R' 0xc2f38 M')
        /\ (forall x, In x KS_qvrKdS2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745968
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 64)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 798520
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 72) ((V 40%nat) / 2)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 64) ((V 36%nat) + 25)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_138 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvrKdL2 := BndP_Na_115.LibSegNa_qvrKdL2.
Definition KS_qvrKdL2 : list nat := Eval vm_compute in (BG.kept_list 80 PqvrKdL2.regs0 PqvrKdL2.regs_out0).
Lemma KS_qvrKdL2_ok : BG.kept_ok 80 PqvrKdL2.regs0 PqvrKdL2.regs_out0 KS_qvrKdL2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBrP7 ()) [] (Mh_0230_blobs1.kr_b_139 ())). Qed.
Lemma qvrKdL2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 35%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1409024 -> 7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) ->
  L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 16) (V 38%nat) -> 7036928 <= (V 38%nat) <= 140737488355272 -> (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 56 <= 2147446784) ->
  L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 38%nat) 1380656 -> L5KA.zeros_at M 2147623474 1 -> ((V 50%nat) + 128 <= (V 38%nat) \/ (V 38%nat) + 56 <= (V 50%nat)) ->
  ((((V 38%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 38%nat) / 8) + 2147450880)) -> (2147618928 + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= 2147618928) -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 ->
  Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) -> 0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) ->
  4096 <= (V 42%nat) <= 140737488355328 -> 7036928 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M ((V 50%nat) + 64) 16 -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450888) 2 -> ((V 50%nat) + 128 <= (V 36%nat) \/ (V 36%nat) + 96 <= (V 50%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 12 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 60%nat) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 160)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 64) <= bv_unsigned a < ((V 50%nat) + 64) + 16) -> ~ (((((V 50%nat) / 8) + 2147450880) + 8) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 8) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 64) <= i < ((V 50%nat) + 64) + 16) -> ~ (((((V 50%nat) / 8) + 2147450880) + 8) <= i < ((((V 50%nat) / 8) + 2147450880) + 8) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5e5c M) (st fx' R' 0xc2f38 M')
        /\ (forall x, In x KS_qvrKdL2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 745968
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 64)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 798520
        /\ getr R' (reg 20) = Z_to_bv 64 (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 72) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 64) (V 42%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 0).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) [] (Mh_0230_blobs1.kr_b_140 ())). Qed.
(* [comment removed for export] *)

End PQAABRP7.

End PnAAdBrP7.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require LeanFeed2. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed. From Stdlib Require ZArith List Lia Bool FunctionalExtensionality Permutation. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdStrCK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require UbjRef.
Module PnAAdBr.
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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdStrCK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObjA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAdStrCK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKSlotA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKCallA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKStepA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKFromA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKEncNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKSlotA3bN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemFrameA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdBrP1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdBrP2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdBrP3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdBrP4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdBrP5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdBrP6 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdBrP7 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016.Na0_code_rb6494_b6498.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdBr () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List4inclC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA6b64lenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lebC69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_binC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA3agAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2or00K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG37bvu_rngC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityI47Corelib4Init5Logic5False00C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7enc_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA4PMEAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8pot_encAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA;epot_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;pot_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7pot_aeAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR9pot_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8sink_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ec_stateAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092;PnQStaticsA5PQSTA7err_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_KBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5VIS_HC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib6ZArith4Zdiv:Z_mod_multI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38obj_pf_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR:b64len_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA7view_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR4OWNEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5own13C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3OCEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7ocell13C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;own13_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR8sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5V2_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxc69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR;hdr_str_le5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR;hdr_bin_le5C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR9DKB_factsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List6filterC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_tC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5lv_eoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl01C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List:filter_appC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3advC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ndestC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR8agA_reflC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR2XVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6frb_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_objC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR9agA_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5a_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_WAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4EVISC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5xv_ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR4QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5HSPCfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAadd_nonneg_nonnegC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR6pv_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR4VOKfC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_applC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5xinvGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3ESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6kbsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_oaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7alvl_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR4valsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP57alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6set_lvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR9ndest_advC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5s_xlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6s_advXC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decc69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5=qvrAk2e0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5=qvrAk2e1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5=qvrAk1e1_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3IXAC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3LSZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5;KS_qvrAk2e0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5;KS_qvrAk2e1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP58PQAABRP5;KS_qvrAk1e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_setC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR:mem_eq_frzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N8pb_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N6pb_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_restC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_app_asciiC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7s_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_xcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_kcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N9s_call_sCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3IXBC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8AOFF_KEYC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2;qvrCqV_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG38regl_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3ADVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5PUSHQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR8DKB_DPHIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP29KS_qvrCqVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR4EST0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP29qvrC_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP27KS_qvrCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2;qvrCqK_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5COLONC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP29KS_qvrCqKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multK46Stdlib9micromega=RingMicromega3Op206C69OSSVerify5KrLib7Mh_01028NemModel3NEM5asciiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N9s_key_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7src_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ins_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7ins_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA8src_okCAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3CQVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3CQKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5INS_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lv_shapeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_kbgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2:qvrQV_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR4INS2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP2:qvrQK_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4GMAXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28KS_qvrQVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP28PQAABRP28KS_qvrQKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5QUOTEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP37alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG>u64_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5COMMAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5KDESTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3;qvrDKz_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3;qvrDKn_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3;qvrDV2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3<qvrDV1z_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3<qvrDV1n_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR2IXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP39KS_qvrDKzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP39KS_qvrDKnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP39KS_qvrDV2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3:KS_qvrDV1zC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP38PQAABRP3:KS_qvrDV1nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8lv_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N:lv_last_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR6KEYB64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR6PATH_DC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lv_rootC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5wappWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_pfactsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP19qvrB_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extc69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3xvFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA8s_xpieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR5DISP1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdBrP18PQAABRP17KS_qvrBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3Hh3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5aeownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA9args_viewC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8pre_bstrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA6b64lenC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lc69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR:u64_at_injC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6cls_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;evis_of_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3phiC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6edepthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02307PnAAdBr6PQAABR3RUNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_v_bstr_rawC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA?v_bstr_raw_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA9step_bstrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00". Local Ltac lia := L5FastLia.plia.

Module PQAABR.
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
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) [] (Mh_0230_blobs1.kr_b_141 ())). Qed.
Lemma b64len_rng n : 0 <= n -> 0 <= PQVA.b64len n <= 2 * n + 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) [] (Mh_0230_blobs1.kr_b_142 ())). Qed.
(* [comment removed for export] *)
Lemma hdr_str_le5 m : NEM.hdr_str m <= 5.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) [] (Mh_0230_blobs1.kr_b_143 ())). Qed.
Lemma hdr_bin_le5 m : NEM.hdr_bin m <= 5.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) [] (Mh_0230_blobs1.kr_b_144 ())). Qed.
(* [comment removed for export] *)
Lemma agA_trans (M0 M1 M2 : mem) a n : PMFA.agA M0 M1 a n -> PMFA.agA M1 M2 a n -> PMFA.agA M0 M2 a n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) [] (Mh_0230_blobs1.kr_b_145 ())). Qed.

(* [comment removed for export] *)
Lemma aacc_join (Mx : mem) p n m : aacc Mx p n -> aacc Mx (p + n) m -> 0 <= n -> aacc Mx p (n + m).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) [] (Mh_0230_blobs1.kr_b_146 ())). Qed.
Lemma aacc_sub (Mx : mem) a0 n0 a1 n1 : aacc Mx a0 n0 -> a0 <= a1 -> a1 + n1 <= a0 + n0 -> aacc Mx a1 n1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) [] (Mh_0230_blobs1.kr_b_147 ())). Qed.

(* [comment removed for export] *)
Lemma mem_eq_frz (Ma Mb : mem) : (forall a, 0 <= a < 2 ^ 64 -> ~ False -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> Mb = Ma.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) [] (Mh_0230_blobs1.kr_b_148 ())). Qed.

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
Hypothesis VBE : NECSA.v_bstr_raw_spec RSEGS AD AQ AAD AE L ar HI (NESKA.PMEA L).
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
Hypothesis TG0 : 0 <= tg < 2 ^ 64.
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
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_149 ())). Qed.
Local Notation "'SX' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Lemma pot_split x kb1 e1 k1 : NEMA.pot_aeA L ar (NEMA.AEST x kb1 e1 k1) = PM.credit_add (PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) x)) (EPOT e1 k1).
Proof using L ar.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_150 ())). Qed.
Lemma CR : PMSP.credit_le (PM.credit_add (PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) sa)) QE) cr.
Proof using CRF.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_151 ())). Qed.
Lemma xinv0 : PQAKENA.xinvG L ar oa ov osk oec cat M (PQMA.a_kb sa) kbb en k bf ef.
Proof using KC U8 ENA SKA ECS ERR.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_152 ())). Qed.

Lemma sp_facts : 140735332487264 + 16 <= V2 /\ V2 + cls <= 140737488355328 /\ (V2 + cls) mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof using ENT Hcls.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_153 ())). Qed.
Lemma V2_lo : 140735332487328 <= V2.
Proof using ENT Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_154 ())). Qed.
Lemma HSPCf : sp - 2048 <= spc /\ spc mod 16 = 0.
Proof using Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_155 ())). Qed.
Lemma oec_rng : 7036928 <= oec /\ oec + 16 <= 2 ^ 47.
Proof using LY HIok HH AOEC.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_156 ())). Qed.
Lemma oa_lo96 : 7036928 <= oa /\ oa + 96 <= 2 ^ 47.
Proof using LY HIok HH AO.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_157 ())). Qed.
Lemma ov_rng56 : 7036928 <= ov /\ ov + 56 <= ahl_ceil ar /\ ov + 56 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784).
Proof using LY HIok HH AOV.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_158 ())). Qed.
Lemma tg_rng : 0 <= tg < 2 ^ 64.
Proof using TG0.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_159 ())). Qed.
(* [comment removed for export] *)
Lemma DKB_facts : 0 <= NB /\ 0 <= n < 2 ^ 26 /\ NB <= 2 * n + 1.
Proof using Hn26.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_160 ())). Qed.
(* [comment removed for export] *)
Lemma VOKf : L5.u64_at RSEGS M pv d /\ L5.u64_at RSEGS M (pv + 8) n /\ L5.defined M d n /\ accA M pv 16 /\ accA M d n
  /\ (n = 0 \/ PGS.in_blk LBX d n \/ PMSPA.aobjA FF d n) /\ (pv + 16 <= oa \/ oa + PQMA.ASIZE <= pv) /\ (d + n <= oa \/ oa + PQMA.ASIZE <= d)
  /\ (pv + 16 <= ov \/ ov + 56 <= pv) /\ (d + n <= ov \/ ov + 56 <= d) /\ (pv + 16 <= osk \/ osk + 24 <= pv) /\ (d + n <= osk \/ osk + 24 <= d) /\ 0 <= d /\ d + n <= 2 ^ 47.
Proof using VOK.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_161 ())). Qed.
Lemma pv_rng : 7036928 <= pv /\ pv + 16 <= 2 ^ 47.
Proof using LY HIok HH APV.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_162 ())). Qed.
Lemma GOWNE : forall Ma Mb, OWN Ma -> (forall a, OC a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> OWN Mb.
Proof using ENT Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_163 ())). Qed.

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
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_164 ())). Qed.
Lemma DKB_DPHI : DKB + 1 <= DPHI /\ NEM.hdr_str NB + NB <= DPHI /\ NEM.hdr_bin n + n <= DPHI.
Proof using Hn26.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_165 ())). Qed.
(* [comment removed for export] *)
Lemma ndest_adv lv0 c : NEMA.ndest (lv0 ++ [PQAKS3N.adv c]) = NEMA.ndest (lv0 ++ [c]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_166 ())). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition XV (Mx : mem) : Prop := PMFA.agA M Mx pv 16 /\ (PMSPA.aobjA FF d n -> PMFA.agA M Mx d n).
Lemma agA_refl (Mx : mem) a m : PMFA.agA Mx Mx a m.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_167 ())). Qed.
Lemma xv0 : XV M.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_168 ())). Qed.
(* [comment removed for export] *)
Ltac vf LM XVM :=
  destruct ((SV PQAKS3BN.s_pv) _ _ _ _ _ _ _ _ LM (proj1 XVM)) as ((PV1 & PV2 & PV3 & PV4 & PV5) & (PW0 & PW8) & (PZ0 & PZ8) & (Hd1 & Hd2 & Hn1) & PVO & (PVF & PSF0 & PSF8));
  change (ff_bytes 1) with 128 in PVF; change (ff_bytes 1 / 8) with 16 in PSF0, PSF8.

(* [comment removed for export] *)
Lemma xv_ek LB1 spx scr W (M1 M3 : mem) :
  L5SAR.ek L ar LB1 FF spx scr W M1 M3 -> PMKA.wapp W ->
  (forall i, pv <= i < pv + 16 -> L5.outside W i) -> (PMSPA.aobjA FF d n -> forall i, d <= i < d + n -> L5.outside W i) -> XV M1 -> XV M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_169 ())). Qed.
(* [comment removed for export] *)
Lemma xvF M1 model1 LK1 Aw1 st1 eso1 qe1 cr1 (M3 : mem) (Wp : Z -> Prop) :
  AMF M1 model1 LK1 Aw1 st1 eso1 qe1 cr1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (spc <= a < sp) \/ (F <= a < F + ff_bytes 1) \/ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 1 / 8)) ->
  XV M1 -> XV M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_170 ())). Qed.
(* [comment removed for export] *)
Lemma xv_ptw (M1 M3 : mem) (Wx : Z -> Prop) :
  (forall i, 0 <= i < 2 ^ 64 -> ~ Wx i -> M3 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) ->
  (forall i, pv <= i < pv + 16 -> ~ Wx i /\ ~ Wx (HeapIfaceA.S i)) ->
  (PMSPA.aobjA FF d n -> forall i, d <= i < d + n -> ~ Wx i /\ ~ Wx (HeapIfaceA.S i)) ->
  XV M1 -> XV M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_171 ())). Qed.

(* [comment removed for export] *)
Lemma FIN M5 model5 LK5 Aw5 st5 cr5 kbb5 en5 k5 (b5 e5 : bool) (fx5 : FPState) R5 :
  AMF M5 model5 LK5 Aw5 st5 (NECS.eown en5 k5) (EPOT en5 k5) cr5 -> REGSA R5 -> xinv M5 (PQMA.a_kb st5) kbb5 en5 k5 b5 e5 -> EST en5 k5 b5 e5 ->
  PQMA.nlv st5 = PQMA.nlv sa -> PQMA.kbsize st5 <= PQMA.kbsize sa + DKB -> PQMA.kbsize st5 + NESK.sk_z k5 <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st5) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb62d0 M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_172 ())). Qed.


(* [comment removed for export] *)
Lemma ADV M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 en1 k1 (b1 e1 : bool) (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 (NECS.eown en1 k1) (EPOT en1 k1) cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en1 k1 b1 e1 -> EST en1 k1 b1 e1 ->
  PQMA.a_lv st1 = lv0 ++ [c] ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 <= PQMA.kbsize sa + DKB -> PQMA.kbsize st1 + NESK.sk_z k1 <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st1) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb6258 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_173 ())). Qed.


(* [comment removed for export] *)
Ltac of LM ELV :=
  destruct ((SF PQAKS3N.s_oa) _ _ _ _ _ _ _ _ LM) as ((OA1 & OA2 & OA3 & OA4 & OA5) & OAZ & O16 & (OV1 & OV2 & OV3 & OV4 & OVZ & OVW) & IMG & VTZ & (OAF & OVF & OASF & OVSF) & (OAV & OAW));
  destruct ((SF PQAKS3N.s_lv) _ _ _ _ _ _ _ _ _ _ LM ELV) as (E80 & (E1 & E2 & E8 & E4 & E5) & (Z24 & Z20 & Z16 & Z8) & (CT & CK & CEO) & (CD & CW & CVIS) & (EO1 & EF1 & EV1) & ((CTR & CKR & CER & CKE) & CT1) & INL & EHI);
  change (ff_bytes 1) with 128 in OAF, OVF; change (ff_bytes 1 / 8) with 16 in OASF, OVSF.

(* [comment removed for export] *)
Lemma PATH_D M1 model1 LK1 Aw1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> XV M1 -> PQMA.a_lv sa = lv0 ++ [c] -> PQMA.lv_t c = 0 -> PQMA.lv_eo c = 1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5d54 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_174 ())). Qed.

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
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_175 ())). Qed.

(* [comment removed for export] *)
Lemma CQV M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs ->
  getr R1 (reg 21) = Z_to_bv 64 (oa + 48) -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + DKB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb6118 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_176 ())). Qed.
(* [comment removed for export] *)
Lemma COLON M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs ->
  getr R1 (reg 21) = Z_to_bv 64 (oa + 48) -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + DKB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb624c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_177 ())). Qed.
(* [comment removed for export] *)
Lemma CQK M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs ->
  getr R1 (reg 21) = Z_to_bv 64 (oa + 48) -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 2 <= PQMA.kbsize sa + DKB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb6240 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_178 ())). Qed.

(* [comment removed for export] *)
Lemma div2_2 m : (2 * m) / 2 = m.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_179 ())). Qed.
(* [comment removed for export] *)
Lemma INS_CALL (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 (ra v11 v12 v13 v14 : Z) :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48) ->
  ra = (if arm then 0xb6118 else 0xb6240) ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 v11 -> getr R1 (reg 12) = Z_to_bv 64 v12 ->
  getr R1 (reg 13) = Z_to_bv 64 v13 -> getr R1 (reg 14) = Z_to_bv 64 v14 ->
  v11 = PM.vs_data (oa + 48) (PQMA.a_kb st1) + PM.vs_size (PQMA.a_kb st1) -> v12 = PM.vs_data (oa + 24) (PQMA.a_key st1) ->
  v13 = v12 + v14 -> v14 = PM.vs_size (PQMA.a_key st1) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + v14 + (if arm then 1 else 2) <= PQMA.kbsize sa + DKB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb95f0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_180 ())). Qed.

Lemma INS2 (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + PM.vs_size (PQMA.a_key st1) + (if arm then 1 else 2) <= PQMA.kbsize sa + DKB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if arm then 0xb5efc else 0xb5f64) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_181 ())). Qed.

(* [comment removed for export] *)
Lemma KDEST M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.lv_t c = 0 -> PQMA.lv_eo c = 0 ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 = PQMA.kbsize sa -> PM.vs_size (PQMA.a_key st1) = NB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5e5c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_182 ())). Qed.

(* [comment removed for export] *)
Lemma QUOTE (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = true -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + 1 + PM.vs_size (PQMA.a_key st1) + (if arm then 1 else 2) <= PQMA.kbsize sa + DKB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if arm then 0xb5ef0 else 0xb5f54) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_183 ())). Qed.

(* [comment removed for export] *)
Lemma COMMA (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSB R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = true -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  getr R1 (reg 1) = Z_to_bv 64 (if arm then 0xb5ef0 else 0xb5f54) -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 44 ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + 2 + PM.vs_size (PQMA.a_key st1) + (if arm then 1 else 2) <= PQMA.kbsize sa + DKB -> 0 <= PM.vs_size (PQMA.a_key st1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xf4640 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_184 ())). Qed.

(* [comment removed for export] *)
Lemma DISP2 M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> (PQMA.lv_eo c = 0 \/ PQMA.lv_t c = 1) ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 = PQMA.kbsize sa -> PM.vs_size (PQMA.a_key st1) = NB ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5e5c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_185 ())). Qed.

(* [comment removed for export] *)
Lemma KEYB64 M1 model1 LK1 Aw1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> XV M1 -> PQMA.a_lv sa = lv0 ++ [c] -> (PQMA.lv_eo c = 0 \/ PQMA.lv_t c = 1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5d54 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_186 ())). Qed.

(* [comment removed for export] *)
Lemma DISP1 M1 model1 LK1 Aw1 cr1 kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> XV M1 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb5d54 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_187 ())). Qed.

(* [comment removed for export] *)
Lemma SETUP Mx modelx LKx Awx (fx2 : FPState) R2 :
  AMF Mx modelx LKx Awx sa ESO QE cr -> xinv Mx (PQMA.a_kb sa) kbb en k bf ef -> XV Mx ->
  getr R2 (reg 2) = Z_to_bv 64 spc -> getr R2 (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R2 (reg 8) = Z_to_bv 64 sp ->
  getr R2 (reg 9) = Z_to_bv 64 spc -> getr R2 (reg 10) = Z_to_bv 64 F -> getr R2 (reg 20) = Z_to_bv 64 oa -> getr R2 (reg 21) = Z_to_bv 64 ctx -> getr R2 (reg 23) = Z_to_bv 64 tg -> getr R2 (reg 24) = Z_to_bv 64 pv ->
  getr R2 (reg 27) = Z_to_bv 64 2147450880 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0xb5ca0 Mx modelx) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_188 ())). Qed.


End Frame.

(* [comment removed for export] *)
Ltac enter_tac Aconc fxv MVv HRgp HRtp :=
  pose proof (LF2CBN( Aconc fxv R MVv (fun j : nat => match j with 2%nat => V2 | _ => 0 end) )) as P;
  L5SAR.feed P ltac:(fd);
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T20 & T21 & T23 & T24 & T27 & CEC & C27 & C26 & C25 & C24 & C23 & C22 & C21 & C20 & C19 & C18 & C9 & C8 & C1 & C0);
  apply ((SX PQAKS3N.s_enterX) spc (V2 - 136) sp OC OWN 1 fxv fx1 R1 0xb5bd0 744528 M1v CR);
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

Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb5c20 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_189 ())). Qed.

End Run.

(* [comment removed for export] *)
Theorem bstr_raw_ok : PNVA.v_bstr_raw_spec RSEGS AD AQ AAD AE L ar HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdBr ()) ["WithHeap"] (Mh_0230_blobs1.kr_b_190 ())). Qed.

End WithHeap.
End PQAABR.


End PnAAdBr.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndP_Na_098. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0171.
Module PnAAdPbP.
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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndP_Na_098. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0171. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0171.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdPbP () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP7KS_qspSC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspS<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthc69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z<eq_decidableK46Stdlib9micromega:ZMicromega;ZArithProof03c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspS6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspS3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP:KS_qspS_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLI5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLI9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP8KS_qspLIC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLI<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLI3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLI2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLI3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLI6cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLI3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLI3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP;KS_qspLI_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspGS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspGS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP8KS_qspGSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspGS<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspGS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspGS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspGS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspGS6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspGS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspGS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP;KS_qspGS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLG9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP8KS_qspLGC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLG<seg_sound_axC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z:mul_div_leK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLG6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspLG3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP;KS_qspLG_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspN9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP7KS_qspNC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspN<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspN3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspN3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP:KS_qspN_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspD9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP7KS_qspDC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspD<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspD3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP:KS_qspD_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspT5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspT9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP7KS_qspTC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspT<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspT3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspT2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspT3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspT6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspT3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP5PqspT3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP:KS_qspT_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspTS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspTS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP8KS_qspTSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspTS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspTS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspTS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspTS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspTS6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspTS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP6PqspTS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP;KS_qspTS_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAAPBP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_191 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_192 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_193 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_194 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_195 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_196 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_197 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_198 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_199 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_200 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_201 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_202 ())). Qed.
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
Module PqspS := BndP_Na_098.LibSegNa_qspS.
Definition KS_qspS : list nat := Eval vm_compute in (BG.kept_list 60 PqspS.regs0 PqspS.regs_out0).
Lemma KS_qspS_ok : BG.kept_ok 60 PqspS.regs0 PqspS.regs_out0 KS_qspS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_203 ())). Qed.
Lemma qspS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 7036928 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 43 -> Z.testbit (V 33%nat) 0 = false -> 0 <= (bv_unsigned (getr R (reg 11))) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xf4640 M) (st fx' R' 0xf4770 M')
        /\ (forall x, In x KS_qspS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 2) 0
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 1) (bv_unsigned (getr R (reg 11)))
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 10))) ((V 33%nat) + 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_204 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqspLI := BndP_Na_097.LibSegNa_qspLI.
Definition KS_qspLI : list nat := Eval vm_compute in (BG.kept_list 60 PqspLI.regs0 PqspLI.regs_out0).
Lemma KS_qspLI_ok : BG.kept_ok 60 PqspLI.regs0 PqspLI.regs_out0 KS_qspLI = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_205 ())). Qed.
Lemma qspLI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 7036928 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 36%nat) -> Z.testbit (V 36%nat) 0 = true ->
  27 <= (V 36%nat) <= 2147483649 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 2147483648 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) (V 35%nat) ->
  4096 <= (V 35%nat) <= 140737488355328 -> 0 <= (bv_unsigned (getr R (reg 11))) <= 255 -> 1 <= (((V 34%nat) - ((((2 * ((V 36%nat) / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) -> L5.writable RSEGS M ((V 35%nat) + (V 34%nat)) 2 ->
  (((V 35%nat) + (V 34%nat)) + 2 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 35%nat) + (V 34%nat))) -> (((V 35%nat) + (V 34%nat)) + 2 <= ((V 2%nat) - 64) \/ ((V 2%nat) - 64) + 64 <= ((V 35%nat) + (V 34%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> ~ ((((V 35%nat) + (V 34%nat)) + 0) <= bv_unsigned a < (((V 35%nat) + (V 34%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> ~ ((((V 35%nat) + (V 34%nat)) + 0) <= i < (((V 35%nat) + (V 34%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xf4640 M) (st fx' R' 0xf4770 M')
        /\ (forall x, In x KS_qspLI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ L5.u8_at RSEGS M' (((V 34%nat) + (V 35%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 34%nat) + (V 35%nat)) (bv_unsigned (getr R (reg 11)))
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) ((V 34%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 10))) (V 33%nat)
        /\ L5.u64_at RSEGS M' (bv_unsigned (getr R (reg 10))) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 16) (V 35%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_206 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqspGS := BndP_Na_097.LibSegNa_qspGS.
Definition KS_qspGS : list nat := Eval vm_compute in (BG.kept_list 60 PqspGS.regs0 PqspGS.regs_out0).
Lemma KS_qspGS_ok : BG.kept_ok 60 PqspGS.regs0 PqspGS.regs_out0 KS_qspGS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_207 ())). Qed.
Lemma qspGS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 7036928 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) 44 ->
  0 <= (bv_unsigned (getr R (reg 11))) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xf4640 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_qspGS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1001220
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 11)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 48
        /\ getr R' (reg 12) = Z_to_bv 64 44
        /\ getr R' (reg 18) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 1)
        /\ getr R' (reg 19) = Z_to_bv 64 48
        /\ getr R' (reg 20) = Z_to_bv 64 22
        /\ getr R' (reg 21) = Z_to_bv 64 23
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_208 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqspLG := BndP_Na_097.LibSegNa_qspLG.
Definition KS_qspLG : list nat := Eval vm_compute in (BG.kept_list 60 PqspLG.regs0 PqspLG.regs_out0).
Lemma KS_qspLG_ok : BG.kept_ok 60 PqspLG.regs0 PqspLG.regs_out0 KS_qspLG = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_209 ())). Qed.
Lemma qspLG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 7036928 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 36%nat) -> Z.testbit (V 36%nat) 0 = true ->
  27 <= (V 36%nat) <= 2147483649 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 2147483648 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) (V 35%nat) ->
  4096 <= (V 35%nat) <= 140737488355328 -> 0 <= (bv_unsigned (getr R (reg 11))) <= 255 -> (((V 34%nat) - ((((2 * ((V 36%nat) / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) < 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xf4640 M) (st fx' R' 0x14f7a0 M')
        /\ (forall x, In x KS_qspLG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1001220
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 11)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 ((8 * (((4 * ((V 36%nat) / 2)) - 2) / 8)) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 12
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((8 * (((4 * ((V 36%nat) / 2)) - 2) / 8)) + 8)
        /\ getr R' (reg 20) = Z_to_bv 64 ((2 * ((V 36%nat) / 2)) - 1)
        /\ getr R' (reg 21) = Z_to_bv 64 (2 * ((V 36%nat) / 2))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_210 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqspN := BndP_Na_097.LibSegNa_qspN.
Definition KS_qspN : list nat := Eval vm_compute in (BG.kept_list 60 PqspN.regs0 PqspN.regs_out0).
Lemma KS_qspN_ok : BG.kept_ok 60 PqspN.regs0 PqspN.regs_out0 KS_qspN = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_211 ())). Qed.
Lemma qspN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 56%nat) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 39%nat) -> getr R (reg 21) = Z_to_bv 64 (V 40%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 7036928 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xf4704 M) (st fx' R' 0x7ebb4 M')
        /\ (forall x, In x KS_qspN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1001236
        /\ getr R' (reg 11) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 37%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_212 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqspD := BndP_Na_097.LibSegNa_qspD.
Definition KS_qspD : list nat := Eval vm_compute in (BG.kept_list 60 PqspD.regs0 PqspD.regs_out0).
Lemma KS_qspD_ok : BG.kept_ok 60 PqspD.regs0 PqspD.regs_out0 KS_qspD = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_213 ())). Qed.
Lemma qspD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 56%nat) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 39%nat) -> getr R (reg 21) = Z_to_bv 64 (V 40%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 7036928 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 26 <= (V 40%nat) <= 2147483649 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xf4714 M) (st fx' R' 0xf1fc0 M')
        /\ (forall x, In x KS_qspD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1001256
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_214 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqspT := BndP_Na_098.LibSegNa_qspT.
Definition KS_qspT : list nat := Eval vm_compute in (BG.kept_list 60 PqspT.regs0 PqspT.regs_out0).
Lemma KS_qspT_ok : BG.kept_ok 60 PqspT.regs0 PqspT.regs_out0 KS_qspT = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_215 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma qspT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 56%nat) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 39%nat) -> getr R (reg 21) = Z_to_bv 64 (V 40%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 7036928 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 0 <= (V 56%nat) <= 255 ->
  4096 <= (V 37%nat) <= 140737488355328 -> 0 <= (V 39%nat) <= 2147483648 -> 26 <= (V 38%nat) <= 2147483649 -> L5.writable RSEGS M ((V 37%nat) + (V 39%nat)) 2 ->
  (((V 37%nat) + (V 39%nat)) + 2 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 37%nat) + (V 39%nat))) -> (((V 37%nat) + (V 39%nat)) + 2 <= ((V 2%nat) - 64) \/ ((V 2%nat) - 64) + 64 <= ((V 37%nat) + (V 39%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> ~ ((((V 37%nat) + (V 39%nat)) + 0) <= bv_unsigned a < (((V 37%nat) + (V 39%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> ~ ((((V 37%nat) + (V 39%nat)) + 0) <= i < (((V 37%nat) + (V 39%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xf4728 M) (st fx' R' 0xf4770 M')
        /\ (forall x, In x KS_qspT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + (V 39%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 39%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ L5.u8_at RSEGS M' (((V 37%nat) + (V 39%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 37%nat) + (V 39%nat)) (V 56%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) ((V 39%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' (V 10%nat) ((2 * ((V 38%nat) / 2)) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_216 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqspTS := BndP_Na_098.LibSegNa_qspTS.
Definition KS_qspTS : list nat := Eval vm_compute in (BG.kept_list 60 PqspTS.regs0 PqspTS.regs_out0).
Lemma KS_qspTS_ok : BG.kept_ok 60 PqspTS.regs0 PqspTS.regs_out0 KS_qspTS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_217 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma qspTS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 56%nat) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (V 39%nat) -> getr R (reg 21) = Z_to_bv 64 23 -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 7036928 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 0 <= (V 56%nat) <= 255 ->
  4096 <= (V 37%nat) <= 140737488355328 -> 0 <= (V 39%nat) <= 2147483648 -> 26 <= (V 38%nat) <= 2147483649 -> L5.writable RSEGS M ((V 37%nat) + (V 39%nat)) 2 ->
  (((V 37%nat) + (V 39%nat)) + 2 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 37%nat) + (V 39%nat))) -> (((V 37%nat) + (V 39%nat)) + 2 <= ((V 2%nat) - 64) \/ ((V 2%nat) - 64) + 64 <= ((V 37%nat) + (V 39%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> ~ ((((V 37%nat) + (V 39%nat)) + 0) <= bv_unsigned a < (((V 37%nat) + (V 39%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> ~ ((((V 37%nat) + (V 39%nat)) + 0) <= i < (((V 37%nat) + (V 39%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xf4714 M) (st fx' R' 0xf4770 M')
        /\ (forall x, In x KS_qspTS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + (V 39%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 39%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ L5.u8_at RSEGS M' (((V 37%nat) + (V 39%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 37%nat) + (V 39%nat)) (V 56%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) ((V 39%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' (V 10%nat) ((2 * ((V 38%nat) / 2)) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbP ()) [] (Mh_0230_blobs1.kr_b_218 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

End PQAAPBP.

End PnAAdPbP.
Module PnAAdPbS2P.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndP_Na_098.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdPbS2P () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P6PqspS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P6PqspS29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P8KS_qspS2C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P6PqspS2<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z<eq_decidableC69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthc69OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InK46Stdlib9micromega:ZMicromega;ZArithProof03c69OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P6PqspS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P6PqspS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P6PqspS23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P6PqspS26cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P6PqspS23kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P6PqspS23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdPbS2P9PQAAPBS2P;KS_qspS2_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAAPBS2P.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_219 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_220 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_221 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_222 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_223 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_224 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_225 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_226 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_227 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_228 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_229 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_230 ())). Qed.
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
Module PqspS2 := BndP_Na_098.LibSegNa_qspS2.
Definition KS_qspS2 : list nat := Eval vm_compute in (BG.kept_list 60 PqspS2.regs0 PqspS2.regs_out0).
Lemma KS_qspS2_ok : BG.kept_ok 60 PqspS2.regs0 PqspS2.regs_out0 KS_qspS2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_231 ())). Qed.
Lemma qspS2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 7036928 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 43 -> Z.testbit (V 33%nat) 0 = false -> 0 <= (bv_unsigned (getr R (reg 11))) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 1) -> ~ ((((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 1) <= bv_unsigned a < (((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 1) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 1) -> ~ ((((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 1) <= i < (((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 1) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xf4640 M) (st fx' R' 0xf4770 M')
        /\ (forall x, In x KS_qspS2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 2) 0
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + ((V 33%nat) / 2)) + 1) (bv_unsigned (getr R (reg 11)))
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 10))) ((V 33%nat) + 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbS2P ()) [] (Mh_0230_blobs1.kr_b_232 ())). Qed.
(* [comment removed for export] *)

End PQAAPBS2P.

End PnAAdPbS2P.
From Stdlib Require ZArith List Lia Bool FunctionalExtensionality. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012.
Module PnAAdPbC1.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdStrCK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0247.PnARzKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKStrA3c OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdPbP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdPbS2P OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAdStrCK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKMoveCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012.Na0_code_rd36f8_d36fc.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdPbC1 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib5Lists4List:length_appK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib9PnAdStrCK6PQASCK=bytes_at_snocC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib9PnAdStrCK6PQASCK<bytes_ok_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC13KCFC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib5Lists4List2InC56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedc69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC15kept0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARBpreserved_by_indexC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8vis_packC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA=aobj_of_aobjAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t01C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:aobj_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_hiC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC16vfactsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u64_at_visC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notc69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC15savesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC16mem_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC16bfactsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<aclient_appbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAReset16PMARS1?own_not_aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6ek_memC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6dk_memC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8dk_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<stack_clientC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=astk_after_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA;S_in_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA6S_monoC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA:accA_agreeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC1:saves_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:shadow_blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00K47Corelib4Init9Datatypes6option01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC14stokC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6adebitC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC19saves_visC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4aobjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A<writable_visC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=astk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP9qspN_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_addC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8astk_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC18aacc_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ>model_rt_transC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC16sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC19saves_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC1:mem_ok_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC18accA_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC14tailC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225:PnAKMoveCA7PQAKMVC@move_stage_preNCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdPbP7PQAAPBP7KS_qspNC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4KCAPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC1?after_move_longC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8ks_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA7ly_costC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_b_linC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA6gcountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7ks_growC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA<pot_ks_growAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:acredit_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4GMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9ek_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA9wapp_consC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9dk_calleeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA5akeptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA:acc_keepA'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA9OPNEW_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC18grow_lawC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnRunAa5PQRAa<opnew_n_specC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6afreshC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC19saves_newC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC1:mem_ok_newC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA7mod16_8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC1=aacc_of_blockC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:obj_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC1?after_new_shortC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR4NREQC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02478PnARzKit6PMARZK;agsh_ahpresC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<block_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC1>after_new_longC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv=Z_div_exact_2C56Stdlib6ZArith6BinInt1Z9div_add_lK46Stdlib9micromega=RingMicromega3Op206C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z9mod_smallC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullK46Stdlib9micromega:ZMicromega;ZArithProof03c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC15capm1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02309PnAAdPbC18PQAAPBC15half2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_0_lC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=aclient_casesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_pieceC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8dk_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:astk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02478PnARzKit6PMARZK:agsh_frameC1?~~~~~~~~~~~~~~~".
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.

Module PQAAPBC1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation kstr_at := (PQMA.kstr_at RSEGS PMSPA.accA).
Abbreviation kcontent := (NEM.kcontent RSEGS).

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis OPN : PQRAa.opnew_n_spec L ar HI.
Hypothesis OPD : PMA.opdel_spec L ar HI.
Hypothesis MML : PQASA.memmove_libc_n_spec L ar HI IL.
Let LYa := PMA.ly_as0 L C LY.
Abbreviation HV := (PMSPA.HV L ar).
Abbreviation scA := (PMSPA.scA L).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (o ch S r SM g : Z) (x : PM.vstr) (bs : list Z).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis STK0 : L5CA.astk ar M0 S 14336.
Hypothesis AO : PMSPA.aobjA FF o 24.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis Hch : 0 <= ch < 256.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 ch.
Hypothesis KO0 : PQMA.ks_ok SM x g.
Hypothesis HSM : SM <= PQASA.SMMAX.
Hypothesis Hroom : PM.vs_size x < SM.
Hypothesis KC0 : kcontent M0 o x bs.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
                         (x' : PM.vstr) (g' : Z) (cr' : credit),
  regs_preserved R0 R' -> kstr_at M' o x' -> kcontent M' o x' (bs ++ [ch]) -> PQMA.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + 1 ->
  (PM.vs_size x < PM.vs_cap x -> PM.vs_own x' = PM.vs_own x /\ g' = g) ->
  L5CA.ahpres L ar LB FF S (PMSPA.pm_scr PQASA.PB_H) [(o, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (scA (PQMA.pot_ks HV SM x g)) (scA (PQMA.pot_ks HV SM x' g')) ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
  ri_inv HI (PM.vs_own x' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall y, In y [3; 4; 23; 24; 25; 26; 27]%nat -> getr R (reg y) = getr R0 (reg y).
(* [comment removed for export] *)
Definition stok (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw.
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  L5SAR.ek L ar LB FF S 14336 [(o, 24)] M0 M /\ L5SAR.dk L ar LB FF S 14336 M0 M /\ L5CA.astk ar M S 14336 /\ PMSPA.accA M o 24.

(* [comment removed for export] *)
Lemma KCF : L5.bytes_at RSEGS M0 (PM.vs_data o x) bs /\ NEM.bytes_ok bs /\ Z.of_nat (length bs) = PM.vs_size x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_233 ())). Qed.
(* [comment removed for export] *)
Lemma kc_snoc M d x' : PM.vs_data o x' = d -> PM.vs_size x' = PM.vs_size x + 1 ->
  L5.bytes_at RSEGS M d bs -> L5.u8_at RSEGS M (d + PM.vs_size x) ch -> kcontent M o x' (bs ++ [ch]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_234 ())). Qed.

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_235 ())). Qed.

(* [comment removed for export] *)
Lemma regs_back (R1 : bvmap 5 word) :
  getr R1 (reg 2) = Z_to_bv 64 S -> getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) ->
  getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) -> getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) ->
  getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) -> getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) ->
  getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) -> getr R1 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) ->
  kept0 R1 -> regs_preserved R0 R1.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_236 ())). Qed.

(* [comment removed for export] *)
Lemma vfacts LB' LK cr Aw M model :
  ri_inv HI LB' FF LK cr Aw M (vml_of model) -> L5CA.astk ar M S 14336 ->
  (forall a m, S - 14336 <= a -> a + m <= 2 ^ 47 -> L5A.avis (ahid Aw model) a m)
  /\ (0x6b6000 <= o /\ o + 24 <= ahl_ceil ar /\ (0x7fff7000 + 17592186048512 <= o \/ o + 24 <= 0x7fff7000))
  /\ L5.defined M o 24 /\ L5A.avis (ahid Aw model) o 24
  /\ (forall q m a k, In (q, m) LB' -> q <= a -> a + k <= q + m -> L5A.avis (ahid Aw model) a k).
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_237 ())). Qed.

(* [comment removed for export] *)
Lemma bfacts LB' LK cr Aw M V q m :
  ri_inv HI LB' FF LK cr Aw M V -> In (q, m) LB' ->
  4096 <= q /\ (q + m <= 0x10000 \/ 0x6b6000 <= q) /\ q mod 16 = 0 /\ 0 < m /\ q + m <= ahl_ceil ar /\ (q + m <= 0x7fff7000 \/ 0x10007fff8000 <= q)
  /\ q + m <= 2 ^ 47 /\ L5.defined M q m /\ (q + m <= o \/ o + 24 <= q).
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_238 ())). Qed.

(* [comment removed for export] *)
Lemma saves_vis LB' LK cr Aw M model :
  ri_inv HI LB' FF LK cr Aw M (vml_of model) -> L5CA.astk ar M S 14336 ->
  forall a v, S - 64 <= a -> a + 8 <= S -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS (mrestrict (ahid Aw model) M) a v.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_239 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail (fx : FPState) R M model LK Aw (n p A B pc a0 s5 g' : Z) (cr' : credit) :
  stok model LK Aw -> n = PM.vs_size x -> 0 <= n -> n + 2 <= A -> 26 <= A <= PQMA.KCAP -> A mod 8 = 0 ->
  (pc = 0xf4714 /\ s5 = 23 \/ pc = 0xf4728) ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 a0 ->
  getr R (reg 18) = Z_to_bv 64 p -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 n -> getr R (reg 21) = Z_to_bv 64 s5 -> getr R (reg 22) = Z_to_bv 64 B ->
  0 <= a0 < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= s5 < 2 ^ 64 ->
  kept0 R -> saves M -> mem_ok M -> PMSPA.accA M B A -> L5.bytes_at RSEGS M B bs ->
  ri_inv HI ((B, A) :: LB) FF LK cr' Aw M (vml_of model) ->
  PQMA.ks_ok SM (PM.VLong A (n + 1) B) g' -> PM.vs_cap x = n ->
  PMSP.credit_keep cr0 cr' (scA (PQMA.pot_ks HV SM x g)) (scA (PQMA.pot_ks HV SM (PM.VLong A (n + 1) B) g')) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R pc M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_240 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aacc_sub (M : word -> option byte) a k a' k' : aacc M a k -> a <= a' -> a' + k' <= a + k -> aacc M a' k'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_241 ())). Qed.

Lemma saves_keep (M M' : word -> option byte) (P : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> (forall a, S - 64 <= a < S -> ~ P a) ->
  140735332483136 <= S <= 2 ^ 47 -> saves M -> saves M'.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_242 ())). Qed.

(* [comment removed for export] *)
Lemma mem_ok_mem (M M1 : word -> option byte) (LBo : list (Z * Z)) LK cr Aw model (dst len : Z) :
  ri_inv HI (LBo ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (LBo ++ LB) FF (S - 64) 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, S - 64 - 2560 <= a < S - 64 -> M1 (Z_to_bv 64 a) <> None) -> L5.defined M1 dst len ->
  (exists q A, In (q, A) LBo /\ q <= dst /\ dst + len <= q + A) ->
  mem_ok M1.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_243 ())). Qed.

(* [comment removed for export] *)
Lemma accA_mem (M M1 : word -> option byte) (LB' : list (Z * Z)) (dst len q A : Z) :
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB' FF (S - 64) 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  In (q, A) LB' -> 0 <= q -> q + A <= 2 ^ 47 -> (dst + len <= 0x7fff7000 \/ 0x10007fff8000 <= dst) -> PMSPA.accA M q A -> PMSPA.accA M1 q A.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_244 ())). Qed.

(* [comment removed for export] *)
Lemma saves_mem (M M1 : word -> option byte) (LB' : list (Z * Z)) (dst len : Z) :
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB' FF (S - 64) 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  dst + len <= ahl_ceil ar -> ahl_ceil ar + 4096 + 14336 <= S -> S <= 2 ^ 47 -> 0x7fff80000000 <= ar_sptop ar -> 0 <= len -> saves M -> saves M1.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_245 ())). Qed.

Lemma aacc_of_block (M : word -> option byte) u m p k : shadow_blk M u m -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + k <= u + m -> aacc M p k.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_246 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_new_short (fx : FPState) R M model LK Aw (A B : Z) :
  stok model LK Aw -> PM.vs_size x = 22 -> PM.vs_cap x = 22 -> 26 <= A <= PQMA.KCAP -> A mod 8 = 0 ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 (o + 1) -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 22 -> getr R (reg 21) = Z_to_bv 64 23 ->
  kept0 R -> saves M -> mem_ok M -> PMSPA.accA M B A -> L5.bytes_at RSEGS M (o + 1) bs ->
  ri_inv HI ((B, A) :: LB) FF LK (adebit L cr0 A) Aw M (vml_of model) ->
  PQMA.ks_ok SM (PM.VLong A (22 + 1) B) (g + 1) ->
  PMSP.credit_keep cr0 (adebit L cr0 A) (scA (PQMA.pot_ks HV SM x g)) (scA (PQMA.pot_ks HV SM (PM.VLong A (22 + 1) B) (g + 1))) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xf4704 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_247 ())). Qed.

(* [comment removed for export] *)
Lemma after_move_long (fx : FPState) R M model LK Aw (n q c A B a0 : Z) :
  stok model LK Aw -> n = PM.vs_size x -> PM.vs_cap x = n -> 1 <= n -> n + 2 <= A -> 26 <= A <= PQMA.KCAP -> A mod 8 = 0 -> 26 <= c <= PQMA.KCAP -> n < c ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 a0 ->
  getr R (reg 18) = Z_to_bv 64 q -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 n -> getr R (reg 21) = Z_to_bv 64 c -> getr R (reg 22) = Z_to_bv 64 B ->
  0 <= a0 < 2 ^ 64 ->
  kept0 R -> saves M -> mem_ok M -> PMSPA.accA M B A -> B <> q -> L5.bytes_at RSEGS M B bs ->
  ri_inv HI ((B, A) :: (q, c) :: LB) FF LK (adebit L cr0 A) Aw M (vml_of model) ->
  PQMA.ks_ok SM (PM.VLong A (n + 1) B) (g + 1) ->
  PMSP.credit_keep cr0 (adebit L cr0 A) (scA (PQMA.pot_ks HV SM x g)) (scA (PQMA.pot_ks HV SM (PM.VLong A (n + 1) B) (g + 1))) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xf4714 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_248 ())). Qed.

(* [comment removed for export] *)
Lemma after_new_long (fx : FPState) R M model LK Aw (n q c A B : Z) :
  stok model LK Aw -> n = PM.vs_size x -> PM.vs_cap x = n -> 1 <= n -> n + 2 <= A -> 26 <= A <= PQMA.KCAP -> A mod 8 = 0 -> 26 <= c <= PQMA.KCAP -> n < c ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 q -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 n -> getr R (reg 21) = Z_to_bv 64 c ->
  kept0 R -> saves M -> mem_ok M -> PMSPA.accA M B A -> PMSPA.accA M q c -> (B + A <= q \/ q + c <= B) -> L5.bytes_at RSEGS M q bs ->
  ri_inv HI ((B, A) :: (q, c) :: LB) FF LK (adebit L cr0 A) Aw M (vml_of model) ->
  PQMA.ks_ok SM (PM.VLong A (n + 1) B) (g + 1) ->
  PMSP.credit_keep cr0 (adebit L cr0 A) (scA (PQMA.pot_ks HV SM x g)) (scA (PQMA.pot_ks HV SM (PM.VLong A (n + 1) B) (g + 1))) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xf4704 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_249 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_law (need n' p' : Z) :
  PM.vs_cap x < need -> need <= SM -> 0 <= n' <= SM -> n' <= need -> PQMA.ks_alloc x <= SM ->
  PMSP.credit_le (scA (PQMA.pot_ks HV SM x g)) cr0 ->
  acredit_ok L cr0 (PQASA.gcount (PM.vs_cap x) need)
  /\ PMSP.credit_keep cr0 (adebit L cr0 (PQASA.gcount (PM.vs_cap x) need)) (scA (PQMA.pot_ks HV SM x g))
                      (scA (PQMA.pot_ks HV SM (PM.VLong (PQASA.gcount (PM.vs_cap x) need) n' p') (g + 1)))
  /\ PQMA.ks_ok SM (PM.VLong (PQASA.gcount (PM.vs_cap x) need) n' p') (g + 1)
  /\ 48 <= PQASA.gcount (PM.vs_cap x) need <= 2 * SM + 8 /\ PQASA.gcount (PM.vs_cap x) need mod 8 = 0 /\ n' < PQASA.gcount (PM.vs_cap x) need
  /\ 26 <= PQASA.gcount (PM.vs_cap x) need <= PQMA.KCAP /\ PQASA.gcount (PM.vs_cap x) need mod 2 = 0.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_250 ())). Qed.

(* [comment removed for export] *)
Lemma mem_ok_new (M M3 : word -> option byte) (BX : list (Z * Z)) LK cr Aw model :
  ri_inv HI (BX ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (BX ++ LB) FF (S - 64) PMSPA.OPNEW_SCR [] M M3 -> mem_ok M3.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_251 ())). Qed.
Lemma saves_new (M M3 : word -> option byte) (LB' : list (Z * Z)) :
  L5CA.ahpres L ar LB' FF (S - 64) PMSPA.OPNEW_SCR [] M M3 -> ahl_ceil ar + 4096 + 14336 <= S -> S <= 2 ^ 47 -> 0x7fff80000000 <= ar_sptop ar ->
  saves M -> saves M3.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_252 ())). Qed.

(* [comment removed for export] *)
Lemma grow_short (fx : FPState) R M model LK Aw :
  stok model LK Aw -> x = PM.VShort 22 -> PMSP.credit_le (scA (PQMA.pot_ks HV SM x g)) cr0 ->
  getr R (reg 1) = Z_to_bv 64 0xf4704 ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 48 ->
  getr R (reg 18) = Z_to_bv 64 (o + 1) -> getr R (reg 19) = Z_to_bv 64 48 -> getr R (reg 20) = Z_to_bv 64 22 -> getr R (reg 21) = Z_to_bv 64 23 ->
  kept0 R -> saves M -> mem_ok M -> L5.bytes_at RSEGS M (o + 1) bs ->
  ri_inv HI LB FF LK cr0 Aw M (vml_of model) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x14f7a0 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_253 ())). Qed.

(* [comment removed for export] *)
Lemma grow_long (fx : FPState) R M model LK Aw (c n0 p A : Z) :
  stok model LK Aw -> x = PM.VLong c n0 p -> n0 + 1 = c -> 1 <= n0 -> PMSP.credit_le (scA (PQMA.pot_ks HV SM x g)) cr0 ->
  26 <= c <= PQMA.KCAP -> PMSPA.accA M p c -> A = PQASA.gcount (c - 1) c ->
  getr R (reg 1) = Z_to_bv 64 0xf4704 ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 A ->
  getr R (reg 18) = Z_to_bv 64 p -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 n0 -> getr R (reg 21) = Z_to_bv 64 c ->
  kept0 R -> saves M -> mem_ok M -> L5.bytes_at RSEGS M p bs ->
  ri_inv HI ((p, c) :: LB) FF LK cr0 Aw M (vml_of model) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x14f7a0 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_254 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma half2 c : c mod 2 = 0 -> 2 * ((c + 1) / 2) = c.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_255 ())). Qed.
Lemma capm1 c : 0 <= c < 2 ^ 63 -> ((c mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64 = c - 1 + (if Z.eqb c 0 then 2 ^ 64 else 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_256 ())). Qed.
Lemma wrap_ne n0 c : 0 <= n0 -> n0 + 1 < c -> c < 2 ^ 62 -> c mod 2 = 0 ->
  1 <= ((n0 - ((((2 * ((c + 1) / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_257 ())). Qed.
Lemma wrap_eq n0 c : n0 + 1 = c -> 0 < c < 2 ^ 62 -> c mod 2 = 0 ->
  ((n0 - ((((2 * ((c + 1) / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) < 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_258 ())). Qed.
Lemma newcnt c : 8 <= c -> c mod 8 = 0 -> 8 * ((4 * ((c + 1) / 2) - 2) / 8) + 8 = 2 * c.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_259 ())). Qed.

(* [comment removed for export] *)
Lemma mem_ok_frame (M M' : word -> option byte) (LBo : list (Z * Z)) LK cr Aw model :
  ri_inv HI (LBo ++ LB) FF LK cr Aw M (vml_of model) ->
  mem_ok M -> mem_grows M M' -> (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 64 <= a < S - 64 + 64) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M'.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_260 ())). Qed.

Lemma saves_of (M : word -> option byte) :
  L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))) -> L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) ->
  L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20))) -> L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) ->
  L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18))) -> L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) ->
  L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8))) -> L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) -> saves M.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnAAdPbC1 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_261 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pb_entry (fx : FPState) :
  L5CA.amodel_ok Aw0 model0 -> ri_inv HI (PM.vs_own x ++ LB) FF LK0 cr0 Aw0 M0 (vml_of model0) ->
  getr R0 (reg 10) = Z_to_bv 64 o -> kstr_at M0 o x -> PMSP.credit_le (scA (PQMA.pot_ks HV SM x g)) cr0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R0 0xf4640 M0 model0) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Call"] (Mh_0230_blobs1.kr_b_262 ())). Qed.

End Call.
End WithHeap.
End PQAAPBC1.

End PnAAdPbC1.
Module PnAAdPbC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdPbC1.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQAAPBC.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Theorem pb_ok : PQRAa.opnew_n_spec L ar HI -> PMA.opdel_spec L ar HI -> PQASA.memmove_libc_n_spec L ar HI IL ->
  PQASCA.pb_specCA RSEGS PMA.AD L ar HI 0xf4640.
Proof.
  intros OPN OPD MML. unfold PQASCA.pb_specCA.
  intros fx R M model K LB FF LK Aw cr o c sp r SM g x bs HH AM K0 ENT FRM FRS SP16 A10 A11 Hc AO O8 KS KC KO HSM ROOM CR KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr PQASA.PB_H) with 14336 in ASTK.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  exact (PQAAPBC1.pb_entry L ar C IL HI LY HIok ICok ILY OPN OPD MML R M model K LB FF LK Aw cr o c sp r SM g x bs Rra RAok Rsp Rtp K0 ASTK AO O8 Hc A11 KO HSM ROOM KC KONT
           fx AM HH A10 KS CR).
Qed.
End WithHeap.
End PQAAPBC.

End PnAAdPbC.
Module PnAAdU64P1.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdU64P1 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuA09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P18KS_qvuA0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuA0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuA03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuA06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuA03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuA03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1;KS_qvuA0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17PqvuA165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17PqvuA169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P19KS_qvuA16C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17PqvuA16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17PqvuA163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17PqvuA162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17PqvuA163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17PqvuA166cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17PqvuA163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17PqvuA163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1<KS_qvuA16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17KS_qvuBC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z<eq_decidableK46Stdlib9micromega=RingMicromega5Psatz07C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuB<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1>u8_of_KWord1maC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuB6cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1:KS_qvuB_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuQ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuQ9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P17KS_qvuQC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuQ<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuQ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuQ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuQ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuQ6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuQ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P15PqvuQ3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1:KS_qvuQ_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P18KS_qvuJ1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1;KS_qvuJ1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P18KS_qvuJ2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuJ23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1;KS_qvuJ2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuKr5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuKr9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P18KS_qvuKrC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuKr<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuKr3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuKr2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuKr3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuKr3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuKr3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1;KS_qvuKr_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P16PqvuKr6cells0C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAAU6P1.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_263 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_264 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_265 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_266 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_267 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_268 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_269 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_270 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_271 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_272 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_273 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_274 ())). Qed.
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
Module PqvuA0 := BndP_Na_120.LibSegNa_qvuA0.
Definition KS_qvuA0 : list nat := Eval vm_compute in (BG.kept_list 80 PqvuA0.regs0 PqvuA0.regs_out0).
Lemma KS_qvuA0_ok : BG.kept_ok 80 PqvuA0.regs0 PqvuA0.regs_out0 KS_qvuA0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_275 ())). Qed.
Lemma qvuA0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1320 M) (st fx' R' 0x647ec M')
        /\ (forall x, In x KS_qvuA0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725920
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1440376
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 20) = getr R (reg 10)
        /\ getr R' (reg 21) = getr R (reg 13)
        /\ getr R' (reg 23) = getr R (reg 12)
        /\ getr R' (reg 24) = getr R (reg 11)
        /\ getr R' (reg 26) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (bv_unsigned (getr R (reg 14)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_276 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuA16 := BndP_Na_120.LibSegNa_qvuA16.
Definition KS_qvuA16 : list nat := Eval vm_compute in (BG.kept_list 80 PqvuA16.regs0 PqvuA16.regs_out0).
Lemma KS_qvuA16_ok : BG.kept_ok 80 PqvuA16.regs0 PqvuA16.regs_out0 KS_qvuA16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_277 ())). Qed.
Lemma qvuA16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) + 16) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487328 <= (V 2%nat) <= 140737488355312 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 176 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1320 M) (st fx' R' 0x647ec M')
        /\ (forall x, In x KS_qvuA16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725920
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) + 16)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1440376
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 20) = getr R (reg 10)
        /\ getr R' (reg 21) = getr R (reg 13)
        /\ getr R' (reg 23) = getr R (reg 12)
        /\ getr R' (reg 24) = getr R (reg 11)
        /\ getr R' (reg 26) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (bv_unsigned (getr R (reg 14)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' (V 2%nat) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_278 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuB := BndP_Na_120.LibSegNa_qvuB.
Definition KS_qvuB : list nat := Eval vm_compute in (BG.kept_list 80 PqvuB.regs0 PqvuB.regs_out0).
Lemma KS_qvuB_ok : BG.kept_ok 80 PqvuB.regs0 PqvuB.regs_out0 KS_qvuB = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_279 ())). Qed.
Lemma qvuB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 112) 8 -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  7036928 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (V 50%nat) 24 ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> 7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) ->
  L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 -> (((((V 36%nat) + 80) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= ((((V 36%nat) + 80) / 8) + 2147450880)) -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 160)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb13a0 M) (st fx' R' 0xb1440 M')
        /\ (forall x, In x KS_qvuB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 68544
        /\ getr R' (reg 12) = Z_to_bv 64 725792
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + 80)
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 725792
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 68544
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_280 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuQ := BndP_Na_122.LibSegNa_qvuQ.
Definition KS_qvuQ : list nat := Eval vm_compute in (BG.kept_list 80 PqvuQ.regs0 PqvuQ.regs_out0).
Lemma KS_qvuQ_ok : BG.kept_ok 80 PqvuQ.regs0 PqvuQ.regs_out0 KS_qvuQ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_281 ())). Qed.
Lemma qvuQ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) ->
  7036928 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (V 50%nat) 8 ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> 140735332487328 <= (V 52%nat) <= 140737488355328 -> aligned (V 52%nat) 16 ->
  L5.u64_at RSEGS M ((V 52%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 32) (V 63%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 64) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 96) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 104) (V 72%nat) -> (((V 52%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 52%nat) - 160)) -> (((V 52%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 52%nat) - 160)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1918 M) (st fx' R' 0xb19b8 M')
        /\ (forall x, In x KS_qvuQ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 72%nat)
        /\ L5.u8_at RSEGS M' (V 51%nat) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_282 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuJ1 := BndP_Na_122.LibSegNa_qvuJ1.
Definition KS_qvuJ1 : list nat := Eval vm_compute in (BG.kept_list 80 PqvuJ1.regs0 PqvuJ1.regs_out0).
Lemma KS_qvuJ1_ok : BG.kept_ok 80 PqvuJ1.regs0 PqvuJ1.regs_out0 KS_qvuJ1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_283 ())). Qed.
Lemma qvuJ1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1684 M) (st fx' R' 0xb18a0 M')
        /\ (forall x, In x KS_qvuJ1 -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_284 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuJ2 := BndP_Na_122.LibSegNa_qvuJ2.
Definition KS_qvuJ2 : list nat := Eval vm_compute in (BG.kept_list 80 PqvuJ2.regs0 PqvuJ2.regs_out0).
Lemma KS_qvuJ2_ok : BG.kept_ok 80 PqvuJ2.regs0 PqvuJ2.regs_out0 KS_qvuJ2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_285 ())). Qed.
Lemma qvuJ2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1770 M) (st fx' R' 0xb18a0 M')
        /\ (forall x, In x KS_qvuJ2 -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_286 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuKr := BndP_Na_122.LibSegNa_qvuKr.
Definition KS_qvuKr : list nat := Eval vm_compute in (BG.kept_list 80 PqvuKr.regs0 PqvuKr.regs_out0).
Lemma KS_qvuKr_ok : BG.kept_ok 80 PqvuKr.regs0 PqvuKr.regs_out0 KS_qvuKr = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_287 ())). Qed.
Lemma qvuKr_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 27) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) ->
  7036928 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450884) 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 4) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= i < ((((V 50%nat) / 8) + 2147450880) + 4) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1844 M) (st fx' R' 0xb18a0 M')
        /\ (forall x, In x KS_qvuKr -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P1 ()) [] (Mh_0230_blobs1.kr_b_288 ())). Qed.
(* [comment removed for export] *)

End PQAAU6P1.

End PnAAdU64P1.
Module PnAAdU64P2.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdU64P2 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0L9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2:KS_qvuKe0LC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P27alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0L<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2=u8_of_KWord1aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0L3NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0L3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0L3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2=KS_qvuKe0L_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0L6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0S9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2:KS_qvuKe0SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0S<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0S3NX0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0S3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0S3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2=KS_qvuKe0S_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe0S6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1L9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2:KS_qvuKe1LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1L<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1L3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2=KS_qvuKe1L_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1L6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1S9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2:KS_qvuKe1SC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1S<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1S3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1S3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P2=KS_qvuKe1S_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P28PQAAU6P28PqvuKe1S6cells0C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAAU6P2.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_289 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_290 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_291 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_292 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_293 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_294 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_295 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_296 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_297 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_298 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_299 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_300 ())). Qed.
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
Module PqvuKe0L := BndP_Na_122.LibSegNa_qvuKe0L.
Definition KS_qvuKe0L : list nat := Eval vm_compute in (BG.kept_list 80 PqvuKe0L.regs0 PqvuKe0L.regs_out0).
Lemma KS_qvuKe0L_ok : BG.kept_ok 80 PqvuKe0L.regs0 PqvuKe0L.regs_out0 KS_qvuKe0L = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_301 ())). Qed.
Lemma qvuKe0L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 ->
  aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) ->
  0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) -> 4096 <= (V 42%nat) <= 140737488355328 -> L5.writable RSEGS M ((V 36%nat) + 32) 8 ->
  L5.writable RSEGS M (V 42%nat) 1 -> (2147446784 + 17592186048512 <= (V 42%nat) \/ (V 42%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 42%nat) / 8) + 2147450880) 1 -> ((V 42%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 96 <= (V 42%nat)) ->
  ((V 42%nat) + 1 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 42%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 32) <= bv_unsigned a < ((V 36%nat) + 32) + 8) -> ~ (((V 42%nat) + 0) <= bv_unsigned a < ((V 42%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 32) <= i < ((V 36%nat) + 32) + 8) -> ~ (((V 42%nat) + 0) <= i < ((V 42%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1440 M) (st fx' R' 0xb8fb0 M')
        /\ (forall x, In x KS_qvuKe0L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726292
        /\ getr R' (reg 10) = getr R (reg 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 32) 0
        /\ L5.u8_at RSEGS M' (V 42%nat) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_302 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuKe0S := BndP_Na_122.LibSegNa_qvuKe0S.
Definition KS_qvuKe0S : list nat := Eval vm_compute in (BG.kept_list 80 PqvuKe0S.regs0 PqvuKe0S.regs_out0).
Lemma KS_qvuKe0S_ok : BG.kept_ok 80 PqvuKe0S.regs0 PqvuKe0S.regs_out0 KS_qvuKe0S = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_303 ())). Qed.
Lemma qvuKe0S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 25) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) ->
  0 <= (V 40%nat) <= 44 -> Z.testbit (V 40%nat) 0 = false -> L5.writable RSEGS M ((V 36%nat) + 24) 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 24) <= bv_unsigned a < ((V 36%nat) + 24) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 24) <= i < ((V 36%nat) + 24) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1440 M) (st fx' R' 0xb8fb0 M')
        /\ (forall x, In x KS_qvuKe0S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726292
        /\ getr R' (reg 10) = getr R (reg 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 12) = Z_to_bv 64 ((((V 36%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 24) 0
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 25) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_304 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuKe1L := BndP_Na_122.LibSegNa_qvuKe1L.
Definition KS_qvuKe1L : list nat := Eval vm_compute in (BG.kept_list 80 PqvuKe1L.regs0 PqvuKe1L.regs_out0).
Lemma KS_qvuKe1L_ok : BG.kept_ok 80 PqvuKe1L.regs0 PqvuKe1L.regs_out0 KS_qvuKe1L = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_305 ())). Qed.
Lemma qvuKe1L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 ->
  aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 ->
  Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) -> 0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) ->
  4096 <= (V 42%nat) <= 140737488355328 -> L5.writable RSEGS M ((V 36%nat) + 32) 8 -> L5.writable RSEGS M (V 42%nat) 1 -> (2147446784 + 17592186048512 <= (V 42%nat) \/ (V 42%nat) + 1 <= 2147446784) ->
  L5KA.zeros_at M (((V 42%nat) / 8) + 2147450880) 1 -> ((V 42%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 96 <= (V 42%nat)) -> ((V 42%nat) + 1 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 42%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 32) <= bv_unsigned a < ((V 36%nat) + 32) + 8) -> ~ (((V 42%nat) + 0) <= bv_unsigned a < ((V 42%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 32) <= i < ((V 36%nat) + 32) + 8) -> ~ (((V 42%nat) + 0) <= i < ((V 42%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1440 M) (st fx' R' 0xb8fb0 M')
        /\ (forall x, In x KS_qvuKe1L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726292
        /\ getr R' (reg 10) = getr R (reg 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 32) 0
        /\ L5.u8_at RSEGS M' (V 42%nat) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_306 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuKe1S := BndP_Na_122.LibSegNa_qvuKe1S.
Definition KS_qvuKe1S : list nat := Eval vm_compute in (BG.kept_list 80 PqvuKe1S.regs0 PqvuKe1S.regs_out0).
Lemma KS_qvuKe1S_ok : BG.kept_ok 80 PqvuKe1S.regs0 PqvuKe1S.regs_out0 KS_qvuKe1S = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_307 ())). Qed.
Lemma qvuKe1S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 25) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 44 -> Z.testbit (V 40%nat) 0 = false ->
  L5.writable RSEGS M ((V 36%nat) + 24) 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 24) <= bv_unsigned a < ((V 36%nat) + 24) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 24) <= i < ((V 36%nat) + 24) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1440 M) (st fx' R' 0xb8fb0 M')
        /\ (forall x, In x KS_qvuKe1S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726292
        /\ getr R' (reg 10) = getr R (reg 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 12) = Z_to_bv 64 ((((V 36%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 24) 0
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 25) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P2 ()) [] (Mh_0230_blobs1.kr_b_308 ())). Qed.
(* [comment removed for export] *)

End PQAAU6P2.

End PnAAdU64P2.
Module PnAAdU64P3.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdU64P3 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDV25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDV29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P39KS_qvuDV2C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDV2<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDV23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDV22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDV23NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDV23kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDV23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3<KS_qvuDV2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1z9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3:KS_qvuDV1zC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1z<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1z3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3=KS_qvuDV1z_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1n9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3:KS_qvuDV1nC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1n<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P38PqvuDV1n3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3=KS_qvuDV1n_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKz5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKz9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P39KS_qvuDKzC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKz<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKz3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKz2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKz3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKz3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKz3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3<KS_qvuDKz_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKn9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P39KS_qvuDKnC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKn<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKn3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37PqvuDKn3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3<KS_qvuDKn_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P35PqvuC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P35PqvuC9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37KS_qvuCC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P35PqvuC<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P35PqvuC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P35PqvuC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P35PqvuC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P35PqvuC3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P35PqvuC3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3:KS_qvuC_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAAU6P3.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_309 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_310 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_311 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_312 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_313 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_314 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_315 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_316 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_317 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_318 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_319 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_320 ())). Qed.
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
Module PqvuDV2 := BndP_Na_121.LibSegNa_qvuDV2.
Definition KS_qvuDV2 : list nat := Eval vm_compute in (BG.kept_list 80 PqvuDV2.regs0 PqvuDV2.regs_out0).
Lemma KS_qvuDV2_ok : BG.kept_ok 80 PqvuDV2.regs0 PqvuDV2.regs_out0 KS_qvuDV2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_321 ())). Qed.
Lemma qvuDV2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 20) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 20) 2 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1514 M) (st fx' R' 0xb15a8 M')
        /\ (forall x, In x KS_qvuDV2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 2
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_322 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuDV1z := BndP_Na_121.LibSegNa_qvuDV1z.
Definition KS_qvuDV1z : list nat := Eval vm_compute in (BG.kept_list 80 PqvuDV1z.regs0 PqvuDV1z.regs_out0).
Lemma KS_qvuDV1z_ok : BG.kept_ok 80 PqvuDV1z.regs0 PqvuDV1z.regs_out0 KS_qvuDV1z = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_323 ())). Qed.
Lemma qvuDV1z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 20) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 8) / 8) + 2147450880) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u64_at RSEGS M ((V 37%nat) - 8) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1514 M) (st fx' R' 0xb15a8 M')
        /\ (forall x, In x KS_qvuDV1z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_324 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuDV1n := BndP_Na_121.LibSegNa_qvuDV1n.
Definition KS_qvuDV1n : list nat := Eval vm_compute in (BG.kept_list 80 PqvuDV1n.regs0 PqvuDV1n.regs_out0).
Lemma KS_qvuDV1n_ok : BG.kept_ok 80 PqvuDV1n.regs0 PqvuDV1n.regs_out0 KS_qvuDV1n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_325 ())). Qed.
Lemma qvuDV1n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 20) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 8) / 8) + 2147450880) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u64_at RSEGS M ((V 37%nat) - 8) (V 43%nat) ->
  1 <= (V 43%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1514 M) (st fx' R' 0xf4640 M')
        /\ (forall x, In x KS_qvuDV1n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726440
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 44
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_326 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuDKz := BndP_Na_121.LibSegNa_qvuDKz.
Definition KS_qvuDKz : list nat := Eval vm_compute in (BG.kept_list 80 PqvuDKz.regs0 PqvuDKz.regs_out0).
Lemma KS_qvuDKz_ok : BG.kept_ok 80 PqvuDKz.regs0 PqvuDKz.regs_out0 KS_qvuDKz = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_327 ())). Qed.
Lemma qvuDKz_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 8) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> L5.u64_at RSEGS M ((V 37%nat) - 8) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1514 M) (st fx' R' 0xb1600 M')
        /\ (forall x, In x KS_qvuDKz -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_328 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuDKn := BndP_Na_121.LibSegNa_qvuDKn.
Definition KS_qvuDKn : list nat := Eval vm_compute in (BG.kept_list 80 PqvuDKn.regs0 PqvuDKn.regs_out0).
Lemma KS_qvuDKn_ok : BG.kept_ok 80 PqvuDKn.regs0 PqvuDKn.regs_out0 KS_qvuDKn = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_329 ())). Qed.
Lemma qvuDKn_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 8) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> L5.u64_at RSEGS M ((V 37%nat) - 8) (V 43%nat) -> 1 <= (V 43%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1514 M) (st fx' R' 0xf4640 M')
        /\ (forall x, In x KS_qvuDKn -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726528
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 44
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_330 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuC := BndP_Na_120.LibSegNa_qvuC.
Definition KS_qvuC : list nat := Eval vm_compute in (BG.kept_list 80 PqvuC.regs0 PqvuC.regs_out0).
Lemma KS_qvuC_ok : BG.kept_ok 80 PqvuC.regs0 PqvuC.regs_out0 KS_qvuC = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_331 ())). Qed.
Lemma qvuC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1894 M) (st fx' R' 0xf4640 M')
        /\ (forall x, In x KS_qvuC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727200
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 58).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P3 ()) [] (Mh_0230_blobs1.kr_b_332 ())). Qed.
(* [comment removed for export] *)

End PQAAU6P3.

End PnAAdU64P3.
Module PnAAdU64P4.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdU64P4 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIVSSC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P47alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSS<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSS3NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSS3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4=KS_qvuIVSS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIVSLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVSL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4=KS_qvuIVSL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIVLSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4=KS_qvuIVLS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIVLLC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIVLL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4=KS_qvuIVLL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIKSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4=KS_qvuIKSS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIKSLC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKSL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4=KS_qvuIKSL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIKLSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4=KS_qvuIKLS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4:KS_qvuIKLLC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P48PqvuIKLL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P48PQAAU6P4=KS_qvuIKLL_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAAU6P4.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_333 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_334 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_335 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_336 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_337 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_338 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_339 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_340 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_341 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_342 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_343 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_344 ())). Qed.
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
Module PqvuIVSS := BndP_Na_121.LibSegNa_qvuIVSS.
Definition KS_qvuIVSS : list nat := Eval vm_compute in (BG.kept_list 80 PqvuIVSS.regs0 PqvuIVSS.regs_out0).
Lemma KS_qvuIVSS_ok : BG.kept_ok 80 PqvuIVSS.regs0 PqvuIVSS.regs_out0 KS_qvuIVSS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_345 ())). Qed.
Lemma qvuIVSS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) -> 0 <= (V 44%nat) <= 44 -> Z.testbit (V 44%nat) 0 = false ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 44 -> Z.testbit (V 40%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb15a8 M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvuIVSS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726896
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + ((V 44%nat) / 2)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + ((V 40%nat) / 2)) + 25)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 40%nat) / 2)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_346 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuIVSL := BndP_Na_121.LibSegNa_qvuIVSL.
Definition KS_qvuIVSL : list nat := Eval vm_compute in (BG.kept_list 80 PqvuIVSL.regs0 PqvuIVSL.regs_out0).
Lemma KS_qvuIVSL_ok : BG.kept_ok 80 PqvuIVSL.regs0 PqvuIVSL.regs_out0 KS_qvuIVSL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_347 ())). Qed.
Lemma qvuIVSL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) ->
  0 <= (V 44%nat) <= 44 -> Z.testbit (V 44%nat) 0 = false -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 ->
  Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) -> 0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) ->
  4096 <= (V 42%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb15a8 M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvuIVSL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726896
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + ((V 44%nat) / 2)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 41%nat) + (V 42%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 41%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_348 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuIVLS := BndP_Na_121.LibSegNa_qvuIVLS.
Definition KS_qvuIVLS : list nat := Eval vm_compute in (BG.kept_list 80 PqvuIVLS.regs0 PqvuIVLS.regs_out0).
Lemma KS_qvuIVLS_ok : BG.kept_ok 80 PqvuIVLS.regs0 PqvuIVLS.regs_out0 KS_qvuIVLS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_349 ())). Qed.
Lemma qvuIVLS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 64) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 56) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) ->
  0 <= (V 44%nat) <= 255 -> Z.testbit (V 44%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 56) (V 45%nat) -> 0 <= (V 45%nat) <= 2147483648 ->
  L5.u64_at RSEGS M ((V 36%nat) + 64) (V 46%nat) -> 4096 <= (V 46%nat) <= 140737488355328 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 44 ->
  Z.testbit (V 40%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb15a8 M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvuIVLS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726896
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 45%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + ((V 40%nat) / 2)) + 25)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 40%nat) / 2)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_350 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuIVLL := BndP_Na_121.LibSegNa_qvuIVLL.
Definition KS_qvuIVLL : list nat := Eval vm_compute in (BG.kept_list 80 PqvuIVLL.regs0 PqvuIVLL.regs_out0).
Lemma KS_qvuIVLL_ok : BG.kept_ok 80 PqvuIVLL.regs0 PqvuIVLL.regs_out0 KS_qvuIVLL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_351 ())). Qed.
Lemma qvuIVLL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 48) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 64) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 56) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) -> 0 <= (V 44%nat) <= 255 -> Z.testbit (V 44%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 36%nat) + 56) (V 45%nat) -> 0 <= (V 45%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 64) (V 46%nat) -> 4096 <= (V 46%nat) <= 140737488355328 ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) ->
  0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) -> 4096 <= (V 42%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb15a8 M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvuIVLL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726896
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 45%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 41%nat) + (V 42%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 41%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_352 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuIKSS := BndP_Na_121.LibSegNa_qvuIKSS.
Definition KS_qvuIKSS : list nat := Eval vm_compute in (BG.kept_list 80 PqvuIKSS.regs0 PqvuIKSS.regs_out0).
Lemma KS_qvuIKSS_ok : BG.kept_ok 80 PqvuIKSS.regs0 PqvuIKSS.regs_out0 KS_qvuIKSS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_353 ())). Qed.
Lemma qvuIKSS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) -> 0 <= (V 44%nat) <= 44 -> Z.testbit (V 44%nat) 0 = false ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 44 -> Z.testbit (V 40%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1600 M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvuIKSS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727188
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + ((V 44%nat) / 2)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + ((V 40%nat) / 2)) + 25)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 40%nat) / 2)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_354 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuIKSL := BndP_Na_121.LibSegNa_qvuIKSL.
Definition KS_qvuIKSL : list nat := Eval vm_compute in (BG.kept_list 80 PqvuIKSL.regs0 PqvuIKSL.regs_out0).
Lemma KS_qvuIKSL_ok : BG.kept_ok 80 PqvuIKSL.regs0 PqvuIKSL.regs_out0 KS_qvuIKSL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_355 ())). Qed.
Lemma qvuIKSL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) ->
  0 <= (V 44%nat) <= 44 -> Z.testbit (V 44%nat) 0 = false -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 ->
  Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) -> 0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) ->
  4096 <= (V 42%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1600 M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvuIKSL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727188
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + ((V 44%nat) / 2)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 41%nat) + (V 42%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_356 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuIKLS := BndP_Na_121.LibSegNa_qvuIKLS.
Definition KS_qvuIKLS : list nat := Eval vm_compute in (BG.kept_list 80 PqvuIKLS.regs0 PqvuIKLS.regs_out0).
Lemma KS_qvuIKLS_ok : BG.kept_ok 80 PqvuIKLS.regs0 PqvuIKLS.regs_out0 KS_qvuIKLS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_357 ())). Qed.
Lemma qvuIKLS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 64) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 56) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) ->
  0 <= (V 44%nat) <= 255 -> Z.testbit (V 44%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 56) (V 45%nat) -> 0 <= (V 45%nat) <= 2147483648 ->
  L5.u64_at RSEGS M ((V 36%nat) + 64) (V 46%nat) -> 4096 <= (V 46%nat) <= 140737488355328 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 44 ->
  Z.testbit (V 40%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1600 M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvuIKLS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727188
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 45%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + ((V 40%nat) / 2)) + 25)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 40%nat) / 2)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_358 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuIKLL := BndP_Na_121.LibSegNa_qvuIKLL.
Definition KS_qvuIKLL : list nat := Eval vm_compute in (BG.kept_list 80 PqvuIKLL.regs0 PqvuIKLL.regs_out0).
Lemma KS_qvuIKLL_ok : BG.kept_ok 80 PqvuIKLL.regs0 PqvuIKLL.regs_out0 KS_qvuIKLL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_359 ())). Qed.
Lemma qvuIKLL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 48) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 64) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 56) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 44%nat) -> 0 <= (V 44%nat) <= 255 -> Z.testbit (V 44%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 36%nat) + 56) (V 45%nat) -> 0 <= (V 45%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 64) (V 46%nat) -> 4096 <= (V 46%nat) <= 140737488355328 ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) ->
  0 <= (V 41%nat) <= 2147483648 -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) -> 4096 <= (V 42%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1600 M) (st fx' R' 0xb95f0 M')
        /\ (forall x, In x KS_qvuIKLL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727188
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 45%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 41%nat) + (V 42%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P4 ()) [] (Mh_0230_blobs1.kr_b_360 ())). Qed.
(* [comment removed for export] *)

End PQAAU6P4.

End PnAAdU64P4.
Module PnAAdU64P5.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdU64P5 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5;KS_qvuAk2e0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P57alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5>u32_of_KWord4aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e03NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5>KS_qvuAk2e0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e06cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5;KS_qvuAk2e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5>KS_qvuAk2e1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk2e16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk1e15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk1e19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5;KS_qvuAk1e1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk1e1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk1e13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk1e12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk1e13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk1e13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P59PqvuAk1e13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5>KS_qvuAk1e1_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAAU6P5.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_361 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_362 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_363 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_364 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_365 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_366 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_367 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_368 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_369 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_370 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_371 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_372 ())). Qed.
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
Module PqvuAk2e0 := BndP_Na_120.LibSegNa_qvuAk2e0.
Definition KS_qvuAk2e0 : list nat := Eval vm_compute in (BG.kept_list 80 PqvuAk2e0.regs0 PqvuAk2e0.regs_out0).
Lemma KS_qvuAk2e0_ok : BG.kept_ok 80 PqvuAk2e0.regs0 PqvuAk2e0.regs_out0 KS_qvuAk2e0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_373 ())). Qed.
Lemma qvuAk2e0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 20) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 2 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 ->
  L5.writable RSEGS M ((V 37%nat) - 16) 4 -> (((V 37%nat) - 24) + 24 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 37%nat) - 24)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 16) <= bv_unsigned a < ((V 37%nat) - 16) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 16) <= i < ((V 37%nat) - 16) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb18a0 M) (st fx' R' 0xb1918 M')
        /\ (forall x, In x KS_qvuAk2e0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) - 16)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((((V 37%nat) - 16) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 2
        /\ L5.u32_at RSEGS M' ((V 37%nat) - 16) 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_374 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuAk2e1 := BndP_Na_120.LibSegNa_qvuAk2e1.
Definition KS_qvuAk2e1 : list nat := Eval vm_compute in (BG.kept_list 80 PqvuAk2e1.regs0 PqvuAk2e1.regs_out0).
Lemma KS_qvuAk2e1_ok : BG.kept_ok 80 PqvuAk2e1.regs0 PqvuAk2e1.regs_out0 KS_qvuAk2e1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_375 ())). Qed.
Lemma qvuAk2e1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 20) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 8) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 2 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.defined M ((V 37%nat) - 8) 8 -> L5.writable RSEGS M ((V 37%nat) - 16) 4 -> L5.writable RSEGS M ((V 37%nat) - 8) 8 ->
  (((V 37%nat) - 24) + 24 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 37%nat) - 24)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 16) <= bv_unsigned a < ((V 37%nat) - 16) + 4) -> ~ (((V 37%nat) - 8) <= bv_unsigned a < ((V 37%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 16) <= i < ((V 37%nat) - 16) + 4) -> ~ (((V 37%nat) - 8) <= i < ((V 37%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb18a0 M) (st fx' R' 0xb1918 M')
        /\ (forall x, In x KS_qvuAk2e1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) - 16)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((((V 37%nat) - 16) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 2
        /\ L5.u32_at RSEGS M' ((V 37%nat) - 16) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_376 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuAk1e1 := BndP_Na_120.LibSegNa_qvuAk1e1.
Definition KS_qvuAk1e1 : list nat := Eval vm_compute in (BG.kept_list 80 PqvuAk1e1.regs0 PqvuAk1e1.regs_out0).
Lemma KS_qvuAk1e1_ok : BG.kept_ok 80 PqvuAk1e1.regs0 PqvuAk1e1.regs_out0 KS_qvuAk1e1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_377 ())). Qed.
Lemma qvuAk1e1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) ->
  L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 20) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 8) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) (V 45%nat) ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.defined M ((V 37%nat) - 8) 8 -> 0 <= (V 45%nat) <= 1 -> L5.writable RSEGS M ((V 37%nat) - 8) 8 ->
  (((V 37%nat) - 24) + 24 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 37%nat) - 24)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 8) <= bv_unsigned a < ((V 37%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 8) <= i < ((V 37%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb18a0 M) (st fx' R' 0xb1918 M')
        /\ (forall x, In x KS_qvuAk1e1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) - 16)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((((V 37%nat) - 16) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 2).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P5 ()) [] (Mh_0230_blobs1.kr_b_378 ())). Qed.
(* [comment removed for export] *)

End PQAAU6P5.

End PnAAdU64P5.
Module PnAAdU64P6.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0223.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdU64P6 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P66PqvuD25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P66PqvuD29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68KS_qvuD2C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P67alignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P66PqvuD2<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P66PqvuD23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P66PqvuD22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P66PqvuD23NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P66PqvuD23kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P66PqvuD23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6;KS_qvuD2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdS29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6:KS_qvuKdS2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdL25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68PqvuKdL29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6:KS_qvuKdL2C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAAU6P6.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_379 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_380 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_381 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_382 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_383 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_384 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_385 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_386 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_387 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_388 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_389 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_390 ())). Qed.
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
Module PqvuD2 := BndP_Na_121.LibSegNa_qvuD2.
Definition KS_qvuD2 : list nat := Eval vm_compute in (BG.kept_list 80 PqvuD2.regs0 PqvuD2.regs_out0).
Lemma KS_qvuD2_ok : BG.kept_ok 80 PqvuD2.regs0 PqvuD2.regs_out0 KS_qvuD2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_391 ())). Qed.
Lemma qvuD2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1409024 -> 7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) ->
  L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 16) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 ->
  aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 24) 0 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 16) (V 38%nat) -> 7036928 <= (V 38%nat) <= 140737488355272 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 38%nat) 1380656 -> L5KA.zeros_at M 2147623466 1 ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 60%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1440 M) (st fx' R' 0xc2158 M')
        /\ (forall x, In x KS_qvuD2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726660
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = getr R (reg 24)
        /\ getr R' (reg 12) = getr R (reg 23)
        /\ getr R' (reg 13) = getr R (reg 21)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 794968).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_392 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuKdS2 := BndP_Na_122.LibSegNa_qvuKdS2.
Definition KS_qvuKdS2 : list nat := Eval vm_compute in (BG.kept_list 80 PqvuKdS2.regs0 PqvuKdS2.regs_out0).
Lemma KS_qvuKdS2_ok : BG.kept_ok 80 PqvuKdS2.regs0 PqvuKdS2.regs_out0 KS_qvuKdS2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_393 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma qvuKdS2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 50%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) ->
  L5.img_clear M 65536 1409024 -> 140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 60%nat) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) -> 7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) ->
  L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) ->
  4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 0 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 16) (V 38%nat) ->
  7036928 <= (V 38%nat) <= 140737488355272 -> (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 38%nat) 1380656 ->
  L5KA.zeros_at M 2147623474 1 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) -> 0 <= (V 40%nat) <= 44 -> Z.testbit (V 40%nat) 0 = false ->
  7036928 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M ((V 50%nat) + 32) 16 ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450884) 2 -> ((V 50%nat) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= (V 50%nat)) -> ((V 50%nat) + 64 <= (V 38%nat) \/ (V 38%nat) + 56 <= (V 50%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 12 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) ->
  ((((V 38%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) -> (2147618928 + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= 2147618928) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 32) <= bv_unsigned a < ((V 50%nat) + 32) + 16) -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 4) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 32) <= i < ((V 50%nat) + 32) + 16) -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= i < ((((V 50%nat) / 8) + 2147450880) + 4) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1514 M) (st fx' R' 0xc2f38 M')
        /\ (forall x, In x KS_qvuKdS2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727108
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 12) = getr R (reg 21)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 798520
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 40) ((V 40%nat) / 2)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 32) ((V 36%nat) + 25)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 0).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) [] (Mh_0230_blobs1.kr_b_394 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PqvuKdL2 := BndP_Na_122.LibSegNa_qvuKdL2.
Definition KS_qvuKdL2 : list nat := Eval vm_compute in (BG.kept_list 80 PqvuKdL2.regs0 PqvuKdL2.regs_out0).
Lemma KS_qvuKdL2_ok : BG.kept_ok 80 PqvuKdL2.regs0 PqvuKdL2.regs_out0 KS_qvuKdL2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64P6 ()) [] (Mh_0230_blobs1.kr_b_395 ())). Qed.
Lemma qvuKdL2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 80) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 80) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 50%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) ->
  L5.img_clear M 65536 1409024 -> 140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 60%nat) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) -> 7036928 <= (V 36%nat) <= 140737488355232 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 96 <= 2147446784) ->
  L5KA.zeros_at M ((((V 36%nat) + 80) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 36%nat) + 40) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> 4120 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 37%nat) - 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 37%nat) - 24) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 24) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 16) (V 38%nat) -> 7036928 <= (V 38%nat) <= 140737488355272 -> (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 56 <= 2147446784) ->
  L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 38%nat) 1380656 -> L5KA.zeros_at M 2147623474 1 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 40%nat) ->
  0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 41%nat) -> 0 <= (V 41%nat) <= 2147483648 ->
  L5.u64_at RSEGS M ((V 36%nat) + 40) (V 42%nat) -> 4096 <= (V 42%nat) <= 140737488355328 -> 7036928 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M ((V 50%nat) + 32) 16 -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450884) 2 -> ((V 50%nat) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= (V 50%nat)) ->
  ((V 50%nat) + 64 <= (V 38%nat) \/ (V 38%nat) + 56 <= (V 50%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 12 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((((V 38%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) -> (2147618928 + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= 2147618928) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 32) <= bv_unsigned a < ((V 50%nat) + 32) + 16) -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 4) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 32) <= i < ((V 50%nat) + 32) + 16) -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= i < ((((V 50%nat) / 8) + 2147450880) + 4) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1514 M) (st fx' R' 0xc2f38 M')
        /\ (forall x, In x KS_qvuKdL2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727108
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 12) = getr R (reg 21)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 798520
        /\ getr R' (reg 20) = Z_to_bv 64 (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 40) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 32) (V 42%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 0).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) [] (Mh_0230_blobs1.kr_b_396 ())). Qed.
(* [comment removed for export] *)

End PQAAU6P6.

End PnAAdU64P6.
Module PnAAdU64.
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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require L5ADetailHR. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdStrCK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreBR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.L5ADetailHR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAReset1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUarK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PmAUar OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgV8A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnVisA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnOwnerFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObjA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAdStrA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAdStrCA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAdStrCK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAKRunF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKSlotA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKCallA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKStepA3N OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKRegA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnAKFromA3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0275.PnAKEncNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.NemLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSinkA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.PnVisNA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0225.NemFrameA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdU64P1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdU64P2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdU64P3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdU64P4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdU64P5 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0230.PnAAdU64P6 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0016.Na0_code_rb1aac_b1ab0.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAAdU64 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_02136PnVisA4PQVA6ndig_fC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z6ltb_geC69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF3:ndig_f_rngC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z7pow_1_rK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU69ndig_f_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnVisA4PQVA4ndigC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z6leb_gtK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU67ndig_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5w_u64C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF39ndig_f_ltC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_symK46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib7Numbers7BinNums1N01C69OSSVerify5KrLib7Mh_0225:PnAKFromA36PQAKF38ndig_rngC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specC69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_strC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG37bvu_rngC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7enc_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4annAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA4PMEAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8pot_encAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA;epot_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:NemLayoutA8NEADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA2HVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;pot_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3scAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA7pot_aeAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU69pot_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02258NemSinkA5NESKA8sink_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA9ec_stateAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092;PnQStaticsA5PQSTA7err_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7AOFF_KBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7AADDR_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5VIS_HC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib6ZArith4Zdiv:Z_mod_multI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38obj_pf_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU64OWNEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5own13C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU63OCEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7ocell13C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;own13_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU68sp_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU65V2_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8TAG_ESECC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU68ndig_u32C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List6filterC69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_tC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4lv_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5lv_eoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl01C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List:filter_appC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3advC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ndestC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4alvl00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List9incl_applC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5a_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34reglC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5xinvGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU63ESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA6kbsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_oaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7alvl_okC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU64valsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P57alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6set_lvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU69ndest_advC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG34sublC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprK46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA5s_xlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU63FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N6s_advXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5=qvuAk2e0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5=qvuAk2e1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5=qvuAk1e1_concC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU63IXAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU64QENNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU65HSPCfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3LSZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5;KS_qvuAk2e0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5;KS_qvuAk2e1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P58PQAAU6P5;KS_qvuAk1e1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_WAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR35g_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4EVISC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5wappWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P67alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P6:qvuD2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU6:mem_eq_frzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA=v_uint64_specC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU6:w_u64_ndigC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemSpecsA5NECSA8aargs_ofC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ea_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ea_tagC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pre_u64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8step_u64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1:qvuJ1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG38regl_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnAKRegA36PQAKG39regl_presC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU63ADVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02569PnAKRunA36PQAKR38g_pfactsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N7s_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ENC_SLOTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N3Hh3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU62IXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ENC_HC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU67oec_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU68ov_rng56C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P68PQAAU6P68KS_qvuD2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9eargs_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8TAG_NONEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P18KS_qvuJ1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P1:qvuJ2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU67DU_DPHIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P18PQAAU6P18KS_qvuJ2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU64EST0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P39qvuC_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N8pb_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N6pb_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N4s_SMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6s_restC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N5s_setC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_app_asciiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_xcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKCallA3N7PQAKC3N9s_call_sCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA4PB_HC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37KS_qvuCC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multK46Stdlib9micromega=RingMicromega3Op206C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5asciiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKStepA3N7PQAKT3N9s_key_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA7src_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA9ins_argsCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7ins_scCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259PnAdStrCA6PQASCA8src_okCAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU67AFTER_VC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU67AFTER_KC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnAdStrA5PQASA5INS_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8AOFF_KEYC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbc69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU64INS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02759PnAKEncNA7PQAKENA7s_kcallC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P37alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG>u64_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU65COMMAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU65KDESTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3;qvuDKz_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3;qvuDKn_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3;qvuDV2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3<qvuDV1z_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3<qvuDV1n_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P39KS_qvuDKzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P39KS_qvuDKnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P39KS_qvuDV2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3:KS_qvuDV1zC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0230:PnAAdU64P38PQAAU6P3:KS_qvuDV1nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA8lv_shapeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5a_kbgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N8lv_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N:lv_last_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU66KEYLITC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU66PATH_DC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA7lv_rootC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5aeownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8args_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA5d_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8dphi_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA7pre_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA7is_esecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA8step_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N6cls_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0225;PnAKSlotA3N7PQAKS3N;evis_of_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA4ndigC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6edepthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02308PnAAdU646PQAAU63RUNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ;qa_v_uint64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02257PnVisNA4PNVA=v_uint64_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6ae_atAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02259NemModelA4NEMA3phiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_02259NemModelA4NEMA4aest00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA3FCMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQAAU6.
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
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) [] (Mh_0230_blobs1.kr_b_397 ())). Qed.
Lemma ndig_lb v k : 0 <= k <= 19 -> 10 ^ k <= v -> k + 1 <= PQVA.ndig v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) [] (Mh_0230_blobs1.kr_b_398 ())). Qed.
Lemma w_u64_ndig v : 0 <= v -> NEM.w_u64 v <= PQVA.ndig v + 2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) [] (Mh_0230_blobs1.kr_b_399 ())). Qed.
Lemma ndig_u32 v : 0 <= v < 2 ^ 32 -> PQVA.ndig v <= 10.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) [] (Mh_0230_blobs1.kr_b_400 ())). Qed.
Lemma hdr_str_ndig v : 0 <= v < 2 ^ 64 -> NEM.hdr_str (PQVA.ndig v) = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) [] (Mh_0230_blobs1.kr_b_401 ())). Qed.

(* [comment removed for export] *)
Lemma aacc_join (Mx : mem) p n m : aacc Mx p n -> aacc Mx (p + n) m -> 0 <= n -> aacc Mx p (n + m).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) [] (Mh_0230_blobs1.kr_b_402 ())). Qed.
Lemma aacc_sub (Mx : mem) a0 n0 a1 n1 : aacc Mx a0 n0 -> a0 <= a1 -> a1 + n1 <= a0 + n0 -> aacc Mx a1 n1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) [] (Mh_0230_blobs1.kr_b_403 ())). Qed.

(* [comment removed for export] *)
Lemma mem_eq_frz (Ma Mb : mem) : (forall a, 0 <= a < 2 ^ 64 -> ~ False -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> Mb = Ma.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) [] (Mh_0230_blobs1.kr_b_404 ())). Qed.

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
Hypothesis FROMK : PQASCA2.fromu_specCA RSEGS AD L ar HI 0xb8fb0.
Hypothesis INSI : PQASCA.ins_specCA RSEGS AD L ar HI 0xb95f0.
Hypothesis VUE : NECSA.v_uint64_spec RSEGS AD AQ AAD AE L ar HI (NESKA.PMEA L).
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
Local Notation ND := (PQVA.ndig bv).
(* [comment removed for export] *)
Local Notation DU := (PQVA.ndig bv + 2).
Local Notation DPHI := (if tg =? NEM.TAG_ESEC then 15 else PQVA.ndig bv + 2).
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
Hypothesis Htg : tg = NEM.TAG_NONE \/ (tg = NEM.TAG_ESEC /\ bv < 2 ^ 32).
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
       /\ NEMA.edepth st' = NEMA.edepth ST0 /\ (b' = bf \/ tg = NEM.TAG_ESEC)) ->
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
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_405 ())). Qed.
Local Notation "'SX' f" := (f L ar C IL HI LY HIok ICok ILY K R M model LBX FF LK Aw cr sp r oa ov osk oec sa ESO QE HH QENN AM K0 ENT FRM FRS AO O8 AOV APT AOSK AOEC AA OACC AOK VIS BASE) (at level 10, f at level 9, only parsing).

(* [comment removed for export] *)
Lemma pot_split x kb1 e1 k1 : NEMA.pot_aeA L ar (NEMA.AEST x kb1 e1 k1) = PM.credit_add (PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) x)) (EPOT e1 k1).
Proof using L ar.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_406 ())). Qed.
Lemma CR : PMSP.credit_le (PM.credit_add (PMSPA.scA L (PQMA.pot_adaptor (PMSPA.HV L ar) sa)) QE) cr.
Proof using CRF.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_407 ())). Qed.
Lemma xinv0 : PQAKENA.xinvG L ar oa ov osk oec cat M (PQMA.a_kb sa) kbb en k bf ef.
Proof using KC U8 ENA SKA ECS ERR.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_408 ())). Qed.

Lemma sp_facts : 140735332487264 + 16 <= V2 /\ V2 + cls <= 140737488355328 /\ (V2 + cls) mod 16 = 0 /\ 0 <= r < 2 ^ 47 /\ r mod 2 = 0.
Proof using ENT Hcls.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_409 ())). Qed.
Lemma V2_lo : 140735332487328 <= V2.
Proof using ENT Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_410 ())). Qed.
Lemma HSPCf : sp - 2048 <= spc /\ spc mod 16 = 0.
Proof using Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_411 ())). Qed.
Lemma oec_rng : 7036928 <= oec /\ oec + 16 <= 2 ^ 47.
Proof using LY HIok HH AOEC.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_412 ())). Qed.
Lemma oa_lo96 : 7036928 <= oa /\ oa + 96 <= 2 ^ 47.
Proof using LY HIok HH AO.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_413 ())). Qed.
Lemma ov_rng56 : 7036928 <= ov /\ ov + 56 <= ahl_ceil ar /\ ov + 56 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784).
Proof using LY HIok HH AOV.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_414 ())). Qed.
Lemma tg_rng : 0 <= tg < 2 ^ 64.
Proof using Htg.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_415 ())). Qed.
Lemma GOWNE : forall Ma Mb, OWN Ma -> (forall a, OC a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> OWN Mb.
Proof using ENT Hcls V32.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_416 ())). Qed.

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
  /\ (bf = true -> b1 = true) /\ (ef = true -> e1 = true) /\ (b1 = bf \/ tg = NEM.TAG_ESEC).
Lemma EST0 : EST en k bf ef.
Proof using Hbv.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_417 ())). Qed.
Lemma DU_DPHI : DU <= DPHI /\ ND + 1 <= DPHI /\ ND + 2 <= DU.
Proof using Hbv Htg.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_418 ())). Qed.
(* [comment removed for export] *)
Lemma ndest_adv lv0 c : NEMA.ndest (lv0 ++ [PQAKS3N.adv c]) = NEMA.ndest (lv0 ++ [c]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_419 ())). Qed.

(* [comment removed for export] *)
Lemma FIN M5 model5 LK5 Aw5 st5 cr5 kbb5 en5 k5 (b5 e5 : bool) (fx5 : FPState) R5 :
  AMF M5 model5 LK5 Aw5 st5 (NECS.eown en5 k5) (EPOT en5 k5) cr5 -> REGSA R5 -> xinv M5 (PQMA.a_kb st5) kbb5 en5 k5 b5 e5 -> EST en5 k5 b5 e5 ->
  PQMA.nlv st5 = PQMA.nlv sa -> PQMA.kbsize st5 <= PQMA.kbsize sa + DU -> PQMA.kbsize st5 + NESK.sk_z k5 <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st5) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb1918 M5 model5) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_420 ())). Qed.


(* [comment removed for export] *)
Lemma ADV M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 en1 k1 (b1 e1 : bool) (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 (NECS.eown en1 k1) (EPOT en1 k1) cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en1 k1 b1 e1 -> EST en1 k1 b1 e1 ->
  PQMA.a_lv st1 = lv0 ++ [c] ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 <= PQMA.kbsize sa + DU -> PQMA.kbsize st1 + NESK.sk_z k1 <= PQMA.kbsize sa + NESK.sk_z k + DPHI ->
  NEMA.ndest (PQMA.a_lv st1) = NEMA.ndest (PQMA.a_lv sa) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb18a0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_421 ())). Qed.


(* [comment removed for export] *)
Ltac of LM ELV :=
  destruct ((SF PQAKS3N.s_oa) _ _ _ _ _ _ _ _ LM) as ((OA1 & OA2 & OA3 & OA4 & OA5) & OAZ & O16 & (OV1 & OV2 & OV3 & OV4 & OVZ & OVW) & IMG & VTZ & (OAF & OVF & OASF & OVSF) & (OAV & OAW));
  destruct ((SF PQAKS3N.s_lv) _ _ _ _ _ _ _ _ _ _ LM ELV) as (E80 & (E1 & E2 & E8 & E4 & E5) & (Z24 & Z20 & Z16 & Z8) & (CT & CK & CEO) & (CD & CW & CVIS) & (EO1 & EF1 & EV1) & ((CTR & CKR & CER & CKE) & CT1) & INL & EHI).

(* [comment removed for export] *)
Lemma PATH_D M1 model1 LK1 Aw1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> PQMA.a_lv sa = lv0 ++ [c] -> PQMA.lv_t c = 0 -> PQMA.lv_eo c = 1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1440 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_422 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AFTER_V M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1770 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_423 ())). Qed.
(* [comment removed for export] *)
Lemma AFTER_K M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48) -> PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 + 1 <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1894 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_424 ())). Qed.


(* [comment removed for export] *)
Lemma div2_2 n : (2 * n) / 2 = n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_425 ())). Qed.
(* [comment removed for export] *)
Lemma INS_CALL (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 (ra v11 v12 v13 v14 : Z) :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGSA R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = false -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  ra = (if arm then 0xb1770 else 0xb1894) ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 v11 -> getr R1 (reg 12) = Z_to_bv 64 v12 ->
  getr R1 (reg 13) = Z_to_bv 64 v13 -> getr R1 (reg 14) = Z_to_bv 64 v14 ->
  v11 = PM.vs_data (oa + 48) (PQMA.a_kb st1) + PM.vs_size (PQMA.a_kb st1) -> v12 = PM.vs_data (oa + 24) (PQMA.a_key st1) ->
  v13 = v12 + v14 -> v14 = PM.vs_size (PQMA.a_key st1) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + v14 + (if arm then 0 else 1) <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb95f0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_426 ())). Qed.

Lemma INS2 (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = true -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + PM.vs_size (PQMA.a_key st1) + (if arm then 0 else 1) <= PQMA.kbsize sa + DU ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if arm then 0xb15a8 else 0xb1600) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_427 ())). Qed.

(* [comment removed for export] *)
Lemma KDEST M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.lv_t c = 0 -> PQMA.lv_eo c = 0 ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 = PQMA.kbsize sa -> PM.vs_size (PQMA.a_key st1) <= ND ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1514 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_428 ())). Qed.

(* [comment removed for export] *)
Lemma COMMA (arm : bool) M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs -> (arm = true -> getr R1 (reg 21) = Z_to_bv 64 (oa + 48)) ->
  getr R1 (reg 1) = Z_to_bv 64 (if arm then 0xb15a8 else 0xb1600) -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 44 ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> PQMA.nlv st1 = PQMA.nlv sa ->
  PQMA.kbsize st1 + 1 + PM.vs_size (PQMA.a_key st1) + (if arm then 0 else 1) <= PQMA.kbsize sa + DU -> 0 <= PM.vs_size (PQMA.a_key st1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xf4640 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_429 ())). Qed.

(* [comment removed for export] *)
Lemma DISP2 M1 model1 LK1 Aw1 st1 cr1 lv0 c kbb1 kcs (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 st1 ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb st1) kbb1 en k bf ef ->
  kcontent M1 (oa + PQMA.AOFF_KEY) (PQMA.a_key st1) kcs -> NEM.ascii kcs ->
  PQMA.a_lv st1 = lv0 ++ [c] -> PQMA.a_lv st1 = PQMA.a_lv sa -> (PQMA.lv_eo c = 0 \/ PQMA.lv_t c = 1) ->
  PQMA.nlv st1 = PQMA.nlv sa -> PQMA.kbsize st1 = PQMA.kbsize sa -> 0 <= PM.vs_size (PQMA.a_key st1) <= ND ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1514 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_430 ())). Qed.

(* [comment removed for export] *)
Lemma KEYLIT M1 model1 LK1 Aw1 cr1 lv0 c kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> PQMA.a_lv sa = lv0 ++ [c] -> (PQMA.lv_eo c = 0 \/ PQMA.lv_t c = 1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1440 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_431 ())). Qed.

(* [comment removed for export] *)
Lemma DISP1 M1 model1 LK1 Aw1 cr1 kbb1 (fx1 : FPState) R1 :
  AMF M1 model1 LK1 Aw1 sa ESO QE cr1 -> REGS R1 -> xinv M1 (PQMA.a_kb sa) kbb1 en k bf ef -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb1440 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_432 ())). Qed.

(* [comment removed for export] *)
Lemma SETUP Mx modelx LKx Awx (fx2 : FPState) R2 :
  AMF Mx modelx LKx Awx sa ESO QE cr -> xinv Mx (PQMA.a_kb sa) kbb en k bf ef ->
  getr R2 (reg 2) = Z_to_bv 64 spc -> getr R2 (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R2 (reg 8) = Z_to_bv 64 sp ->
  getr R2 (reg 9) = Z_to_bv 64 spc -> getr R2 (reg 10) = Z_to_bv 64 F -> getr R2 (reg 20) = Z_to_bv 64 oa -> getr R2 (reg 23) = Z_to_bv 64 tg -> getr R2 (reg 24) = Z_to_bv 64 bv ->
  getr R2 (reg 26) = Z_to_bv 64 2147450880 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0xb13a0 Mx modelx) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Run"; "Frame"] (Mh_0230_blobs1.kr_b_433 ())). Qed.

End Frame.

(* [comment removed for export] *)
Ltac enter_tac Aconc fxv MVv HRgp HRtp :=
  pose proof (LF2CBN( Aconc fxv R MVv (fun j : nat => match j with 2%nat => V2 | _ => 0 end) )) as P;
  L5SAR.feed P ltac:(fd);
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T20 & T21 & T23 & T24 & T26 & CEC & C27 & C26 & C25 & C24 & C23 & C22 & C21 & C20 & C19 & C18 & C9 & C8 & C1 & C0);
  apply ((SX PQAKS3N.s_enterX) spc (V2 - 136) sp OC OWN 0 fxv fx1 R1 0xb12d0 725840 M1v CR);
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

Lemma RUN (fx : FPState) : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb1320 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0230 ()) ["WithHeap"; "Run"] (Mh_0230_blobs1.kr_b_434 ())). Qed.

End Run.

(* [comment removed for export] *)
Theorem uint64_ok : PNVA.v_uint64_spec RSEGS AD AQ AAD AE L ar HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAAdU64 ()) ["WithHeap"] (Mh_0230_blobs1.kr_b_435 ())). Qed.

End WithHeap.
End PQAAU6.


End PnAAdU64.
