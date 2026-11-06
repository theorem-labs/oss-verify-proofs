(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Mh_0197_blobs1.
(* [comment removed for export] *)
Set Warnings "-require-in-module".
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0197 () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00I46Stdlib9micromega7EnvRing5PExpr00C47Corelib5Lists7ListDef3seqI47Corelib4Init9Datatypes4list00C47Corelib4Init5Peano2ltK59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega6VarMap1t01C46Stdlib9micromega:ZMicromega=Zeval_formulaC46Stdlib9micromega5Tauto4rtypC56Stdlib6ZArith6BinInt1Z3powK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I46Stdlib9micromega6VarMap1t00K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init5Logic2eq00C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z9ltb_spec0K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natK47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_1<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC47Corelib5Lists7ListDef3mapK69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega6VarMap4findC56Stdlib6ZArith6BinInt1Z6of_natK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto7eval_bfK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses5mkrelC49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_13PSSC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_19regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_19regs_out1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_19regs_out2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_16cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums8positive00I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I46Stdlib9micromega5Tauto4kind00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I46Stdlib9micromega:ZMicromega;ZArithProof00K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_15regs0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP<KS_tsA32_1_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP<KS_tsA32_1_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP<KS_tsA32_1_2C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_13F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP?KS_tsA32_1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_16cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_13ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP?KS_tsA32_1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_16cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_13ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP?KS_tsA32_1_2_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0>C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z:mul_div_leC69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_1<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9lxor_byteC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP@defined_of_KUnkaC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_19regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_19regs_out1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_19regs_out2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_16cells0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5aluop06c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=KS_tsSub1_1_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=KS_tsSub1_1_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=KS_tsSub1_1_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_13F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP@KS_tsSub1_1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_16cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_13ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP@KS_tsSub1_1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_16cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_13ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP@KS_tsSub1_1_2_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z4landC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul1<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP=word_of_zpolyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP9land_byteC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul19regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul19regs_out1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul19regs_out2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul16cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K47Corelib4Init9Datatypes4bool02c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsMul1_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsMul1_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsMul1_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul13F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP>KS_tsMul1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul16cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul13ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP>KS_tsMul1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul16cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul13ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP>KS_tsMul1_2_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init5Logic3iffI46Stdlib9micromega=RingMicromega5Psatz00C56Stdlib5Arith8PeanoNat3Nat3eqbI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK69OSSVerify5KrLib7Mh_00846L5Defs2L56bstore01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00846L5Defs2L56bigobj01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55bo_fbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56bo_lenC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC69OSSVerify5KrLib7Mh_00846L5Defs2L56big_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55bo_stC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR4m9_AC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses:impl_morphc69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR5m9_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR5m9_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS4wlenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS7binl_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;tsMul0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS3wfbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR7ret_mulC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;tsMul1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR7mul9_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR4m9_cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR4m9_BC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z7sub_0_rC56Stdlib6ZArith6BinInt1Z8eqb_specC46Stdlib4Bool4Bool<andb_false_rc69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR7wlen_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C69OSSVerify5KrLib7Mh_00846L5Defs2L5:hull_apartC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS9ARITH_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS5NANOSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP9KS_tsMul0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K2CSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS4MULUC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00846L5Defs2L56bigobj00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00846L5Defs2L56bstore00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS=mulu_run_stmtC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;tsAdd0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR7ret_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_lc69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR:land253_idC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;tsAdd1_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8add_commC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsAdd0_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsAdd0_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsAdd1_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsAdd1_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS6ADDU64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsAdd1_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS>add64_run_stmtC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0@C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0?C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0=C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorc69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP9land_byteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP9land_le_lC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8lor_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lxor_0_lc69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP@defined_of_KUnkaC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa9regs_out1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa6cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop08K4ELinuxProcessSemantics5Riscv5Instr5mulop06K4ELinuxProcessSemantics5Riscv5Instr5aluop09c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP<KS_tsDivBa_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP<KS_tsDivBa_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP?KS_tsDivBa_0_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP?KS_tsDivBa_1_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP@defined_of_KUnkaC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b9regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b9regs_out1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b9regs_out2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b6cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop04c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsW6b_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsW6b_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsW6b_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=KS_tsW6b_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=KS_tsW6b_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=KS_tsW6b_2_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP=word_of_zpolyC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP@defined_of_KUnkaC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a9regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a9regs_out1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a9regs_out2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_tw6a_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_tw6a_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_tw6a_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP<KS_tw6a_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP<KS_tw6a_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP<KS_tw6a_2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b9regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b9regs_out1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b9regs_out2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_tw6b_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_tw6b_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_tw6b_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP<KS_tw6b_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP<KS_tw6b_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP<KS_tw6b_2_okC1?~~~~~~~~~~~~~~~".
Module PnTsFn12P.
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsFn12P () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z;lxor_nonnegK46Stdlib9micromega5Tauto8GFormula09C56Stdlib6ZArith6BinInt1Z9log2_lxorC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP<KS_tsA32_0_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_09regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP<KS_tsA32_0_1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=word_of_zpolyC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InK59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_03ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_03ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP?KS_tsA32_0_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop01I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP?KS_tsA32_0_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP<KS_tsA32_1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP<KS_tsA32_1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsA32_19regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP<KS_tsA32_1_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2a9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP;KS_tsA32_2aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2a<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2a3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP>KS_tsA32_2a_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2a6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2b9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=KS_tsA32_2b_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2b9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=KS_tsA32_2b_1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2b<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2b3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2b3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2b6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsA32_2b3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP@KS_tsA32_2b_0_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP@KS_tsA32_2b_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP;KS_tsSub1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_0<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0>C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z:mul_div_leK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9lxor_byteC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP@defined_of_KUnkaC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_06cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP>KS_tsSub1_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop06c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=KS_tsSub1_1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=KS_tsSub1_1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9PtsSub1_19regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=KS_tsSub1_1_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsSub2a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsSub2a9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:KS_tsSub2aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsSub2a<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsSub2a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsSub2a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsSub2a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsSub2a6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsSub2a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8PtsSub2a3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP=KS_tsSub2a_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP<KS_tsSub2b_0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_06cells0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP?KS_tsSub2b_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP>KS_tsSub2b_1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP>KS_tsSub2b_1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_13ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_13ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP:PtsSub2b_13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGPAKS_tsSub2b_1_0_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGPAKS_tsSub2b_1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP6PtsRzA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP6PtsRzA9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP8KS_tsRzAC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP6PtsRzA<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP6PtsRzA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP6PtsRzA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP6PtsRzA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP6PtsRzA6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP6PtsRzA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP6PtsRzA3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP;KS_tsRzA_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9KS_tsRzB0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB06cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP<KS_tsRzB0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP9KS_tsRzB2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP7PtsRzB23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsFn12P6PQTSGP<KS_tsRzB2_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQTSGP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_001 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_002 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_003 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_004 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_005 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_006 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_007 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_008 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_009 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_010 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_011 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_012 ())). Qed.
(* [comment removed for export] *)
Lemma lxor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_013 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lxor _ _ < 256 => apply lxor_byte; byte_go
  | |- 0 <= ?x mod 18446744073709551616 < 256 => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia); byte_go
  | |- 0 <= ?x mod 2 ^ 64 < 256 => rewrite (Z.mod_small x (2 ^ 64)) by (zfacts; lia); byte_go
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
Module PtsA32_0 := BndP_Ns_077.LibSegNs_tsA32_0.
Definition KS_tsA32_0_0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsA32_0.regs0 PtsA32_0.regs_out0).
Lemma KS_tsA32_0_0_ok : BG.kept_ok 64 PtsA32_0.regs0 PtsA32_0.regs_out0 KS_tsA32_0_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_014 ())). Qed.
Definition KS_tsA32_0_1 : list nat := Eval vm_compute in (BG.kept_list 64 PtsA32_0.regs0 PtsA32_0.regs_out1).
Lemma KS_tsA32_0_1_ok : BG.kept_ok 64 PtsA32_0.regs0 PtsA32_0.regs_out1 KS_tsA32_0_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_015 ())). Qed.
Lemma tsA32_0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) ->
  140735332483296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.img_clear M 65536 814272 ->
  140735332483296 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 224) + 224 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 224)) -> L5.u8_at RSEGS M (V 34%nat) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 34%nat) + 16) 0 -> L5.u64_at RSEGS M ((V 34%nat) + 24) 0 -> L5.writable RSEGS M (V 34%nat) 32 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46f7c M) (st fx' R' 0x470bc M')
        /\ (forall x, In x KS_tsA32_0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ bv_unsigned (getr R' (reg 15)) = (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)
        /\ 1 <= (((((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 290736
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u8_at RSEGS M' (V 34%nat) 0)
      \/ (msteps RSEGS (st fx R 0x46f7c M) (st fx' R' 0x470bc M')
        /\ (forall x, In x KS_tsA32_0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 8)
        /\ bv_unsigned (getr R' (reg 15)) = (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)
        /\ L5.u8_at RSEGS M' (V 34%nat) 0
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 0
        /\ (((((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 290736
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_016 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsA32_1 := BndP_Ns_077.LibSegNs_tsA32_1.
Definition KS_tsA32_1_0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsA32_1.regs0 PtsA32_1.regs_out0).
Lemma KS_tsA32_1_0_ok : BG.kept_ok 64 PtsA32_1.regs0 PtsA32_1.regs_out0 KS_tsA32_1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_017 ())). Qed.
Definition KS_tsA32_1_1 : list nat := Eval vm_compute in (BG.kept_list 64 PtsA32_1.regs0 PtsA32_1.regs_out1).
Lemma KS_tsA32_1_1_ok : BG.kept_ok 64 PtsA32_1.regs0 PtsA32_1.regs_out1 KS_tsA32_1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_018 ())). Qed.
Definition KS_tsA32_1_2 : list nat := Eval vm_compute in (BG.kept_list 64 PtsA32_1.regs0 PtsA32_1.regs_out2).
Lemma KS_tsA32_1_2_ok : BG.kept_ok 64 PtsA32_1.regs0 PtsA32_1.regs_out2 KS_tsA32_1_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_019 ())). Qed.
Lemma tsA32_1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) ->
  140735332483296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.img_clear M 65536 814272 ->
  140735332483296 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 224) + 224 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 224)) -> L5.u8_at RSEGS M (V 34%nat) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) 0 -> L5.writable RSEGS M (V 34%nat) 32 ->
  1 <= (V 36%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46f7c M) (st fx' R' 0x470bc M')
        /\ (forall x, In x KS_tsA32_1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 24)
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 1
        /\ 1 <= (((if (((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 290736
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u8_at RSEGS M' (V 34%nat) 0)
      \/ (msteps RSEGS (st fx R 0x46f7c M) (st fx' R' 0x470bc M')
        /\ (forall x, In x KS_tsA32_1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ bv_unsigned (getr R' (reg 15)) = (((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)
        /\ 1 <= (((((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 1
        /\ (((if (((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 290736
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u8_at RSEGS M' (V 34%nat) 0)
      \/ (msteps RSEGS (st fx R 0x46f7c M) (st fx' R' 0x470bc M')
        /\ (forall x, In x KS_tsA32_1_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 8)
        /\ bv_unsigned (getr R' (reg 15)) = (((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (V 34%nat) 0
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 0
        /\ (((((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ (((if (((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 290736
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat))).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0197 ()) [] (Mh_0197_blobs1.kr_b_020 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsA32_2a := BndP_Ns_077.LibSegNs_tsA32_2a.
Definition KS_tsA32_2a : list nat := Eval vm_compute in (BG.kept_list 64 PtsA32_2a.regs0 PtsA32_2a.regs_out0).
Lemma KS_tsA32_2a_ok : BG.kept_ok 64 PtsA32_2a.regs0 PtsA32_2a.regs_out0 KS_tsA32_2a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_021 ())). Qed.
Lemma tsA32_2a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) ->
  140735332483168 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> L5.img_clear M 65536 814272 ->
  140735332483168 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 96)) -> L5.u8_at RSEGS M (V 34%nat) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 2 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) -> L5.writable RSEGS M (V 34%nat) 32 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46f7c M) (st fx' R' 0x4343c M')
        /\ (forall x, In x KS_tsA32_2a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290736
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_022 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsA32_2b := BndP_Ns_077.LibSegNs_tsA32_2b.
Definition KS_tsA32_2b_0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsA32_2b.regs0 PtsA32_2b.regs_out0).
Lemma KS_tsA32_2b_0_ok : BG.kept_ok 64 PtsA32_2b.regs0 PtsA32_2b.regs_out0 KS_tsA32_2b_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_023 ())). Qed.
Definition KS_tsA32_2b_1 : list nat := Eval vm_compute in (BG.kept_list 64 PtsA32_2b.regs0 PtsA32_2b.regs_out1).
Lemma KS_tsA32_2b_1_ok : BG.kept_ok 64 PtsA32_2b.regs0 PtsA32_2b.regs_out1 KS_tsA32_2b_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_024 ())). Qed.
Lemma tsA32_2b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) ->
  140735332483168 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> L5.img_clear M 65536 814272 ->
  140735332483168 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 96)) -> L5.u8_at RSEGS M (V 34%nat) 1 ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 3 -> L5.u64_at RSEGS M ((V 34%nat) + 16) 8 -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 41%nat) -> L5.writable RSEGS M (V 34%nat) 32 ->
  4096 <= (V 41%nat) <= 140737487306752 -> aligned (V 41%nat) 16 -> L5.writable RSEGS M (V 41%nat) 64 -> L5.defined M ((V 41%nat) + 24) 40 ->
  L5.u64_at RSEGS M (V 41%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 41%nat) + 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 41%nat) + 16) 0 -> ((V 41%nat) + 64 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 41%nat)) ->
  (((V 2%nat) - 96) + 96 <= (V 41%nat) \/ (V 41%nat) + 64 <= ((V 2%nat) - 96)) -> 1 <= (V 38%nat) <= 4611686018427387904 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 8%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 9%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46fb0 M) (st fx' R' 0x470bc M')
        /\ (forall x, In x KS_tsA32_2b_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 9%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 41%nat) + 8)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 38%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 2
        /\ L5.u64_at RSEGS M' ((V 41%nat) + 8) ((V 38%nat) + 1)
        /\ 1 <= (((if (((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' (V 41%nat) (((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (V 34%nat) 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) 8
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 41%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 8%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 9%nat))
      \/ (msteps RSEGS (st fx R 0x46fb0 M) (st fx' R' 0x470bc M')
        /\ (forall x, In x KS_tsA32_2b_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 9%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 41%nat) + 8)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 2
        /\ (((if (((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' (V 41%nat) (((V 36%nat) + (((4294967296 * (V 35%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (V 34%nat) 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) 8
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 41%nat) + 8) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 41%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 8%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 9%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_025 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsSub1_0 := BndP_Ns_078.LibSegNs_tsSub1_0.
Definition KS_tsSub1_0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsSub1_0.regs0 PtsSub1_0.regs_out0).
Lemma KS_tsSub1_0_ok : BG.kept_ok 64 PtsSub1_0.regs0 PtsSub1_0.regs_out0 KS_tsSub1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_026 ())). Qed.
Lemma tsSub1_0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) ->
  140735332483408 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 336) 336 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 336) 336 -> L5.u8_at RSEGS M ((V 2%nat) - 72) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483408 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 336) + 336 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 336)) -> L5.u8_at RSEGS M (V 34%nat) 2 -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 ->
  L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) 0 -> L5.writable RSEGS M (V 34%nat) 32 -> 1 <= (V 36%nat) <= 18446744073709551615 ->
  140735332483408 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 336) + 336 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 336)) -> L5.u8_at RSEGS M (V 33%nat) 0 ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 42%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 24) 0 -> ((V 33%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 33%nat)) ->
  0 <= (V 42%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 336) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 336) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x43888 M) (st fx' R' 0x43aac M')
        /\ (forall x, In x KS_tsSub1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) 277844
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 276732
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 72) (Z.lxor ((4 * ((V 50%nat) / 4)) mod 2 ^ 64) 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 336) 8
        /\ L5.defined M' ((V 2%nat) - 272) 32
        /\ L5.defined M' ((V 2%nat) - 208) 32
        /\ L5.defined M' ((V 2%nat) - 144) 72
        /\ L5.defined M' ((V 2%nat) - 71) 7
        /\ L5.u8_at RSEGS M' (V 34%nat) 2
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (V 36%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_027 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsSub1_1 := BndP_Ns_078.LibSegNs_tsSub1_1.
Definition KS_tsSub1_1_0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsSub1_1.regs0 PtsSub1_1.regs_out0).
Lemma KS_tsSub1_1_0_ok : BG.kept_ok 64 PtsSub1_1.regs0 PtsSub1_1.regs_out0 KS_tsSub1_1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_028 ())). Qed.
Definition KS_tsSub1_1_1 : list nat := Eval vm_compute in (BG.kept_list 64 PtsSub1_1.regs0 PtsSub1_1.regs_out1).
Lemma KS_tsSub1_1_1_ok : BG.kept_ok 64 PtsSub1_1.regs0 PtsSub1_1.regs_out1 KS_tsSub1_1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_029 ())). Qed.
Definition KS_tsSub1_1_2 : list nat := Eval vm_compute in (BG.kept_list 64 PtsSub1_1.regs0 PtsSub1_1.regs_out2).
Lemma KS_tsSub1_1_2_ok : BG.kept_ok 64 PtsSub1_1.regs0 PtsSub1_1.regs_out2 KS_tsSub1_1_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_030 ())). Qed.
Lemma tsSub1_1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) ->
  140735332483408 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 336) 336 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 336) 336 -> L5.u8_at RSEGS M ((V 2%nat) - 72) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483408 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 336) + 336 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 336)) -> L5.u8_at RSEGS M (V 34%nat) 2 -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 ->
  L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) 0 -> L5.writable RSEGS M (V 34%nat) 32 -> 1 <= (V 36%nat) <= 18446744073709551615 ->
  140735332483408 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 336) + 336 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 336)) -> L5.u8_at RSEGS M (V 33%nat) 0 ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 42%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 24) 0 -> ((V 33%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 33%nat)) ->
  0 <= (V 42%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 336) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 336) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x43888 M) (st fx' R' 0x43aac M')
        /\ (forall x, In x KS_tsSub1_1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 24)
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 1
        /\ 1 <= (((if (((V 36%nat) + (V 42%nat)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (((V 36%nat) + (V 42%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) 277844
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 276732
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 72) (Z.lxor ((4 * ((V 50%nat) / 4)) mod 2 ^ 64) 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 336) 8
        /\ L5.defined M' ((V 2%nat) - 272) 32
        /\ L5.defined M' ((V 2%nat) - 208) 32
        /\ L5.defined M' ((V 2%nat) - 144) 72
        /\ L5.defined M' ((V 2%nat) - 71) 7
        /\ L5.u8_at RSEGS M' (V 34%nat) 2)
      \/ (msteps RSEGS (st fx R 0x43888 M) (st fx' R' 0x43aac M')
        /\ (forall x, In x KS_tsSub1_1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ bv_unsigned (getr R' (reg 15)) = (((V 36%nat) + (V 42%nat)) mod 2 ^ 64)
        /\ 1 <= (((((V 36%nat) + (V 42%nat)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 1
        /\ (((if (((V 36%nat) + (V 42%nat)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (((V 36%nat) + (V 42%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) 277844
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 276732
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 72) (Z.lxor ((4 * ((V 50%nat) / 4)) mod 2 ^ 64) 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 336) 8
        /\ L5.defined M' ((V 2%nat) - 272) 32
        /\ L5.defined M' ((V 2%nat) - 208) 32
        /\ L5.defined M' ((V 2%nat) - 144) 72
        /\ L5.defined M' ((V 2%nat) - 71) 7
        /\ L5.u8_at RSEGS M' (V 34%nat) 2)
      \/ (msteps RSEGS (st fx R 0x43888 M) (st fx' R' 0x43aac M')
        /\ (forall x, In x KS_tsSub1_1_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 8)
        /\ bv_unsigned (getr R' (reg 15)) = (((V 36%nat) + (V 42%nat)) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (V 34%nat) 0
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 0
        /\ (((((V 36%nat) + (V 42%nat)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ (((if (((V 36%nat) + (V 42%nat)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (((V 36%nat) + (V 42%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) 277844
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 276732
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 72) (Z.lxor ((4 * ((V 50%nat) / 4)) mod 2 ^ 64) 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 336) 8
        /\ L5.defined M' ((V 2%nat) - 272) 32
        /\ L5.defined M' ((V 2%nat) - 208) 32
        /\ L5.defined M' ((V 2%nat) - 144) 72
        /\ L5.defined M' ((V 2%nat) - 71) 7)).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0197 ()) [] (Mh_0197_blobs1.kr_b_031 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsSub2a := BndP_Ns_078.LibSegNs_tsSub2a.
Definition KS_tsSub2a : list nat := Eval vm_compute in (BG.kept_list 64 PtsSub2a.regs0 PtsSub2a.regs_out0).
Lemma KS_tsSub2a_ok : BG.kept_ok 64 PtsSub2a.regs0 PtsSub2a.regs_out0 KS_tsSub2a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_032 ())). Qed.
Lemma tsSub2a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) ->
  140735332483280 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 208) 208 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 208) 208 -> L5.u8_at RSEGS M ((V 2%nat) - 72) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483280 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 208) + 208 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 208)) -> L5.u8_at RSEGS M (V 34%nat) 2 -> L5.u64_at RSEGS M ((V 34%nat) + 8) 2 ->
  L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) -> L5.writable RSEGS M (V 34%nat) 32 -> 140735332483280 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 208) + 208 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 208)) -> L5.u8_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) (V 42%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 24) 0 -> ((V 33%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 33%nat)) -> 0 <= (V 41%nat) <= 1 ->
  0 <= (V 42%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x43888 M) (st fx' R' 0x4343c M')
        /\ (forall x, In x KS_tsSub2a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 277844
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 276732
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 72) (Z.lxor ((4 * ((V 50%nat) / 4)) mod 2 ^ 64) 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 208) 32
        /\ L5.defined M' ((V 2%nat) - 144) 72
        /\ L5.defined M' ((V 2%nat) - 71) 7).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_033 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsSub2b_0 := BndP_Ns_078.LibSegNs_tsSub2b_0.
Definition KS_tsSub2b_0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsSub2b_0.regs0 PtsSub2b_0.regs_out0).
Lemma KS_tsSub2b_0_ok : BG.kept_ok 64 PtsSub2b_0.regs0 PtsSub2b_0.regs_out0 KS_tsSub2b_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_034 ())). Qed.
Lemma tsSub2b_0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 208) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 9) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 56) ->
  140735332483280 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 208) 208 -> L5.img_clear M 65536 814272 ->
  140735332483280 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 208) + 208 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 208)) -> L5.u8_at RSEGS M (V 34%nat) 3 ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 3 -> L5.u64_at RSEGS M ((V 34%nat) + 16) 8 -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 43%nat) -> L5.writable RSEGS M (V 34%nat) 32 ->
  4096 <= (V 43%nat) <= 140737487306752 -> aligned (V 43%nat) 16 -> L5.writable RSEGS M (V 43%nat) 64 -> L5.defined M ((V 43%nat) + 24) 40 ->
  L5.u64_at RSEGS M (V 43%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 43%nat) + 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 43%nat) + 16) 0 -> ((V 43%nat) + 64 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 43%nat)) ->
  (((V 2%nat) - 208) + 208 <= (V 43%nat) \/ (V 43%nat) + 64 <= ((V 2%nat) - 208)) -> 1 <= (V 38%nat) <= 4611686018427387904 -> 0 <= (V 42%nat) <= 4294967295 -> L5.u8_at RSEGS M ((V 2%nat) - 72) (V 51%nat) ->
  0 <= (V 51%nat) <= 255 -> Z.testbit (V 51%nat) 0 = false -> L5.u64_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 9%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19))) -> L5.u64_at RSEGS M ((V 2%nat) - 152) 276732 -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 52%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> ~ (((V 43%nat) + 0) <= bv_unsigned a < ((V 43%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> ~ (((V 43%nat) + 0) <= i < ((V 43%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x43d54 M) (st fx' R' 0x43aac M')
        /\ (forall x, In x KS_tsSub2b_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 9%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 43%nat) + 8)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 18%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 2
        /\ L5.u8_at RSEGS M' (V 34%nat) 3
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) 8
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) (V 43%nat)
        /\ L5.u64_at RSEGS M' (V 43%nat) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 43%nat) + 8) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 43%nat) + 16) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 72) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 8%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 9%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 18%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 276732
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 52%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_035 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsSub2b_1 := BndP_Ns_078.LibSegNs_tsSub2b_1.
Definition KS_tsSub2b_1_0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsSub2b_1.regs0 PtsSub2b_1.regs_out0).
Lemma KS_tsSub2b_1_0_ok : BG.kept_ok 64 PtsSub2b_1.regs0 PtsSub2b_1.regs_out0 KS_tsSub2b_1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_036 ())). Qed.
Definition KS_tsSub2b_1_1 : list nat := Eval vm_compute in (BG.kept_list 64 PtsSub2b_1.regs0 PtsSub2b_1.regs_out1).
Lemma KS_tsSub2b_1_1_ok : BG.kept_ok 64 PtsSub2b_1.regs0 PtsSub2b_1.regs_out1 KS_tsSub2b_1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_037 ())). Qed.
Lemma tsSub2b_1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 208) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 9) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 56) ->
  140735332483280 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 208) 208 -> L5.img_clear M 65536 814272 ->
  140735332483280 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 208) + 208 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 208)) -> L5.u8_at RSEGS M (V 34%nat) 3 ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 3 -> L5.u64_at RSEGS M ((V 34%nat) + 16) 8 -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 43%nat) -> L5.writable RSEGS M (V 34%nat) 32 ->
  4096 <= (V 43%nat) <= 140737487306752 -> aligned (V 43%nat) 16 -> L5.writable RSEGS M (V 43%nat) 64 -> L5.defined M ((V 43%nat) + 24) 40 ->
  L5.u64_at RSEGS M (V 43%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 43%nat) + 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 43%nat) + 16) 0 -> ((V 43%nat) + 64 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 43%nat)) ->
  (((V 2%nat) - 208) + 208 <= (V 43%nat) \/ (V 43%nat) + 64 <= ((V 2%nat) - 208)) -> 1 <= (V 38%nat) <= 4611686018427387904 -> 0 <= (V 42%nat) <= 4294967295 -> L5.u8_at RSEGS M ((V 2%nat) - 72) (V 51%nat) ->
  0 <= (V 51%nat) <= 255 -> Z.testbit (V 51%nat) 0 = false -> L5.u64_at RSEGS M ((V 2%nat) - 64) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 9%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19))) -> L5.u64_at RSEGS M ((V 2%nat) - 152) 276732 -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 52%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 208) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> ~ (((V 43%nat) + 0) <= bv_unsigned a < ((V 43%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 208) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> ~ (((V 43%nat) + 0) <= i < ((V 43%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x43d54 M) (st fx' R' 0x43aac M')
        /\ (forall x, In x KS_tsSub2b_1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 9%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 43%nat) + 8)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 38%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 18%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 2
        /\ L5.u64_at RSEGS M' ((V 43%nat) + 8) ((V 38%nat) + 1)
        /\ 1 <= (((if (((V 36%nat) + (V 42%nat)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' (V 43%nat) (((V 36%nat) + (V 42%nat)) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (V 34%nat) 3
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) 8
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 43%nat) + 16) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 72) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 8%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 9%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 18%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 276732
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 52%nat))
      \/ (msteps RSEGS (st fx R 0x43d54 M) (st fx' R' 0x43aac M')
        /\ (forall x, In x KS_tsSub2b_1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 9%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 43%nat) + 8)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 18%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 2
        /\ (((if (((V 36%nat) + (V 42%nat)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' (V 43%nat) (((V 36%nat) + (V 42%nat)) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (V 34%nat) 3
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) 8
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 43%nat) + 8) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 43%nat) + 16) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 72) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 8%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 9%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 18%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 276732
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 52%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_038 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsRzA := BndP_Ns_077.LibSegNs_tsRzA.
Definition KS_tsRzA : list nat := Eval vm_compute in (BG.kept_list 64 PtsRzA.regs0 PtsRzA.regs_out0).
Lemma KS_tsRzA_ok : BG.kept_ok 64 PtsRzA.regs0 PtsRzA.regs_out0 KS_tsRzA = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_039 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma tsRzA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 3 ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 240) 240 -> L5.img_clear M 65536 814272 ->
  140735332483312 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 240) + 240 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 240)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 2 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) -> L5.writable RSEGS M (V 34%nat) 32 ->
  0 <= (V 37%nat) <= 255 -> Z.testbit (V 37%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x4343c M) (st fx' R' 0xbe8b0 M')
        /\ (forall x, In x KS_tsRzA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 276128
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 8
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 2305843009213693946
        /\ getr R' (reg 12) = Z_to_bv 64 2305843009213693943
        /\ getr R' (reg 18) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 38%nat)
        /\ bv_unsigned (getr R' (reg 20)) = (Z.land (V 37%nat) 2)
        /\ getr R' (reg 21) = Z_to_bv 64 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) 3
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 276108
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 3
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 275932
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 0
        /\ L5.u8_at RSEGS M' (V 34%nat) ((4 * ((V 37%nat) / 4)) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) 3
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_040 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsRzB0 := BndP_Ns_078.LibSegNs_tsRzB0.
Definition KS_tsRzB0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsRzB0.regs0 PtsRzB0.regs_out0).
Lemma KS_tsRzB0_ok : BG.kept_ok 64 PtsRzB0.regs0 PtsRzB0.regs_out0 KS_tsRzB0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_041 ())). Qed.
Lemma tsRzB0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 9) = Z_to_bv 64 8 -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 2 ->
  140735332483264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 65536 814272 ->
  140735332483264 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M (V 34%nat) 1 ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 34%nat) + 16) 0 -> L5.u64_at RSEGS M ((V 34%nat) + 24) 0 -> L5.writable RSEGS M (V 34%nat) 32 ->
  4096 <= (V 41%nat) <= 140737487306752 -> aligned (V 41%nat) 16 -> L5.writable RSEGS M (V 41%nat) 64 -> L5.defined M (V 41%nat) 64 ->
  ((V 41%nat) + 64 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 41%nat)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 64 <= ((V 2%nat) - 192)) -> L5.u64_at RSEGS M ((V 2%nat) - 168) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) 3 -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) 275932 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 21%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 112) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) 2 -> L5.u64_at RSEGS M ((V 2%nat) - 88) 3 ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) 275552 -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 9%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x436a0 M) (st fx' R' 0xb9ef8 M')
        /\ (forall x, In x KS_tsRzB0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 9%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 41%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ getr R' (reg 18) = Z_to_bv 64 (V 18%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 19%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 20%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 3
        /\ L5.u64_at RSEGS M' ((V 41%nat) + 8) (V 38%nat)
        /\ L5.u64_at RSEGS M' (V 41%nat) (V 36%nat)
        /\ L5.u8_at RSEGS M' (V 34%nat) 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) 8
        /\ L5.defined M' ((V 41%nat) + 16) 48
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 3
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 275932
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 21%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 20%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) 3
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 18%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 9%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 8%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_042 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsRzB2 := BndP_Ns_078.LibSegNs_tsRzB2.
Definition KS_tsRzB2 : list nat := Eval vm_compute in (BG.kept_list 64 PtsRzB2.regs0 PtsRzB2.regs_out0).
Lemma KS_tsRzB2_ok : BG.kept_ok 64 PtsRzB2.regs0 PtsRzB2.regs_out0 KS_tsRzB2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_043 ())). Qed.
Lemma tsRzB2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 9) = Z_to_bv 64 8 -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 2 -> getr R (reg 21) = Z_to_bv 64 2 ->
  140735332483264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 65536 814272 ->
  140735332483264 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M (V 34%nat) 1 ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 34%nat) + 16) 0 -> L5.u64_at RSEGS M ((V 34%nat) + 24) 0 -> L5.writable RSEGS M (V 34%nat) 32 ->
  4096 <= (V 41%nat) <= 140737487306752 -> aligned (V 41%nat) 16 -> L5.writable RSEGS M (V 41%nat) 64 -> L5.defined M (V 41%nat) 64 ->
  ((V 41%nat) + 64 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 41%nat)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 64 <= ((V 2%nat) - 192)) -> L5.u64_at RSEGS M ((V 2%nat) - 168) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) 3 -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) 275932 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 21%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 112) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) 2 -> L5.u64_at RSEGS M ((V 2%nat) - 88) 3 ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) 275552 -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 9%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x436a0 M) (st fx' R' 0xb9ef8 M')
        /\ (forall x, In x KS_tsRzB2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 9%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 41%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ getr R' (reg 18) = Z_to_bv 64 (V 18%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 19%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 20%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 3
        /\ L5.u64_at RSEGS M' ((V 41%nat) + 8) (V 38%nat)
        /\ L5.u64_at RSEGS M' (V 41%nat) (V 36%nat)
        /\ L5.u8_at RSEGS M' (V 34%nat) 3
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) 8
        /\ L5.defined M' ((V 41%nat) + 16) 48
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 3
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 275932
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 21%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 20%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) 3
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 18%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 9%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 8%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFn12P ()) [] (Mh_0197_blobs1.kr_b_044 ())). Qed.
(* [comment removed for export] *)

End PQTSGP.

End PnTsFn12P.
Module PnTsFnP.
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsFnP () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP9KS_tsMul0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP=word_of_zpolyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP9land_byteC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP<KS_tsMul0_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsMul1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsMul1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsMul19regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsMul1_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsAdd0_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd09regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsAdd0_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land2_bit1_falseC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd0<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd03ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd03ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd06cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd03kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP>KS_tsAdd0_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP>KS_tsAdd0_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsAdd1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsAdd1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd19regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP;KS_tsAdd1_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd1<seg_sound_axC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapK69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd13F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP>KS_tsAdd1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd16cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd13ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP>KS_tsAdd1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd16cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP7PtsAdd13ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsFnP6PQTSFP>KS_tsAdd1_2_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQTSFP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_045 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_046 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_047 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_048 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_049 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_050 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_051 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_052 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_053 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_054 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_055 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_056 ())). Qed.
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
Module PtsMul0 := BndP_Ns_077.LibSegNs_tsMul0.
Definition KS_tsMul0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsMul0.regs0 PtsMul0.regs_out0).
Lemma KS_tsMul0_ok : BG.kept_ok 64 PtsMul0.regs0 PtsMul0.regs_out0 KS_tsMul0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_057 ())). Qed.
Lemma tsMul0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 1000000000 ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 814272 ->
  140735332483248 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 176)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 34%nat) + 16) 0 -> L5.u64_at RSEGS M ((V 34%nat) + 24) 0 -> L5.writable RSEGS M (V 34%nat) 32 ->
  0 <= (V 37%nat) <= 255 -> Z.testbit (V 37%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x4446c M) (st fx' R' 0x4458c M')
        /\ (forall x, In x KS_tsMul0 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 37%nat) 253)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 8)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' (V 34%nat) (Z.land (V 37%nat) 253)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 0
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 34%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 1000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 279740
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_058 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsMul1 := BndP_Ns_077.LibSegNs_tsMul1.
Definition KS_tsMul1_0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsMul1.regs0 PtsMul1.regs_out0).
Lemma KS_tsMul1_0_ok : BG.kept_ok 64 PtsMul1.regs0 PtsMul1.regs_out0 KS_tsMul1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_059 ())). Qed.
Definition KS_tsMul1_1 : list nat := Eval vm_compute in (BG.kept_list 64 PtsMul1.regs0 PtsMul1.regs_out1).
Lemma KS_tsMul1_1_ok : BG.kept_ok 64 PtsMul1.regs0 PtsMul1.regs_out1 KS_tsMul1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_060 ())). Qed.
Definition KS_tsMul1_2 : list nat := Eval vm_compute in (BG.kept_list 64 PtsMul1.regs0 PtsMul1.regs_out2).
Lemma KS_tsMul1_2_ok : BG.kept_ok 64 PtsMul1.regs0 PtsMul1.regs_out2 KS_tsMul1_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_061 ())). Qed.
Lemma tsMul1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 1000000000 ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 814272 ->
  140735332483248 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 176)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) 0 -> L5.writable RSEGS M (V 34%nat) 32 ->
  0 <= (V 37%nat) <= 255 -> Z.testbit (V 37%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x4446c M) (st fx' R' 0x4458c M')
        /\ (forall x, In x KS_tsMul1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 6)) = (if ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64) <? ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64) then 1 else 0)
        /\ getr R' (reg 7) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 24)
        /\ bv_unsigned (getr R' (reg 15)) = (((if ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64) <? ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64) then 1 else 0) + (((1000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 34%nat) + 32)
        /\ bv_unsigned (getr R' (reg 17)) = (((1000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)
        /\ getr R' (reg 28) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 29)) = ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)
        /\ 1 <= (((((if ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64) <? ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64) then 1 else 0) + (((1000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) (((if ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64) <? ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64) then 1 else 0) + (((1000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 34%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 1000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 279740
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u8_at RSEGS M' (V 34%nat) (V 37%nat))
      \/ (msteps RSEGS (st fx R 0x4446c M) (st fx' R' 0x4458c M')
        /\ (forall x, In x KS_tsMul1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 6)) = (if ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64) <? ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64) then 1 else 0)
        /\ getr R' (reg 7) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ bv_unsigned (getr R' (reg 15)) = ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 34%nat) + 32)
        /\ bv_unsigned (getr R' (reg 17)) = (((1000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)
        /\ getr R' (reg 28) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 29)) = ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)
        /\ 1 <= ((((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 1
        /\ (((((if ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64) <? ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64) then 1 else 0) + (((1000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) (((if ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64) <? ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64) then 1 else 0) + (((1000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 34%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 1000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 279740
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u8_at RSEGS M' (V 34%nat) (V 37%nat))
      \/ (msteps RSEGS (st fx R 0x4446c M) (st fx' R' 0x4458c M')
        /\ (forall x, In x KS_tsMul1_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 6)) = (if ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64) <? ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64) then 1 else 0)
        /\ getr R' (reg 7) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 37%nat) 253)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 8)
        /\ bv_unsigned (getr R' (reg 15)) = ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 34%nat) + 32)
        /\ bv_unsigned (getr R' (reg 17)) = (((1000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)
        /\ getr R' (reg 28) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 29)) = ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (V 34%nat) (Z.land (V 37%nat) 253)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 0
        /\ ((((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ (((((if ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64) <? ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64) then 1 else 0) + (((1000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) (((if ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64) <? ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64) then 1 else 0) + (((1000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) ((((4294967296000000000 * ((V 36%nat) / 4294967296)) mod 2 ^ 64) + ((1000000000 * (Z.land (V 36%nat) 4294967295)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 34%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 1000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 279740
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat))).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0197 ()) [] (Mh_0197_blobs1.kr_b_062 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsAdd0 := BndP_Ns_077.LibSegNs_tsAdd0.
Definition KS_tsAdd0_0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsAdd0.regs0 PtsAdd0.regs_out0).
Lemma KS_tsAdd0_0_ok : BG.kept_ok 64 PtsAdd0.regs0 PtsAdd0.regs_out0 KS_tsAdd0_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_063 ())). Qed.
Definition KS_tsAdd0_1 : list nat := Eval vm_compute in (BG.kept_list 64 PtsAdd0.regs0 PtsAdd0.regs_out1).
Lemma KS_tsAdd0_1_ok : BG.kept_ok 64 PtsAdd0.regs0 PtsAdd0.regs_out1 KS_tsAdd0_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_064 ())). Qed.
Lemma tsAdd0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) ->
  140735332483296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.img_clear M 65536 814272 ->
  140735332483296 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 224) + 224 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 224)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 34%nat) + 16) 0 -> L5.u64_at RSEGS M ((V 34%nat) + 24) 0 -> L5.writable RSEGS M (V 34%nat) 32 ->
  0 <= (V 37%nat) <= 255 -> Z.testbit (V 37%nat) 0 = false -> Z.testbit (V 37%nat) 1 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x43208 M) (st fx' R' 0x43338 M')
        /\ (forall x, In x KS_tsAdd0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 35%nat)
        /\ 1 <= (((V 35%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 275004
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u8_at RSEGS M' (V 34%nat) (V 37%nat))
      \/ (msteps RSEGS (st fx R 0x43208 M) (st fx' R' 0x43338 M')
        /\ (forall x, In x KS_tsAdd0_1 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 37%nat) 253)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 8)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 35%nat)
        /\ L5.u8_at RSEGS M' (V 34%nat) (Z.land (V 37%nat) 253)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 0
        /\ (((V 35%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 275004
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_065 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsAdd1 := BndP_Ns_077.LibSegNs_tsAdd1.
Definition KS_tsAdd1_0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsAdd1.regs0 PtsAdd1.regs_out0).
Lemma KS_tsAdd1_0_ok : BG.kept_ok 64 PtsAdd1.regs0 PtsAdd1.regs_out0 KS_tsAdd1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_066 ())). Qed.
Definition KS_tsAdd1_1 : list nat := Eval vm_compute in (BG.kept_list 64 PtsAdd1.regs0 PtsAdd1.regs_out1).
Lemma KS_tsAdd1_1_ok : BG.kept_ok 64 PtsAdd1.regs0 PtsAdd1.regs_out1 KS_tsAdd1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_067 ())). Qed.
Definition KS_tsAdd1_2 : list nat := Eval vm_compute in (BG.kept_list 64 PtsAdd1.regs0 PtsAdd1.regs_out2).
Lemma KS_tsAdd1_2_ok : BG.kept_ok 64 PtsAdd1.regs0 PtsAdd1.regs_out2 KS_tsAdd1_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_068 ())). Qed.
Lemma tsAdd1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) ->
  140735332483296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.img_clear M 65536 814272 ->
  140735332483296 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 224) + 224 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 224)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) 0 -> L5.writable RSEGS M (V 34%nat) 32 ->
  0 <= (V 37%nat) <= 255 -> Z.testbit (V 37%nat) 0 = false -> Z.testbit (V 37%nat) 1 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x43208 M) (st fx' R' 0x43338 M')
        /\ (forall x, In x KS_tsAdd1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 24)
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 1
        /\ 1 <= (((if (((V 35%nat) + (V 36%nat)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (((V 35%nat) + (V 36%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 275004
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u8_at RSEGS M' (V 34%nat) (V 37%nat))
      \/ (msteps RSEGS (st fx R 0x43208 M) (st fx' R' 0x43338 M')
        /\ (forall x, In x KS_tsAdd1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ bv_unsigned (getr R' (reg 15)) = (((V 35%nat) + (V 36%nat)) mod 2 ^ 64)
        /\ 1 <= (((((V 35%nat) + (V 36%nat)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 1
        /\ (((if (((V 35%nat) + (V 36%nat)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (((V 35%nat) + (V 36%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 275004
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u8_at RSEGS M' (V 34%nat) (V 37%nat))
      \/ (msteps RSEGS (st fx R 0x43208 M) (st fx' R' 0x43338 M')
        /\ (forall x, In x KS_tsAdd1_2 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 37%nat) 253)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 34%nat) + 8)
        /\ bv_unsigned (getr R' (reg 15)) = (((V 35%nat) + (V 36%nat)) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (V 34%nat) (Z.land (V 37%nat) 253)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 0
        /\ (((((V 35%nat) + (V 36%nat)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ (((if (((V 35%nat) + (V 36%nat)) mod 2 ^ 64) <? (V 36%nat) then 1 else 0) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 16) (((V 35%nat) + (V 36%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 275004
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsFnP ()) [] (Mh_0197_blobs1.kr_b_069 ())). Qed.
(* [comment removed for export] *)

End PQTSFP.

End PnTsFnP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.
Module PnTsArith.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103.PnHeapR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnTsSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0197.PnTsFnP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r414d4_414d8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r41608_4160c.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsArith () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z7div_posK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR5xl_eqC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z9mod_smallC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC56Stdlib6ZArith6BinInt1Z<eq_decidableI47Corelib4Init5Logic2or00C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z7add_0_lK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR6xh_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR6xl_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR7x_splitC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR5m9_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsArith6PQTSAR5m9_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init9Datatypes3orbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z6eqb_eqC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes4bool02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r414d4_414d87W_44544C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r414d4_414d87F_44544C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r414d4_414d87D_44544C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r41608_4160c7W_432f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r41608_4160c7F_432f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r41608_4160c7D_432f0C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQTSAR.
Import PMS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Mul9.
  Variable x : Z.
  Hypothesis Hx : 0 <= x < 2 ^ 64.
  Let xh := x / 4294967296.
  Let xl := Z.land x 4294967295.
  Definition m9_T : Z := (4294967296000000000 * xh) mod 2 ^ 64.
  Definition m9_B : Z := (1000000000 * xl) mod 2 ^ 64.
  Definition m9_lo : Z := (m9_T + m9_B) mod 2 ^ 64.
  Definition m9_c : Z := if m9_lo <? m9_B then 1 else 0.
  Definition m9_A : Z := (1000000000 * xh) mod 2 ^ 64.
  Definition m9_hi : Z := (m9_c + m9_A / 4294967296) mod 2 ^ 64.

  Lemma xl_eq : xl = x mod 4294967296.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArith ()) ["Mul9"] (Mh_0197_blobs1.kr_b_070 ())). Qed.
  Lemma xh_rng : 0 <= xh < 4294967296.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArith ()) ["Mul9"] (Mh_0197_blobs1.kr_b_071 ())). Qed.
  Lemma xl_rng : 0 <= xl < 4294967296.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArith ()) ["Mul9"] (Mh_0197_blobs1.kr_b_072 ())). Qed.
  Lemma x_split : x = 4294967296 * xh + xl.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArith ()) ["Mul9"] (Mh_0197_blobs1.kr_b_073 ())). Qed.

  Lemma mul9_ok : m9_lo + 2 ^ 64 * m9_hi = x * 1000000000 /\ 0 <= m9_lo < 2 ^ 64 /\ 0 <= m9_hi < 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArith ()) ["Mul9"] (Mh_0197_blobs1.kr_b_074 ())). Qed.
End Mul9.

(* [comment removed for export] *)
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Local Ltac rifeed := first [ PMK.sc | unfold PQTSFP.aligned; first [ assumption | lia ] ].

Lemma wlen_eq lo hi : 0 <= lo -> 0 <= hi ->
  PQTSS.wlen lo hi = (if Z.eqb hi 0 then (if Z.eqb lo 0 then 0%nat else 1%nat) else 2%nat).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArith ()) [] (Mh_0197_blobs1.kr_b_075 ())). Qed.

(* [comment removed for export] *)
Lemma land253_id fb : 0 <= fb < 256 -> Z.testbit fb 1 = false -> Z.land fb 253 = fb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArith ()) [] (Mh_0197_blobs1.kr_b_076 ())). Qed.

(* [comment removed for export] *)
Lemma ret_mul fx R M r : getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 0x4458c) M (seg_rom RSEGS)) (@mkst fx R (Z_to_bv 64 r) M (seg_rom RSEGS)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArith ()) [] (Mh_0197_blobs1.kr_b_077 ())). Qed.
Lemma ret_add fx R M r : getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 0x43338) M (seg_rom RSEGS)) (@mkst fx R (Z_to_bv 64 r) M (seg_rom RSEGS)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArith ()) [] (Mh_0197_blobs1.kr_b_078 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem mulu_ok : PQTSS.mulu_run_stmt.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0197 ()) [] (Mh_0197_blobs1.kr_b_079 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem add64_ok : PQTSS.add64_run_stmt.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0197 ()) [] (Mh_0197_blobs1.kr_b_080 ())). Qed.

End PQTSAR.

End PnTsArith.
Module PnTsArmP.
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsArmP () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8a05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8a09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP8KS_ts8a0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8a0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8a03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8a02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8a03NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8a03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8a03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP;KS_ts8a0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8a9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP7KS_ts8aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8a<seg_sound_axC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthc79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8a6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8a3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP:KS_ts8a_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop01I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8b9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP7KS_ts8bC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8b<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8b3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP:KS_ts8b_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP8KS_ts8cSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cS<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP?u8x2_of_KWord2aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cS3NX0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP;KS_ts8cS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cS6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP8KS_ts8cLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP;KS_ts8cL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8cL6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8d5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8d9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP7KS_ts8dC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8d<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8d3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8d2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8d3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8d3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8d3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP:KS_ts8d_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP5Pts8d6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8dS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8dS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP8KS_ts8dSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8dS<seg_sound_axC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8dS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8dS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8dS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8dS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8dS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP;KS_ts8dS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts8dS6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts_q95regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts_q99regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP8KS_ts_q9C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts_q9<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts_q93PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts_q92F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts_q93NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts_q93kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts_q93ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP;KS_ts_q9_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsArmP6PQTSAP6Pts_q96cells0C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQTSAP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_081 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_082 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_083 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_084 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_085 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_086 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_087 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_088 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_089 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_090 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_091 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_092 ())). Qed.
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
Module Pts8a0 := BndP_Ns_076.LibSegNs_ts8a0.
Definition KS_ts8a0 : list nat := Eval vm_compute in (BG.kept_list 64 Pts8a0.regs0 Pts8a0.regs_out0).
Lemma KS_ts8a0_ok : BG.kept_ok 64 Pts8a0.regs0 Pts8a0.regs_out0 KS_ts8a0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_093 ())). Qed.
Lemma ts8a0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 20) = Z_to_bv 64 8 -> getr R (reg 21) = Z_to_bv 64 255 ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> 8 <= (V 49%nat) <= 8 -> L5.defined M ((V 2%nat) - 72) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x45bc4 M) (st fx' R' 0x45c30 M')
        /\ (forall x, In x KS_ts8a0 -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_094 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts8a := BndP_Ns_076.LibSegNs_ts8a.
Definition KS_ts8a : list nat := Eval vm_compute in (BG.kept_list 64 Pts8a.regs0 Pts8a.regs_out0).
Lemma KS_ts8a_ok : BG.kept_ok 64 Pts8a.regs0 Pts8a.regs_out0 KS_ts8a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_095 ())). Qed.
Lemma ts8a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 8 -> getr R (reg 21) = Z_to_bv 64 255 ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x45c30 M) (st fx' R' 0x4446c M')
        /\ (forall x, In x KS_ts8a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 285788
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 1000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (((1073741824 * (V 35%nat)) mod 2 ^ 64) / 1073741824)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (if 0 <? (((1073741824 * (V 35%nat)) mod 2 ^ 64) / 1073741824) then 1 else 0)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 104) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_096 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts8b := BndP_Ns_076.LibSegNs_ts8b.
Definition KS_ts8b : list nat := Eval vm_compute in (BG.kept_list 64 Pts8b.regs0 Pts8b.regs_out0).
Lemma KS_ts8b_ok : BG.kept_ok 64 Pts8b.regs0 Pts8b.regs_out0 KS_ts8b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_097 ())). Qed.
Lemma ts8b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x45c5c M) (st fx' R' 0x43208 M')
        /\ (forall x, In x KS_ts8b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 285800
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 35%nat) / 17179869184)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_098 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts8cS := BndP_Ns_076.LibSegNs_ts8cS.
Definition KS_ts8cS : list nat := Eval vm_compute in (BG.kept_list 64 Pts8cS.regs0 Pts8cS.regs_out0).
Lemma KS_ts8cS_ok : BG.kept_ok 64 Pts8cS.regs0 Pts8cS.regs_out0 KS_ts8cS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_099 ())). Qed.
Lemma ts8cS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 8 -> getr R (reg 21) = Z_to_bv 64 255 ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 328) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = false ->
  L5.writable RSEGS M ((V 36%nat) + 328) 24 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 328) <= bv_unsigned a < ((V 36%nat) + 328) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 328) <= i < ((V 36%nat) + 328) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x45c68 M) (st fx' R' 0x46c40 M')
        /\ (forall x, In x KS_ts8cS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287024
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 328)
        /\ (L5.u8_at RSEGS M' ((V 36%nat) + 328) 0 /\ L5.u8_at RSEGS M' (((V 36%nat) + 328) + 1) 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_100 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts8cL := BndP_Ns_076.LibSegNs_ts8cL.
Definition KS_ts8cL : list nat := Eval vm_compute in (BG.kept_list 64 Pts8cL.regs0 Pts8cL.regs_out0).
Lemma KS_ts8cL_ok : BG.kept_ok 64 Pts8cL.regs0 Pts8cL.regs_out0 KS_ts8cL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_101 ())). Qed.
Lemma ts8cL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 8 -> getr R (reg 21) = Z_to_bv 64 255 ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 328) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 36%nat) + 344) (V 39%nat) -> 4096 <= (V 39%nat) <= 140737488289792 -> L5.writable RSEGS M (V 39%nat) 1 -> L5.writable RSEGS M ((V 36%nat) + 328) 24 ->
  ((V 39%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 400 <= (V 39%nat)) -> (((V 2%nat) - 144) + 144 <= (V 39%nat) \/ (V 39%nat) + 1 <= ((V 2%nat) - 144)) -> ((V 39%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 39%nat)) -> ((V 39%nat) + 1 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 39%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 336) <= bv_unsigned a < ((V 36%nat) + 336) + 8) -> ~ (((V 39%nat) + 0) <= bv_unsigned a < ((V 39%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 336) <= i < ((V 36%nat) + 336) + 8) -> ~ (((V 39%nat) + 0) <= i < ((V 39%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x45c68 M) (st fx' R' 0x46c40 M')
        /\ (forall x, In x KS_ts8cL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287024
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 328)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 336) 0
        /\ L5.u8_at RSEGS M' (V 39%nat) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_102 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts8d := BndP_Ns_076.LibSegNs_ts8d.
Definition KS_ts8d : list nat := Eval vm_compute in (BG.kept_list 64 Pts8d.regs0 Pts8d.regs_out0).
Lemma KS_ts8d_ok : BG.kept_ok 64 Pts8d.regs0 Pts8d.regs_out0 KS_ts8d = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_103 ())). Qed.
Lemma ts8d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 8 -> getr R (reg 21) = Z_to_bv 64 255 ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u64_at RSEGS M (V 37%nat) 785032 -> L5.u8_at RSEGS M ((V 36%nat) + 328) (V 33%nat) -> 0 <= (V 33%nat) <= 255 ->
  Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 336) (V 40%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 344) (V 39%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46130 M) (st fx' R' 0x3b934 M')
        /\ (forall x, In x KS_ts8d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287104
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 12) = Z_to_bv 64 7
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 244020
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 39%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_104 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts8dS := BndP_Ns_077.LibSegNs_ts8dS.
Definition KS_ts8dS : list nat := Eval vm_compute in (BG.kept_list 64 Pts8dS.regs0 Pts8dS.regs_out0).
Lemma KS_ts8dS_ok : BG.kept_ok 64 Pts8dS.regs0 Pts8dS.regs_out0 KS_ts8dS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_105 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ts8dS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 8 -> getr R (reg 21) = Z_to_bv 64 255 ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u64_at RSEGS M (V 37%nat) 785032 -> L5.u8_at RSEGS M ((V 36%nat) + 328) (V 33%nat) -> 0 <= (V 33%nat) <= 255 ->
  Z.testbit (V 33%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46130 M) (st fx' R' 0x3b934 M')
        /\ (forall x, In x KS_ts8dS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287104
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 12) = Z_to_bv 64 7
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 244020
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 33%nat) / 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 36%nat) + 329)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_106 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts_q9 := BndP_Ns_079.LibSegNs_ts_q9.
Definition KS_ts_q9 : list nat := Eval vm_compute in (BG.kept_list 64 Pts_q9.regs0 Pts_q9.regs_out0).
Lemma KS_ts_q9_ok : BG.kept_ok 64 Pts_q9.regs0 Pts_q9.regs_out0 KS_ts_q9 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_107 ())). Qed.
Lemma ts_q9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 46%nat) ->
  L5.u8_at RSEGS M ((V 36%nat) + 16) 0 -> L5.u8_at RSEGS M ((V 2%nat) - 104) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46180 M) (st fx' R' 0x460c0 M')
        /\ (forall x, In x KS_ts_q9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArmP ()) [] (Mh_0197_blobs1.kr_b_108 ())). Qed.
(* [comment removed for export] *)

End PQTSAP.

End PnTsArmP.
Module PnTsArm12P.
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsArm12P () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z;lxor_nonnegK46Stdlib9micromega5Tauto8GFormula09C56Stdlib6ZArith6BinInt1Z9log2_lxorC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12a05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12a09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12a0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12a0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12a03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12a02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12a03NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12a03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12a03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12a0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP6Pts12e5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP6Pts12e9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP8KS_ts12eC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP6Pts12e<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP6Pts12e3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP6Pts12e2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP6Pts12e3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP6Pts12e3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP6Pts12e3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP;KS_ts12e_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bz5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bz9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12bzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bz<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bz3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bz2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bz3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bz6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bz3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bz3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12bz_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bn9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12bnC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bn<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9land_byteC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bn3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bn3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12bn_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5aluop07I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12bn6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12c05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12c09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12c0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12c0<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0=C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12c03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12c02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12c03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12c03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12c03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12c0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cZ9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12cZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cZ<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cZ6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cZ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cZ3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12cZ_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cP5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cP9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12cPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cP<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cP3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cP2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cP3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cP6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cP3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cP3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12cP_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cN9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12cNC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cN<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cN6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cN3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12cN3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12cN_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12tSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tS<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP?u8x2_of_KWord2aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tS3NX0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12tS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tS6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12tLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12tL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12tL6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12uSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12uS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uS6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12uLC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12uL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12uL6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12vSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vS<seg_sound_axC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12vS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vS6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12vLC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12vL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12vL6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qI5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qI9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12qIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qI<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qI3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qI2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qI3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qI3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qI3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12qI_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qI6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qD9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12qDC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qD<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qD3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12qD_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qD6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qE9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP9KS_ts12qEC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qE<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP7Pts12qE3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsArm12P6PQTSBP<KS_ts12qE_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQTSBP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_109 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_110 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_111 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_112 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_113 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_114 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_115 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_116 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_117 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_118 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_119 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_120 ())). Qed.
(* [comment removed for export] *)
Lemma lxor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_121 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lxor _ _ < 256 => apply lxor_byte; byte_go
  | |- 0 <= ?x mod 18446744073709551616 < 256 => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia); byte_go
  | |- 0 <= ?x mod 2 ^ 64 < 256 => rewrite (Z.mod_small x (2 ^ 64)) by (zfacts; lia); byte_go
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; rewrite ?Z.lxor_0_l, ?Z.lxor_0_r, ?Z.lor_0_l, ?Z.lor_0_r; byte_go.
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
Module Pts12a0 := BndP_Ns_075.LibSegNs_ts12a0.
Definition KS_ts12a0 : list nat := Eval vm_compute in (BG.kept_list 64 Pts12a0.regs0 Pts12a0.regs_out0).
Lemma KS_ts12a0_ok : BG.kept_ok 64 Pts12a0.regs0 Pts12a0.regs_out0 KS_ts12a0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_122 ())). Qed.
Lemma ts12a0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 10) = Z_to_bv 64 4 -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 20) = Z_to_bv 64 4 -> getr R (reg 21) = Z_to_bv 64 255 ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> 0 <= (V 35%nat) <= 4294967295 -> L5.u32_at RSEGS M ((V 2%nat) - 108) (V 35%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x45f50 M) (st fx' R' 0x4629c M')
        /\ (forall x, In x KS_ts12a0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 286572
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 72)
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ getr R' (reg 20) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 8).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_123 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12e := BndP_Ns_075.LibSegNs_ts12e.
Definition KS_ts12e : list nat := Eval vm_compute in (BG.kept_list 64 Pts12e.regs0 Pts12e.regs_out0).
Lemma KS_ts12e_ok : BG.kept_ok 64 Pts12e.regs0 Pts12e.regs_out0 KS_ts12e = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_124 ())). Qed.
Lemma ts12e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 8 ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> 0 <= (V 49%nat) <= 7 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x45f6c M) (st fx' R' 0x41a54 M')
        /\ (forall x, In x KS_ts12e -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 286876
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_125 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12bz := BndP_Ns_075.LibSegNs_ts12bz.
Definition KS_ts12bz : list nat := Eval vm_compute in (BG.kept_list 64 Pts12bz.regs0 Pts12bz.regs_out0).
Lemma KS_ts12bz_ok : BG.kept_ok 64 Pts12bz.regs0 Pts12bz.regs_out0 KS_ts12bz = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_126 ())). Qed.
Lemma ts12bz_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 10) = Z_to_bv 64 8 -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 8 ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 72) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x45f6c M) (st fx' R' 0x4446c M')
        /\ (forall x, In x KS_ts12bz -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 286736
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 1000000000
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 65280
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 104) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_127 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12bn := BndP_Ns_075.LibSegNs_ts12bn.
Definition KS_ts12bn : list nat := Eval vm_compute in (BG.kept_list 64 Pts12bn.regs0 Pts12bn.regs_out0).
Lemma KS_ts12bn_ok : BG.kept_ok 64 Pts12bn.regs0 Pts12bn.regs_out0 KS_ts12bn = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_128 ())). Qed.
Lemma ts12bn_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 10) = Z_to_bv 64 8 -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 8 ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 50%nat) -> 1 <= (V 50%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x45f6c M) (st fx' R' 0x4446c M')
        /\ (forall x, In x KS_ts12bn -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 286736
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 1000000000
        /\ bv_unsigned (getr R' (reg 14)) = (Z.land ((V 50%nat) / 64) 2)
        /\ getr R' (reg 19) = Z_to_bv 64 65280
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 104) (Z.land ((V 50%nat) / 64) 2)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_129 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12c0 := BndP_Ns_075.LibSegNs_ts12c0.
Definition KS_ts12c0 : list nat := Eval vm_compute in (BG.kept_list 64 Pts12c0.regs0 Pts12c0.regs_out0).
Lemma KS_ts12c0_ok : BG.kept_ok 64 Pts12c0.regs0 Pts12c0.regs_out0 KS_ts12c0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_130 ())). Qed.
Lemma ts12c0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 65280 -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46010 M) (st fx' R' 0x46034 M')
        /\ (forall x, In x KS_ts12c0 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (Z.land ((V 35%nat) / 256) 65280) ((V 35%nat) / 16777216))
        /\ bv_unsigned (getr R' (reg 12)) = ((256 * (Z.land (V 35%nat) 65280)) mod 2 ^ 64)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_131 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12cZ := BndP_Ns_075.LibSegNs_ts12cZ.
Definition KS_ts12cZ : list nat := Eval vm_compute in (BG.kept_list 64 Pts12cZ.regs0 Pts12cZ.regs_out0).
Lemma KS_ts12cZ_ok : BG.kept_ok 64 Pts12cZ.regs0 Pts12cZ.regs_out0 KS_ts12cZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_132 ())). Qed.
Lemma ts12cZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 55%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) ->
  140735332483264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 140735332483264 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 192)) -> 140735332483264 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 192) + 192 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 192)) -> 140735332483264 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 192)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 2%nat) - 104) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 96) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 88) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.writable RSEGS M ((V 2%nat) - 104) 32 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 48) -> ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 48) -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46034 M) (st fx' R' 0x46f7c M')
        /\ (forall x, In x KS_ts12cZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287164
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 88)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 286784
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 104) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_133 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12cP := BndP_Ns_075.LibSegNs_ts12cP.
Definition KS_ts12cP : list nat := Eval vm_compute in (BG.kept_list 64 Pts12cP.regs0 Pts12cP.regs_out0).
Lemma KS_ts12cP_ok : BG.kept_ok 64 Pts12cP.regs0 Pts12cP.regs_out0 KS_ts12cP = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_134 ())). Qed.
Lemma ts12cP_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 55%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) ->
  140735332483264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 140735332483264 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 192)) -> 140735332483264 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 192) + 192 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 192)) -> 140735332483264 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 192)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 2%nat) - 104) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 54%nat) -> L5.writable RSEGS M ((V 2%nat) - 104) 32 -> 1 <= (V 52%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 48) -> ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 48) -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46034 M) (st fx' R' 0x46f7c M')
        /\ (forall x, In x KS_ts12cP -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287164
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 88)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 286784
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 104) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 54%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_135 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12cN := BndP_Ns_075.LibSegNs_ts12cN.
Definition KS_ts12cN : list nat := Eval vm_compute in (BG.kept_list 64 Pts12cN.regs0 Pts12cN.regs_out0).
Lemma KS_ts12cN_ok : BG.kept_ok 64 Pts12cN.regs0 Pts12cN.regs_out0 KS_ts12cN = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_136 ())). Qed.
Lemma ts12cN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 55%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) ->
  140735332483264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 140735332483264 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 192)) -> 140735332483264 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 192) + 192 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 192)) -> 140735332483264 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 192)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 2%nat) - 104) 2 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 54%nat) -> L5.writable RSEGS M ((V 2%nat) - 104) 32 -> 1 <= (V 52%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 48) -> ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 32) -> ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 48) -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 32) -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46034 M) (st fx' R' 0x43888 M')
        /\ (forall x, In x KS_ts12cN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 286828
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 88)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 19)) = ((4294967296 * (V 55%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (((4294967296 * (V 55%nat)) mod 2 ^ 64) / 4294967296)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (if 0 <? (V 35%nat) then 1 else 0)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 144) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 286784
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 104) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 54%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_137 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12tS := BndP_Ns_076.LibSegNs_ts12tS.
Definition KS_ts12tS : list nat := Eval vm_compute in (BG.kept_list 64 Pts12tS.regs0 Pts12tS.regs_out0).
Lemma KS_ts12tS_ok : BG.kept_ok 64 Pts12tS.regs0 Pts12tS.regs_out0 KS_ts12tS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_138 ())). Qed.
Lemma ts12tS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 55%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 328) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = false ->
  L5.writable RSEGS M ((V 36%nat) + 328) 24 -> L5.u8_at RSEGS M ((V 2%nat) - 144) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 328) <= bv_unsigned a < ((V 36%nat) + 328) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 328) <= i < ((V 36%nat) + 328) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x4606c M) (st fx' R' 0x46c40 M')
        /\ (forall x, In x KS_ts12tS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287208
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 328)
        /\ (L5.u8_at RSEGS M' ((V 36%nat) + 328) 0 /\ L5.u8_at RSEGS M' (((V 36%nat) + 328) + 1) 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_139 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12tL := BndP_Ns_076.LibSegNs_ts12tL.
Definition KS_ts12tL : list nat := Eval vm_compute in (BG.kept_list 64 Pts12tL.regs0 Pts12tL.regs_out0).
Lemma KS_ts12tL_ok : BG.kept_ok 64 Pts12tL.regs0 Pts12tL.regs_out0 KS_ts12tL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_140 ())). Qed.
Lemma ts12tL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 55%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 328) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 36%nat) + 344) (V 39%nat) -> 4096 <= (V 39%nat) <= 140737488289792 -> L5.writable RSEGS M (V 39%nat) 1 -> L5.writable RSEGS M ((V 36%nat) + 328) 24 ->
  ((V 39%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 400 <= (V 39%nat)) -> (((V 2%nat) - 144) + 144 <= (V 39%nat) \/ (V 39%nat) + 1 <= ((V 2%nat) - 144)) -> ((V 39%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 39%nat)) -> ((V 39%nat) + 1 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 39%nat)) ->
  L5.u8_at RSEGS M ((V 2%nat) - 144) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 336) <= bv_unsigned a < ((V 36%nat) + 336) + 8) -> ~ (((V 39%nat) + 0) <= bv_unsigned a < ((V 39%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 336) <= i < ((V 36%nat) + 336) + 8) -> ~ (((V 39%nat) + 0) <= i < ((V 39%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x4606c M) (st fx' R' 0x46c40 M')
        /\ (forall x, In x KS_ts12tL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287208
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 328)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 336) 0
        /\ L5.u8_at RSEGS M' (V 39%nat) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_141 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12uS := BndP_Ns_076.LibSegNs_ts12uS.
Definition KS_ts12uS : list nat := Eval vm_compute in (BG.kept_list 64 Pts12uS.regs0 Pts12uS.regs_out0).
Lemma KS_ts12uS_ok : BG.kept_ok 64 Pts12uS.regs0 Pts12uS.regs_out0 KS_ts12uS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_142 ())). Qed.
Lemma ts12uS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 55%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 328) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = false ->
  L5.writable RSEGS M ((V 36%nat) + 328) 24 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 328) <= bv_unsigned a < ((V 36%nat) + 328) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 328) <= i < ((V 36%nat) + 328) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x461bc M) (st fx' R' 0x46c40 M')
        /\ (forall x, In x KS_ts12uS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287208
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 328)
        /\ (L5.u8_at RSEGS M' ((V 36%nat) + 328) 0 /\ L5.u8_at RSEGS M' (((V 36%nat) + 328) + 1) 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_143 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12uL := BndP_Ns_076.LibSegNs_ts12uL.
Definition KS_ts12uL : list nat := Eval vm_compute in (BG.kept_list 64 Pts12uL.regs0 Pts12uL.regs_out0).
Lemma KS_ts12uL_ok : BG.kept_ok 64 Pts12uL.regs0 Pts12uL.regs_out0 KS_ts12uL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_144 ())). Qed.
Lemma ts12uL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 55%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 328) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 36%nat) + 344) (V 39%nat) -> 4096 <= (V 39%nat) <= 140737488289792 -> L5.writable RSEGS M (V 39%nat) 1 -> L5.writable RSEGS M ((V 36%nat) + 328) 24 ->
  ((V 39%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 400 <= (V 39%nat)) -> (((V 2%nat) - 144) + 144 <= (V 39%nat) \/ (V 39%nat) + 1 <= ((V 2%nat) - 144)) -> ((V 39%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 39%nat)) -> ((V 39%nat) + 1 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 39%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 336) <= bv_unsigned a < ((V 36%nat) + 336) + 8) -> ~ (((V 39%nat) + 0) <= bv_unsigned a < ((V 39%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 336) <= i < ((V 36%nat) + 336) + 8) -> ~ (((V 39%nat) + 0) <= i < ((V 39%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x461bc M) (st fx' R' 0x46c40 M')
        /\ (forall x, In x KS_ts12uL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287208
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 328)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 336) 0
        /\ L5.u8_at RSEGS M' (V 39%nat) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_145 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12vS := BndP_Ns_076.LibSegNs_ts12vS.
Definition KS_ts12vS : list nat := Eval vm_compute in (BG.kept_list 64 Pts12vS.regs0 Pts12vS.regs_out0).
Lemma KS_ts12vS_ok : BG.kept_ok 64 Pts12vS.regs0 Pts12vS.regs_out0 KS_ts12vS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_146 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ts12vS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 55%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u64_at RSEGS M (V 37%nat) 785032 -> L5.u8_at RSEGS M ((V 36%nat) + 328) (V 33%nat) -> 0 <= (V 33%nat) <= 255 ->
  Z.testbit (V 33%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x461e8 M) (st fx' R' 0x3b934 M')
        /\ (forall x, In x KS_ts12vS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287288
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 12) = Z_to_bv 64 7
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 244020
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 33%nat) / 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 36%nat) + 329)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_147 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12vL := BndP_Ns_076.LibSegNs_ts12vL.
Definition KS_ts12vL : list nat := Eval vm_compute in (BG.kept_list 64 Pts12vL.regs0 Pts12vL.regs_out0).
Lemma KS_ts12vL_ok : BG.kept_ok 64 Pts12vL.regs0 Pts12vL.regs_out0 KS_ts12vL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_148 ())). Qed.
Lemma ts12vL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 (V 55%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u64_at RSEGS M (V 37%nat) 785032 -> L5.u8_at RSEGS M ((V 36%nat) + 328) (V 33%nat) -> 0 <= (V 33%nat) <= 255 ->
  Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 336) (V 40%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 344) (V 39%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x461e8 M) (st fx' R' 0x3b934 M')
        /\ (forall x, In x KS_ts12vL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287288
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 12) = Z_to_bv 64 7
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 244020
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 39%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_149 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12qI := BndP_Ns_076.LibSegNs_ts12qI.
Definition KS_ts12qI : list nat := Eval vm_compute in (BG.kept_list 64 Pts12qI.regs0 Pts12qI.regs_out0).
Lemma KS_ts12qI_ok : BG.kept_ok 64 Pts12qI.regs0 Pts12qI.regs_out0 KS_ts12qI = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_150 ())). Qed.
Lemma ts12qI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 46%nat) ->
  L5.u8_at RSEGS M ((V 36%nat) + 16) 0 -> L5.u8_at RSEGS M ((V 2%nat) - 104) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46238 M) (st fx' R' 0x460c0 M')
        /\ (forall x, In x KS_ts12qI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_151 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12qD := BndP_Ns_075.LibSegNs_ts12qD.
Definition KS_ts12qD : list nat := Eval vm_compute in (BG.kept_list 64 Pts12qD.regs0 Pts12qD.regs_out0).
Lemma KS_ts12qD_ok : BG.kept_ok 64 Pts12qD.regs0 Pts12qD.regs_out0 KS_ts12qD = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_152 ())). Qed.
Lemma ts12qD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 36%nat) + 16) 0 -> L5.u8_at RSEGS M ((V 2%nat) - 104) (V 33%nat) -> 0 <= (V 33%nat) <= 255 ->
  Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 54%nat) -> 1 <= (V 54%nat) <= 18446744073709551615 ->
  0 <= (V 53%nat) <= 1024 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46238 M) (st fx' R' 0x63dc4 M')
        /\ (forall x, In x KS_ts12qD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 287148
        /\ getr R' (reg 10) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 53%nat))
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_153 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pts12qE := BndP_Ns_076.LibSegNs_ts12qE.
Definition KS_ts12qE : list nat := Eval vm_compute in (BG.kept_list 64 Pts12qE.regs0 Pts12qE.regs_out0).
Lemma KS_ts12qE_ok : BG.kept_ok 64 Pts12qE.regs0 Pts12qE.regs_out0 KS_ts12qE = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_154 ())). Qed.
Lemma ts12qE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483216 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 144) 144 -> 140735332483216 <= (V 36%nat) <= 140737488354928 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 36%nat) \/ (V 36%nat) + 400 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 144) + 144 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 144)) -> 140735332483216 <= (V 37%nat) <= 140737488355232 -> aligned (V 37%nat) 8 -> (((V 2%nat) - 144) + 144 <= (V 37%nat) \/ (V 37%nat) + 96 <= ((V 2%nat) - 144)) ->
  L5.img_clear M 65536 814272 -> ((V 36%nat) + 400 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 96 <= (V 38%nat)) -> ((V 36%nat) + 400 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  L5.writable RSEGS M ((V 36%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x461ac M) (st fx' R' 0x460c0 M')
        /\ (forall x, In x KS_ts12qE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsArm12P ()) [] (Mh_0197_blobs1.kr_b_155 ())). Qed.
(* [comment removed for export] *)

End PQTSBP.

End PnTsArm12P.
Module PnTsDivP.
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsDivP () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z;lxor_nonnegK46Stdlib9micromega5Tauto8GFormula09C56Stdlib6ZArith6BinInt1Z9log2_lxorC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP:KS_tsDivA0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InK59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0=C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP9land_byteC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8lor_byteC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0>C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP9land_le_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z:mul_div_leC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z8lxor_0_lc69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP@defined_of_KUnkaC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP=KS_tsDivA0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP:KS_tsDivA1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivA13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP=KS_tsDivA1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP<KS_tsDivBa_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBa9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP<KS_tsDivBa_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBb5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBb9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP:KS_tsDivBbC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBb<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBb3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBb2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBb3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBb6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBb3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP8PtsDivBb3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsDivP6PQTSDP=KS_tsDivBb_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQTSDP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_156 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_157 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_158 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_159 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_160 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_161 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_162 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_163 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_164 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_165 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_166 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_167 ())). Qed.
(* [comment removed for export] *)
Lemma lxor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_168 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lxor _ _ < 256 => apply lxor_byte; byte_go
  | |- 0 <= ?x mod 18446744073709551616 < 256 => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia); byte_go
  | |- 0 <= ?x mod 2 ^ 64 < 256 => rewrite (Z.mod_small x (2 ^ 64)) by (zfacts; lia); byte_go
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; rewrite ?Z.lxor_0_l, ?Z.lxor_0_r, ?Z.lor_0_l, ?Z.lor_0_r; byte_go.
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
Module PtsDivA0 := BndP_Ns_077.LibSegNs_tsDivA0.
Definition KS_tsDivA0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsDivA0.regs0 PtsDivA0.regs_out0).
Lemma KS_tsDivA0_ok : BG.kept_ok 64 PtsDivA0.regs0 PtsDivA0.regs_out0 KS_tsDivA0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_169 ())). Qed.
Lemma tsDivA0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) + 72) -> getr R (reg 11) = Z_to_bv 64 ((V 2%nat) + 8) -> getr R (reg 12) = Z_to_bv 64 ((V 2%nat) + 72) -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) + 40) -> getr R (reg 14) = Z_to_bv 64 1 ->
  140735332483552 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 480) 480 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 480) 480 -> L5.writable RSEGS M ((V 2%nat) + 8) 96 -> L5.u8_at RSEGS M ((V 2%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 16) 1 ->
  L5.u64_at RSEGS M ((V 2%nat) + 24) 10000000000000000000 -> L5.u64_at RSEGS M ((V 2%nat) + 32) 0 -> L5.u8_at RSEGS M ((V 2%nat) + 40) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 48) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) + 56) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 64) 0 -> L5.u8_at RSEGS M ((V 2%nat) + 72) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 80) 1 ->
  L5.u64_at RSEGS M ((V 2%nat) + 88) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 96) (V 38%nat) -> 0 <= (V 37%nat) <= 255 -> Z.testbit (V 37%nat) 0 = false ->
  1 <= (V 36%nat) <= 9999999999999999999 -> 0 <= (V 43%nat) <= 255 -> Z.testbit (V 43%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 480) <= bv_unsigned a < ((V 2%nat) - 480) + 480) -> ~ (((V 2%nat) + 8) <= bv_unsigned a < ((V 2%nat) + 8) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 480) <= i < ((V 2%nat) - 480) + 480) -> ~ (((V 2%nat) + 8) <= i < ((V 2%nat) + 8) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42450 M) (st fx' R' 0x42a18 M')
        /\ (forall x, In x KS_tsDivA0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 40) (Z.lor (Z.land (V 43%nat) 253) (Z.land (V 37%nat) 2))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 56) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 64) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 48) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 472) ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 456) ((V 2%nat) - 168)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 448) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 440) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 432) ((V 2%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 424) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 384) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 376) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 368) ((V 2%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 360) 275408
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 352) ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 344) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) ((V 2%nat) + 72)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) ((V 2%nat) + 72)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) 271744
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 72) (Z.lor (Z.land (V 37%nat) 253) ((2 * ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)) mod 2 ^ 64))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 200) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 1
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 480) 8
        /\ L5.defined M' ((V 2%nat) - 416) 32
        /\ L5.defined M' ((V 2%nat) - 304) 104
        /\ L5.defined M' ((V 2%nat) - 199) 7
        /\ L5.defined M' ((V 2%nat) - 167) 7
        /\ L5.defined M' ((V 2%nat) - 135) 7
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 8) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 96) (V 38%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_170 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsDivA1 := BndP_Ns_077.LibSegNs_tsDivA1.
Definition KS_tsDivA1 : list nat := Eval vm_compute in (BG.kept_list 64 PtsDivA1.regs0 PtsDivA1.regs_out0).
Lemma KS_tsDivA1_ok : BG.kept_ok 64 PtsDivA1.regs0 PtsDivA1.regs_out0 KS_tsDivA1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_171 ())). Qed.
Lemma tsDivA1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) + 72) -> getr R (reg 11) = Z_to_bv 64 ((V 2%nat) + 8) -> getr R (reg 12) = Z_to_bv 64 ((V 2%nat) + 72) -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) + 40) -> getr R (reg 14) = Z_to_bv 64 1 ->
  140735332483552 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 480) 480 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 480) 480 -> L5.writable RSEGS M ((V 2%nat) + 8) 96 -> L5.u8_at RSEGS M ((V 2%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 16) 1 ->
  L5.u64_at RSEGS M ((V 2%nat) + 24) 10000000000000000000 -> L5.u64_at RSEGS M ((V 2%nat) + 32) 0 -> L5.u8_at RSEGS M ((V 2%nat) + 40) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 48) 1 ->
  L5.u64_at RSEGS M ((V 2%nat) + 56) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 64) 0 -> L5.u8_at RSEGS M ((V 2%nat) + 72) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 80) 1 ->
  L5.u64_at RSEGS M ((V 2%nat) + 88) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 96) (V 38%nat) -> 0 <= (V 37%nat) <= 255 -> Z.testbit (V 37%nat) 0 = false ->
  1 <= (V 36%nat) <= 9999999999999999999 -> 0 <= (V 43%nat) <= 255 -> Z.testbit (V 43%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 480) <= bv_unsigned a < ((V 2%nat) - 480) + 480) -> ~ (((V 2%nat) + 8) <= bv_unsigned a < ((V 2%nat) + 8) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 480) <= i < ((V 2%nat) - 480) + 480) -> ~ (((V 2%nat) + 8) <= i < ((V 2%nat) + 8) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42450 M) (st fx' R' 0x42a18 M')
        /\ (forall x, In x KS_tsDivA1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 40) (Z.lor (Z.land (V 43%nat) 253) (Z.land (V 37%nat) 2))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 56) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 48) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 472) ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 456) ((V 2%nat) - 168)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 448) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 440) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 432) ((V 2%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 424) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 384) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 376) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 368) ((V 2%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 360) 275408
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 352) ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 344) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) ((V 2%nat) + 72)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) ((V 2%nat) + 72)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) 271744
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 72) (Z.lor (Z.land (V 37%nat) 253) ((2 * ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)) mod 2 ^ 64))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 200) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 1
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 480) 8
        /\ L5.defined M' ((V 2%nat) - 416) 32
        /\ L5.defined M' ((V 2%nat) - 304) 104
        /\ L5.defined M' ((V 2%nat) - 199) 7
        /\ L5.defined M' ((V 2%nat) - 167) 7
        /\ L5.defined M' ((V 2%nat) - 135) 7
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 8) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 64) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 96) (V 38%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_172 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsDivBa := BndP_Ns_077.LibSegNs_tsDivBa.
Definition KS_tsDivBa_0 : list nat := Eval vm_compute in (BG.kept_list 64 PtsDivBa.regs0 PtsDivBa.regs_out0).
Lemma KS_tsDivBa_0_ok : BG.kept_ok 64 PtsDivBa.regs0 PtsDivBa.regs_out0 KS_tsDivBa_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_173 ())). Qed.
Definition KS_tsDivBa_1 : list nat := Eval vm_compute in (BG.kept_list 64 PtsDivBa.regs0 PtsDivBa.regs_out1).
Lemma KS_tsDivBa_1_ok : BG.kept_ok 64 PtsDivBa.regs0 PtsDivBa.regs_out1 KS_tsDivBa_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_174 ())). Qed.
Lemma tsDivBa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) + 72) -> getr R (reg 11) = Z_to_bv 64 ((V 2%nat) + 8) -> getr R (reg 12) = Z_to_bv 64 ((V 2%nat) + 72) -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) + 40) -> getr R (reg 14) = Z_to_bv 64 1 ->
  140735332483552 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 480) 480 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 480) 480 -> L5.writable RSEGS M ((V 2%nat) + 8) 96 -> L5.u8_at RSEGS M ((V 2%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 16) 1 ->
  L5.u64_at RSEGS M ((V 2%nat) + 24) 10000000000000000000 -> L5.u64_at RSEGS M ((V 2%nat) + 32) 0 -> L5.u8_at RSEGS M ((V 2%nat) + 40) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 48) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) + 56) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 64) 0 -> L5.u8_at RSEGS M ((V 2%nat) + 72) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 80) 1 ->
  L5.u64_at RSEGS M ((V 2%nat) + 88) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 96) (V 38%nat) -> 0 <= (V 37%nat) <= 255 -> Z.testbit (V 37%nat) 0 = false ->
  10000000000000000001 <= (V 36%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 480) <= bv_unsigned a < ((V 2%nat) - 480) + 480) -> ~ (((V 2%nat) + 8) <= bv_unsigned a < ((V 2%nat) + 8) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 480) <= i < ((V 2%nat) - 480) + 480) -> ~ (((V 2%nat) + 8) <= i < ((V 2%nat) + 8) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x42450 M) (st fx' R' 0x42a18 M')
        /\ (forall x, In x KS_tsDivBa_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 11)) = ((2 * ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 40) (Z.land (V 37%nat) 2)
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 72) (Z.lor (Z.land (V 37%nat) 253) ((2 * ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)) mod 2 ^ 64))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 56) (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 64) 0
        /\ 1 <= (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000) <= 9999999999999999999
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 48) (if 0 <? (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000) then 1 else 0)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 472) ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 464) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 456) ((V 2%nat) - 200)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 448) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 440) (if 0 <? (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000) then 1 else 0)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 432) ((V 2%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 424) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 384) (if 0 <? (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000) then 1 else 0)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 376) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 368) ((V 2%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 360) 275408
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 352) ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 344) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) ((V 2%nat) + 72)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) ((V 2%nat) + 72)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) 271924
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (if 0 <? (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000) then 1 else 0)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 200) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 88) (if 10000000000000000000 =? 0 then 2 ^ 64 - 1 else (V 36%nat) / 10000000000000000000)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 80) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 1
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 480) 8
        /\ L5.defined M' ((V 2%nat) - 416) 32
        /\ L5.defined M' ((V 2%nat) - 304) 48
        /\ L5.defined M' ((V 2%nat) - 248) 48
        /\ L5.defined M' ((V 2%nat) - 199) 7
        /\ L5.defined M' ((V 2%nat) - 167) 7
        /\ L5.defined M' ((V 2%nat) - 135) 7
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 8) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 96) (V 38%nat))
      \/ (msteps RSEGS (st fx R 0x42450 M) (st fx' R' 0x42a18 M')
        /\ (forall x, In x KS_tsDivBa_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 11)) = ((2 * ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)) mod 2 ^ 64)
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 40) (Z.land (V 37%nat) 2)
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 72) (Z.lor (Z.land (V 37%nat) 253) ((2 * ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)) mod 2 ^ 64))
        /\ 0 <= (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000) <= 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 48) (if 0 <? (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000) then 1 else 0)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 472) ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 464) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 456) ((V 2%nat) - 200)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 448) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 440) (if 0 <? (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000) then 1 else 0)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 432) ((V 2%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 424) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 384) (if 0 <? (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000) then 1 else 0)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 376) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 368) ((V 2%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 360) 275408
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 352) ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 344) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) ((V 2%nat) + 72)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) ((V 2%nat) + 72)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) 271924
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (if 0 <? (if 10000000000000000000 =? 0 then (V 36%nat) else (V 36%nat) mod 10000000000000000000) then 1 else 0)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 200) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 88) (if 10000000000000000000 =? 0 then 2 ^ 64 - 1 else (V 36%nat) / 10000000000000000000)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 80) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 1
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 480) 8
        /\ L5.defined M' ((V 2%nat) - 416) 32
        /\ L5.defined M' ((V 2%nat) - 304) 48
        /\ L5.defined M' ((V 2%nat) - 248) 48
        /\ L5.defined M' ((V 2%nat) - 199) 7
        /\ L5.defined M' ((V 2%nat) - 167) 7
        /\ L5.defined M' ((V 2%nat) - 135) 7
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 8) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 56) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 64) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 96) (V 38%nat))).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0197 ()) [] (Mh_0197_blobs1.kr_b_175 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsDivBb := BndP_Ns_077.LibSegNs_tsDivBb.
Definition KS_tsDivBb : list nat := Eval vm_compute in (BG.kept_list 64 PtsDivBb.regs0 PtsDivBb.regs_out0).
Lemma KS_tsDivBb_ok : BG.kept_ok 64 PtsDivBb.regs0 PtsDivBb.regs_out0 KS_tsDivBb = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_176 ())). Qed.
Lemma tsDivBb_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) + 72) -> getr R (reg 11) = Z_to_bv 64 ((V 2%nat) + 8) -> getr R (reg 12) = Z_to_bv 64 ((V 2%nat) + 72) -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) + 40) -> getr R (reg 14) = Z_to_bv 64 1 ->
  140735332483552 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 480) 480 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 480) 480 -> L5.writable RSEGS M ((V 2%nat) + 8) 96 -> L5.u8_at RSEGS M ((V 2%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 16) 1 ->
  L5.u64_at RSEGS M ((V 2%nat) + 24) 10000000000000000000 -> L5.u64_at RSEGS M ((V 2%nat) + 32) 0 -> L5.u8_at RSEGS M ((V 2%nat) + 40) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 48) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) + 56) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 64) 0 -> L5.u8_at RSEGS M ((V 2%nat) + 72) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 80) 1 ->
  L5.u64_at RSEGS M ((V 2%nat) + 88) 10000000000000000000 -> L5.u64_at RSEGS M ((V 2%nat) + 96) (V 38%nat) -> 0 <= (V 37%nat) <= 255 -> Z.testbit (V 37%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 480) <= bv_unsigned a < ((V 2%nat) - 480) + 480) -> ~ (((V 2%nat) + 8) <= bv_unsigned a < ((V 2%nat) + 8) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 480) <= i < ((V 2%nat) - 480) + 480) -> ~ (((V 2%nat) + 8) <= i < ((V 2%nat) + 8) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42450 M) (st fx' R' 0x42a18 M')
        /\ (forall x, In x KS_tsDivBb -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 11)) = ((2 * ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)) mod 2 ^ 64)
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 40) (Z.land (V 37%nat) 2)
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 72) (Z.lor (Z.land (V 37%nat) 253) ((2 * ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)) mod 2 ^ 64))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 48) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 472) ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 464) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 456) ((V 2%nat) - 200)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 448) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 440) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 432) ((V 2%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 424) 275552
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 384) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 376) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 368) ((V 2%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 360) 275408
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 352) ((V 2%nat) - 120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 344) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 336) ((V 2%nat) + 72)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 328) ((V 2%nat) + 72)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 320) ((Z.lxor 0 (Z.land (V 37%nat) 2)) / 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) 271924
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 200) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 88) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 80) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 1
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 480) 8
        /\ L5.defined M' ((V 2%nat) - 416) 32
        /\ L5.defined M' ((V 2%nat) - 304) 48
        /\ L5.defined M' ((V 2%nat) - 248) 48
        /\ L5.defined M' ((V 2%nat) - 199) 7
        /\ L5.defined M' ((V 2%nat) - 167) 7
        /\ L5.defined M' ((V 2%nat) - 135) 7
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 8) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 56) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 64) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 96) (V 38%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsDivP ()) [] (Mh_0197_blobs1.kr_b_177 ())). Qed.
(* [comment removed for export] *)

End PQTSDP.

End PnTsDivP.
Module PnTsWsP.
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsWsP () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z;lxor_nonnegK46Stdlib9micromega5Tauto8GFormula09C56Stdlib6ZArith6BinInt1Z9log2_lxorC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0S9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP8KS_tsW0SC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0S<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP9land_le_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z:mul_div_leC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP@defined_of_KUnkaC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0S6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0S3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0S3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP;KS_tsW0S_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0L9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP8KS_tsW0LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0L<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=word_of_zpolyC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0L6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW0L3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP;KS_tsW0L_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1S9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP8KS_tsW1SC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1S<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1S6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1S3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1S3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP;KS_tsW1S_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1L9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP8KS_tsW1LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1L<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1L6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW1L3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP;KS_tsW1L_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP7KS_tsW2C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsW2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP7KS_tsW3C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW36cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsW33ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsW3_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4a9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP8KS_tsW4aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4a<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4a3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP;KS_tsW4a_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4b9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP8KS_tsW4bC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4b<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW4b3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP;KS_tsW4b_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsW6a_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsW6a_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsW6a_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a<seg_sound_axC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapK69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00K59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=KS_tsW6a_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop04K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=KS_tsW6a_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6a3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=KS_tsW6a_2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsW6b_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsW6b_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsW6b9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsW6b_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWsg5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWsg9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsWsg_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWsg9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsWsg_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWsg<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWsg3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWsg2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWsg3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWsg3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWsg3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWsg6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWsg3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=KS_tsWsg_0_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=KS_tsWsg_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsWr0_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr09regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsWr0_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr03ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr03ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr03kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=KS_tsWr0_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr06cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=KS_tsWr0_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsWr1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsWr1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr13ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr13ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=KS_tsWr1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP6PtsWr16cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP=KS_tsWr1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsWt5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsWt9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP7KS_tsWtC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsWt<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsWt3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsWt2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsWt3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsWt3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP5PtsWt3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01977PnTsWsP6PQTSWP:KS_tsWt_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQTSWP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_178 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_179 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_180 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_181 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_182 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_183 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_184 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_185 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_186 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_187 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_188 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_189 ())). Qed.
(* [comment removed for export] *)
Lemma lxor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_190 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lxor _ _ < 256 => apply lxor_byte; byte_go
  | |- 0 <= ?x mod 18446744073709551616 < 256 => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia); byte_go
  | |- 0 <= ?x mod 2 ^ 64 < 256 => rewrite (Z.mod_small x (2 ^ 64)) by (zfacts; lia); byte_go
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; rewrite ?Z.lxor_0_l, ?Z.lxor_0_r, ?Z.lor_0_l, ?Z.lor_0_r; byte_go.
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
Module PtsW0S := BndP_Ns_078.LibSegNs_tsW0S.
Definition KS_tsW0S : list nat := Eval vm_compute in (BG.kept_list 80 PtsW0S.regs0 PtsW0S.regs_out0).
Lemma KS_tsW0S_ok : BG.kept_ok 80 PtsW0S.regs0 PtsW0S.regs_out0 KS_tsW0S = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_191 ())). Qed.
Lemma tsW0S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 45%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) 0 -> L5.u64_at RSEGS M (V 45%nat) (V 49%nat) -> Z.testbit (V 49%nat) 0 = false ->
  0 <= Z.land (V 49%nat) 255 <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 672) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 672) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46c40 M) (st fx' R' 0x46e88 M')
        /\ (forall x, In x KS_tsW0S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 48
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (V 37%nat) 2)
        /\ L5.u8_at RSEGS M' ((V 45%nat) + 2) 0
        /\ L5.u8_at RSEGS M' ((V 45%nat) + 1) 48
        /\ L5.u8_at RSEGS M' (V 45%nat) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290228
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 120) ((((4 * ((V 50%nat) / 4)) mod 2 ^ 64) + (Z.land (V 37%nat) 2)) mod 2 ^ 64)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 72
        /\ L5.defined M' ((V 2%nat) - 119) 7).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_192 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsW0L := BndP_Ns_078.LibSegNs_tsW0L.
Definition KS_tsW0L : list nat := Eval vm_compute in (BG.kept_list 80 PtsW0L.regs0 PtsW0L.regs_out0).
Lemma KS_tsW0L_ok : BG.kept_ok 80 PtsW0L.regs0 PtsW0L.regs_out0 KS_tsW0L = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_193 ())). Qed.
Lemma tsW0L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 45%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true ->
  L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 27 <= (V 46%nat) <= 268435457 ->
  25 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 -> L5.writable RSEGS M (V 47%nat) 26 -> L5.defined M (V 47%nat) 26 ->
  ((V 47%nat) + 26 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 26 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 26 <= ((V 2%nat) - 672)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 672) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 672) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46c40 M) (st fx' R' 0x46e88 M')
        /\ (forall x, In x KS_tsW0L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (V 37%nat) 2)
        /\ L5.u8_at RSEGS M' ((V 47%nat) + 1) 0
        /\ L5.u8_at RSEGS M' (V 47%nat) 48
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290228
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 120) ((((4 * ((V 50%nat) / 4)) mod 2 ^ 64) + (Z.land (V 37%nat) 2)) mod 2 ^ 64)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 72
        /\ L5.defined M' ((V 2%nat) - 119) 7
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat)
        /\ L5.defined M' ((V 47%nat) + 2) 24).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_194 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsW1S := BndP_Ns_078.LibSegNs_tsW1S.
Definition KS_tsW1S : list nat := Eval vm_compute in (BG.kept_list 80 PtsW1S.regs0 PtsW1S.regs_out0).
Lemma KS_tsW1S_ok : BG.kept_ok 80 PtsW1S.regs0 PtsW1S.regs_out0 KS_tsW1S = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_195 ())). Qed.
Lemma tsW1S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 45%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) 0 -> L5.u64_at RSEGS M (V 45%nat) (V 49%nat) -> Z.testbit (V 49%nat) 0 = false ->
  0 <= Z.land (V 49%nat) 255 <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 672) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 672) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46c40 M) (st fx' R' 0xbe8b0 M')
        /\ (forall x, In x KS_tsW1S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 418016
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 272)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 25
        /\ getr R' (reg 10) = Z_to_bv 64 26
        /\ bv_unsigned (getr R' (reg 11)) = ((72057594037927936 * (V 49%nat)) mod 2 ^ 64)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 22
        /\ getr R' (reg 18) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 26
        /\ bv_unsigned (getr R' (reg 20)) = (((72057594037927936 * (V 49%nat)) mod 2 ^ 64) / 144115188075855872)
        /\ getr R' (reg 21) = Z_to_bv 64 22
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 ((2 * ((V 49%nat) / 2)) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 289960
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 120) ((((4 * ((V 50%nat) / 4)) mod 2 ^ 64) + (Z.land (V 37%nat) 2)) mod 2 ^ 64)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 672) 408
        /\ L5.defined M' ((V 2%nat) - 192) 72
        /\ L5.defined M' ((V 2%nat) - 119) 7).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_196 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsW1L := BndP_Ns_078.LibSegNs_tsW1L.
Definition KS_tsW1L : list nat := Eval vm_compute in (BG.kept_list 80 PtsW1L.regs0 PtsW1L.regs_out0).
Lemma KS_tsW1L_ok : BG.kept_ok 80 PtsW1L.regs0 PtsW1L.regs_out0 KS_tsW1L = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_197 ())). Qed.
Lemma tsW1L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 45%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true ->
  L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 27 <= (V 46%nat) <= 268435457 ->
  25 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 -> L5.writable RSEGS M (V 47%nat) 26 -> L5.defined M (V 47%nat) 26 ->
  ((V 47%nat) + 26 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 26 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 26 <= ((V 2%nat) - 672)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 672) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 672) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46c40 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_tsW1L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 19) = Z_to_bv 64 10
        /\ getr R' (reg 20) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 21) = Z_to_bv 64 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 152) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 120) ((((4 * ((V 50%nat) / 4)) mod 2 ^ 64) + (Z.land (V 37%nat) 2)) mod 2 ^ 64)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 672) 488
        /\ L5.defined M' ((V 2%nat) - 183) 7
        /\ L5.defined M' ((V 2%nat) - 151) 7
        /\ L5.defined M' ((V 2%nat) - 119) 7).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_198 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsW2 := BndP_Ns_078.LibSegNs_tsW2.
Definition KS_tsW2 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW2.regs0 PtsW2.regs_out0).
Lemma KS_tsW2_ok : BG.kept_ok 80 PtsW2.regs0 PtsW2.regs_out0 KS_tsW2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_199 ())). Qed.
Lemma tsW2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 272) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 25 -> getr R (reg 10) = Z_to_bv 64 (V 48%nat) -> getr R (reg 19) = Z_to_bv 64 26 -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 22 -> getr R (reg 22) = Z_to_bv 64 0 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> 4096 <= (V 48%nat) <= 140737487306752 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x660e0 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_tsW2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 418144
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 45%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 45%nat) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_200 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsW3 := BndP_Ns_078.LibSegNs_tsW3.
Definition KS_tsW3 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW3.regs0 PtsW3.regs_out0).
Lemma KS_tsW3_ok : BG.kept_ok 80 PtsW3.regs0 PtsW3.regs_out0 KS_tsW3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_201 ())). Qed.
Lemma tsW3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 272) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 25 -> getr R (reg 18) = Z_to_bv 64 (V 48%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 45%nat) + 1) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 22 -> getr R (reg 22) = Z_to_bv 64 0 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) ->
  L5.writable RSEGS M (V 45%nat) 24 -> 4096 <= (V 48%nat) <= 140737487306752 -> L5.u64_at RSEGS M ((V 2%nat) - 200) 289960 -> L5.u64_at RSEGS M ((V 2%nat) - 208) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 240) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 248) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 256) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 264) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 2%nat) - 184) <= bv_unsigned a < ((V 2%nat) - 184) + 64) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 2%nat) - 184) <= i < ((V 2%nat) - 184) + 64) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x66160 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_tsW3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 19) = Z_to_bv 64 10
        /\ getr R' (reg 20) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 21) = Z_to_bv 64 18
        /\ getr R' (reg 22) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 152) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) 0
        /\ L5.u64_at RSEGS M' (V 45%nat) 27
        /\ L5.defined M' ((V 2%nat) - 672) 488
        /\ L5.defined M' ((V 2%nat) - 183) 7
        /\ L5.defined M' ((V 2%nat) - 151) 7
        /\ L5.defined M' ((V 2%nat) - 120) 120
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 289960
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (V 71%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 73%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) (V 74%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_202 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsW4a := BndP_Ns_078.LibSegNs_tsW4a.
Definition KS_tsW4a : list nat := Eval vm_compute in (BG.kept_list 80 PtsW4a.regs0 PtsW4a.regs_out0).
Lemma KS_tsW4a_ok : BG.kept_ok 80 PtsW4a.regs0 PtsW4a.regs_out0 KS_tsW4a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_203 ())). Qed.
Lemma tsW4a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 1 -> L5.u8_at RSEGS M ((V 2%nat) - 152) (V 58%nat) -> 0 <= (V 58%nat) <= 255 ->
  Z.testbit (V 58%nat) 0 = false -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 52%nat) -> 0 <= (V 52%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46d04 M) (st fx' R' 0x46d38 M')
        /\ (forall x, In x KS_tsW4a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((-1) * (V 52%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_204 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsW4b := BndP_Ns_079.LibSegNs_tsW4b.
Definition KS_tsW4b : list nat := Eval vm_compute in (BG.kept_list 80 PtsW4b.regs0 PtsW4b.regs_out0).
Lemma KS_tsW4b_ok : BG.kept_ok 80 PtsW4b.regs0 PtsW4b.regs_out0 KS_tsW4b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_205 ())). Qed.
Lemma tsW4b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 0 -> L5.u8_at RSEGS M ((V 2%nat) - 152) (V 58%nat) -> 0 <= (V 58%nat) <= 255 ->
  Z.testbit (V 58%nat) 0 = false -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 52%nat) -> 0 <= (V 52%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46d04 M) (st fx' R' 0x46d38 M')
        /\ (forall x, In x KS_tsW4b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((-1) * (V 52%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_206 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsW6a := BndP_Ns_079.LibSegNs_tsW6a.
Definition KS_tsW6a_0 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6a.regs0 PtsW6a.regs_out0).
Lemma KS_tsW6a_0_ok : BG.kept_ok 80 PtsW6a.regs0 PtsW6a.regs_out0 KS_tsW6a_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_207 ())). Qed.
Definition KS_tsW6a_1 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6a.regs0 PtsW6a.regs_out1).
Lemma KS_tsW6a_1_ok : BG.kept_ok 80 PtsW6a.regs0 PtsW6a.regs_out1 KS_tsW6a_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_208 ())). Qed.
Definition KS_tsW6a_2 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6a.regs0 PtsW6a.regs_out2).
Lemma KS_tsW6a_2_ok : BG.kept_ok 80 PtsW6a.regs0 PtsW6a.regs_out2 KS_tsW6a_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_209 ())). Qed.
Lemma tsW6a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 -> getr R (reg 22) = Z_to_bv 64 (V 51%nat) -> getr R (reg 23) = Z_to_bv 64 0 -> getr R (reg 24) = Z_to_bv 64 0 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true ->
  L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 27 <= (V 46%nat) <= 268435457 ->
  25 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 -> L5.writable RSEGS M (V 47%nat) 26 -> L5.defined M (V 47%nat) 26 ->
  ((V 47%nat) + 26 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 26 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 26 <= ((V 2%nat) - 672)) -> 0 <= (V 53%nat) <= 20 ->
  L5.writable RSEGS M ((V 47%nat) + (V 53%nat)) 2 -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 47%nat) + (V 53%nat))) -> (((V 2%nat) - 672) + 672 <= ((V 47%nat) + (V 53%nat)) \/ ((V 47%nat) + (V 53%nat)) + 2 <= ((V 2%nat) - 672)) -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 47%nat) + (V 53%nat))) ->
  0 <= (V 54%nat) <= 18 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= bv_unsigned a < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= i < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x46d38 M')
        /\ (forall x, In x KS_tsW6a_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 54%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ (V 54%nat) < 18
        /\ 1 <= ((((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8) - 0) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x46d70 M')
        /\ (forall x, In x KS_tsW6a_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + (V 53%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ ((((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8) - 0) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x46d70 M')
        /\ (forall x, In x KS_tsW6a_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 54%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ 18 <= (V 54%nat)
        /\ 1 <= ((((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8) - 0) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_210 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsW6b := BndP_Ns_079.LibSegNs_tsW6b.
Definition KS_tsW6b_0 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6b.regs0 PtsW6b.regs_out0).
Lemma KS_tsW6b_0_ok : BG.kept_ok 80 PtsW6b.regs0 PtsW6b.regs_out0 KS_tsW6b_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_211 ())). Qed.
Definition KS_tsW6b_1 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6b.regs0 PtsW6b.regs_out1).
Lemma KS_tsW6b_1_ok : BG.kept_ok 80 PtsW6b.regs0 PtsW6b.regs_out1 KS_tsW6b_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_212 ())). Qed.
Definition KS_tsW6b_2 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6b.regs0 PtsW6b.regs_out2).
Lemma KS_tsW6b_2_ok : BG.kept_ok 80 PtsW6b.regs0 PtsW6b.regs_out2 KS_tsW6b_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_213 ())). Qed.
Lemma tsW6b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 -> getr R (reg 22) = Z_to_bv 64 (V 51%nat) -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 24) = Z_to_bv 64 (-1) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true ->
  L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 27 <= (V 46%nat) <= 268435457 ->
  25 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 -> L5.writable RSEGS M (V 47%nat) 26 -> L5.defined M (V 47%nat) 26 ->
  ((V 47%nat) + 26 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 26 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 26 <= ((V 2%nat) - 672)) -> 0 <= (V 53%nat) <= 20 ->
  L5.writable RSEGS M ((V 47%nat) + (V 53%nat)) 2 -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 47%nat) + (V 53%nat))) -> (((V 2%nat) - 672) + 672 <= ((V 47%nat) + (V 53%nat)) \/ ((V 47%nat) + (V 53%nat)) + 2 <= ((V 2%nat) - 672)) -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 47%nat) + (V 53%nat))) ->
  0 <= (V 54%nat) <= 18 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= bv_unsigned a < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= i < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x46d38 M')
        /\ (forall x, In x KS_tsW6b_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 54%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ (V 54%nat) < 18
        /\ 1 <= ((((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8) - 18446744073709551615) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_tsW6b_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ ((((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8) - 18446744073709551615) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_tsW6b_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ 18 <= (V 54%nat)
        /\ 1 <= ((((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8) - 18446744073709551615) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0197 ()) [] (Mh_0197_blobs1.kr_b_214 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsWsg := BndP_Ns_079.LibSegNs_tsWsg.
Definition KS_tsWsg_0 : list nat := Eval vm_compute in (BG.kept_list 80 PtsWsg.regs0 PtsWsg.regs_out0).
Lemma KS_tsWsg_0_ok : BG.kept_ok 80 PtsWsg.regs0 PtsWsg.regs_out0 KS_tsWsg_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_215 ())). Qed.
Definition KS_tsWsg_1 : list nat := Eval vm_compute in (BG.kept_list 80 PtsWsg.regs0 PtsWsg.regs_out1).
Lemma KS_tsWsg_1_ok : BG.kept_ok 80 PtsWsg.regs0 PtsWsg.regs_out1 KS_tsWsg_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_216 ())). Qed.
Lemma tsWsg_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true ->
  L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 27 <= (V 46%nat) <= 268435457 ->
  25 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 -> L5.writable RSEGS M (V 47%nat) 26 -> L5.defined M (V 47%nat) 26 ->
  ((V 47%nat) + 26 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 26 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 26 <= ((V 2%nat) - 672)) -> 0 <= (V 53%nat) <= 20 ->
  L5.writable RSEGS M ((V 47%nat) + (V 53%nat)) 2 -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 47%nat) + (V 53%nat))) -> (((V 2%nat) - 672) + 672 <= ((V 47%nat) + (V 53%nat)) \/ ((V 47%nat) + (V 53%nat)) + 2 <= ((V 2%nat) - 672)) -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 47%nat) + (V 53%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= bv_unsigned a < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= i < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46d70 M) (st fx' R' 0x46d88 M')
        /\ (forall x, In x KS_tsWsg_0 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (Z.land (V 37%nat) 2)
        /\ (((Z.land (V 37%nat) 2) - 0) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d70 M) (st fx' R' 0x46d88 M')
        /\ (forall x, In x KS_tsWsg_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290184
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + (V 53%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) 45
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290184
        /\ 1 <= (((Z.land (V 37%nat) 2) - 0) mod 2 ^ 64)
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_217 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsWr0 := BndP_Ns_079.LibSegNs_tsWr0.
Definition KS_tsWr0_0 : list nat := Eval vm_compute in (BG.kept_list 80 PtsWr0.regs0 PtsWr0.regs_out0).
Lemma KS_tsWr0_0_ok : BG.kept_ok 80 PtsWr0.regs0 PtsWr0.regs_out0 KS_tsWr0_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_218 ())). Qed.
Definition KS_tsWr0_1 : list nat := Eval vm_compute in (BG.kept_list 80 PtsWr0.regs0 PtsWr0.regs_out1).
Lemma KS_tsWr0_1_ok : BG.kept_ok 80 PtsWr0.regs0 PtsWr0.regs_out1 KS_tsWr0_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_219 ())). Qed.
Lemma tsWr0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true ->
  L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 27 <= (V 46%nat) <= 268435457 ->
  25 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 -> L5.writable RSEGS M (V 47%nat) 26 -> L5.defined M (V 47%nat) 26 ->
  ((V 47%nat) + 26 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 26 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 26 <= ((V 2%nat) - 672)) -> 1 <= (V 53%nat) <= 21 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46d88 M) (st fx' R' 0x46dd8 M')
        /\ (forall x, In x KS_tsWr0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 47%nat) + (V 53%nat)) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ (V 47%nat) < (((((V 47%nat) + (V 53%nat)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x46d88 M) (st fx' R' 0x46df8 M')
        /\ (forall x, In x KS_tsWr0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 47%nat) + (V 53%nat)) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ (((((V 47%nat) + (V 53%nat)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64) <= (V 47%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_220 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsWr1 := BndP_Ns_079.LibSegNs_tsWr1.
Definition KS_tsWr1_0 : list nat := Eval vm_compute in (BG.kept_list 80 PtsWr1.regs0 PtsWr1.regs_out0).
Lemma KS_tsWr1_0_ok : BG.kept_ok 80 PtsWr1.regs0 PtsWr1.regs_out0 KS_tsWr1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_221 ())). Qed.
Definition KS_tsWr1_1 : list nat := Eval vm_compute in (BG.kept_list 80 PtsWr1.regs0 PtsWr1.regs_out1).
Lemma KS_tsWr1_1_ok : BG.kept_ok 80 PtsWr1.regs0 PtsWr1.regs_out1 KS_tsWr1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_222 ())). Qed.
Lemma tsWr1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> 4096 <= (V 55%nat) <= 140737487306752 -> 4096 <= (V 56%nat) <= 140737487306752 -> L5.defined M (V 56%nat) 1 ->
  L5.writable RSEGS M (V 56%nat) 1 -> L5.defined M ((V 55%nat) - 1) 1 -> L5.writable RSEGS M ((V 55%nat) - 1) 1 -> (((V 55%nat) - 1) + 1 <= (V 56%nat) \/ (V 56%nat) + 1 <= ((V 55%nat) - 1)) ->
  (((V 2%nat) - 672) + 672 <= ((V 55%nat) - 1) \/ ((V 55%nat) - 1) + 1 <= ((V 2%nat) - 672)) -> (((V 2%nat) - 672) + 672 <= (V 56%nat) \/ (V 56%nat) + 1 <= ((V 2%nat) - 672)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 55%nat) - 1) <= bv_unsigned a < ((V 55%nat) - 1) + 1) -> ~ (((V 56%nat) + 0) <= bv_unsigned a < ((V 56%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 55%nat) - 1) <= i < ((V 55%nat) - 1) + 1) -> ~ (((V 56%nat) + 0) <= i < ((V 56%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46dd8 M) (st fx' R' 0x46dd8 M')
        /\ (forall x, In x KS_tsWr1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 55%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 56%nat) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 55%nat)
        /\ (V 55%nat) < (((V 56%nat) + 18446744073709551615) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x46dd8 M) (st fx' R' 0x46df8 M')
        /\ (forall x, In x KS_tsWr1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 55%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 56%nat) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 55%nat)
        /\ (((V 56%nat) + 18446744073709551615) mod 2 ^ 64) <= (V 55%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_223 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsWt := BndP_Ns_079.LibSegNs_tsWt.
Definition KS_tsWt : list nat := Eval vm_compute in (BG.kept_list 80 PtsWt.regs0 PtsWt.regs_out0).
Lemma KS_tsWt_ok : BG.kept_ok 80 PtsWt.regs0 PtsWt.regs_out0 KS_tsWt = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_224 ())). Qed.
Lemma tsWt_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.u8_at RSEGS M ((V 2%nat) - 184) 0 -> L5.u8_at RSEGS M ((V 2%nat) - 152) (V 58%nat) -> 0 <= (V 58%nat) <= 255 -> Z.testbit (V 58%nat) 0 = false ->
  L5.u8_at RSEGS M ((V 2%nat) - 120) (V 57%nat) -> 0 <= (V 57%nat) <= 255 -> Z.testbit (V 57%nat) 0 = false -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 73%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46df8 M) (st fx' R' 0x46e88 M')
        /\ (forall x, In x KS_tsWt -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 73%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsP ()) [] (Mh_0197_blobs1.kr_b_225 ())). Qed.
(* [comment removed for export] *)

End PQTSWP.

End PnTsWsP.
Module PnTsWsPX.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsWsPX () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K5zpolyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;zpoly_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX6PtsW6A5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX6PtsW6A9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX8KS_tsW6AC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zpoly_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX6PtsW6A<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX6PtsW6A3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX6PtsW6A2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX6PtsW6A3NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX6PtsW6A3kn0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop04I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX6PtsW6A3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX;KS_tsW6A_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX;KS_tsW6aB_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX;KS_tsW6aB_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX;KS_tsW6aB_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapK69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InK59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00K59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX@defined_of_KUnkaC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX>KS_tsW6aB_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX>KS_tsW6aB_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6aB3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX>KS_tsW6aB_2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX;KS_tsW6bB_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX;KS_tsW6bB_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX;KS_tsW6bB_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX>KS_tsW6bB_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX>KS_tsW6bB_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsW6bB3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX>KS_tsW6bB_2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsWr1C5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsWr1C9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX;KS_tsWr1C_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsWr1C9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX;KS_tsWr1C_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsWr1C<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsWr1C3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsWr1C2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsWr1C3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsWr1C3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsWr1C3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsWr1C3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX>KS_tsWr1C_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX7PtsWr1C6cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01978PnTsWsPX7PQTSWPX>KS_tsWr1C_1_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQTSWPX.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_226 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_227 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_228 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_229 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_230 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_231 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_232 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_233 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_234 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_235 ())). Qed.
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
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5K.zpoly_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5K.zpoly]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5K.zpoly_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5K.zpoly]; pvz_unfold ZA; reflexivity | solve_modk k ].
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
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5K.zpoly]; pvz_unfold ZA; f_equal; clear; lia]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5K.zpoly]; pvz_unfold ZA; f_equal; clear; lia ].
(* [comment removed for export] *)
Module PtsW6A := BndP_Ns_079.LibSegNs_tsW6A.
Definition KS_tsW6A : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6A.regs0 PtsW6A.regs_out0).
Lemma KS_tsW6A_ok : BG.kept_ok 80 PtsW6A.regs0 PtsW6A.regs_out0 KS_tsW6A = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_236 ())). Qed.
Lemma tsW6A_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 -> getr R (reg 22) = Z_to_bv 64 (V 51%nat) -> getr R (reg 23) = Z_to_bv 64 (V 59%nat) -> getr R (reg 24) = Z_to_bv 64 (V 60%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true ->
  L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 27 <= (V 46%nat) <= 268435457 ->
  25 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 -> L5.writable RSEGS M (V 47%nat) 26 -> L5.defined M (V 47%nat) 26 ->
  ((V 47%nat) + 26 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 26 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 26 <= ((V 2%nat) - 672)) -> 0 <= (V 53%nat) <= 20 ->
  L5.writable RSEGS M ((V 47%nat) + (V 53%nat)) 2 -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 47%nat) + (V 53%nat))) -> (((V 2%nat) - 672) + 672 <= ((V 47%nat) + (V 53%nat)) \/ ((V 47%nat) + (V 53%nat)) + 2 <= ((V 2%nat) - 672)) -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 47%nat) + (V 53%nat))) ->
  0 <= (V 54%nat) <= 18 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x46d58 M')
        /\ (forall x, In x KS_tsW6A -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_AND (EAluw Instr.ALU_SUB (EVar 51) (EMd Instr.M_MUL (ELit 10) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EVar 51) (ELit 14757395258967641293)) (ELit 3)))) (ELit (-49))) (ELit 48))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_AND (EAluw Instr.ALU_SUB (EVar 51) (EMd Instr.M_MUL (ELit 10) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EVar 51) (ELit 14757395258967641293)) (ELit 3)))) (ELit (-49))) (ELit 48)) (ELit 255))
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_237 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsW6aB := BndP_Ns_079.LibSegNs_tsW6aB.
Definition KS_tsW6aB_0 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6aB.regs0 PtsW6aB.regs_out0).
Lemma KS_tsW6aB_0_ok : BG.kept_ok 80 PtsW6aB.regs0 PtsW6aB.regs_out0 KS_tsW6aB_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_238 ())). Qed.
Definition KS_tsW6aB_1 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6aB.regs0 PtsW6aB.regs_out1).
Lemma KS_tsW6aB_1_ok : BG.kept_ok 80 PtsW6aB.regs0 PtsW6aB.regs_out1 KS_tsW6aB_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_239 ())). Qed.
Definition KS_tsW6aB_2 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6aB.regs0 PtsW6aB.regs_out2).
Lemma KS_tsW6aB_2_ok : BG.kept_ok 80 PtsW6aB.regs0 PtsW6aB.regs_out2 KS_tsW6aB_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_240 ())). Qed.
Lemma tsW6aB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 56%nat) -> getr R (reg 11) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 -> getr R (reg 22) = Z_to_bv 64 (V 61%nat) -> getr R (reg 23) = Z_to_bv 64 0 -> getr R (reg 24) = Z_to_bv 64 0 -> getr R (reg 25) = Z_to_bv 64 (V 54%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true ->
  L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 27 <= (V 46%nat) <= 268435457 ->
  25 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 -> L5.writable RSEGS M (V 47%nat) 26 -> L5.defined M (V 47%nat) 26 ->
  ((V 47%nat) + 26 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 26 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 26 <= ((V 2%nat) - 672)) -> 0 <= (V 53%nat) <= 20 ->
  L5.writable RSEGS M ((V 47%nat) + (V 53%nat)) 2 -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 47%nat) + (V 53%nat))) -> (((V 2%nat) - 672) + 672 <= ((V 47%nat) + (V 53%nat)) \/ ((V 47%nat) + (V 53%nat)) + 2 <= ((V 2%nat) - 672)) -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 47%nat) + (V 53%nat))) ->
  0 <= (V 54%nat) <= 18 -> 48 <= (V 55%nat) <= 57 -> 0 <= (V 61%nat) <= 1844674407370955161 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= bv_unsigned a < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= i < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46d58 M) (st fx' R' 0x46d38 M')
        /\ (forall x, In x KS_tsW6aB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 54%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ (V 54%nat) < 18
        /\ 1 <= (((V 61%nat) - 0) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d58 M) (st fx' R' 0x46d70 M')
        /\ (forall x, In x KS_tsW6aB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + (V 53%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ (((V 61%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d58 M) (st fx' R' 0x46d70 M')
        /\ (forall x, In x KS_tsW6aB_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 54%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ 18 <= (V 54%nat)
        /\ 1 <= (((V 61%nat) - 0) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_241 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsW6bB := BndP_Ns_079.LibSegNs_tsW6bB.
Definition KS_tsW6bB_0 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6bB.regs0 PtsW6bB.regs_out0).
Lemma KS_tsW6bB_0_ok : BG.kept_ok 80 PtsW6bB.regs0 PtsW6bB.regs_out0 KS_tsW6bB_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_242 ())). Qed.
Definition KS_tsW6bB_1 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6bB.regs0 PtsW6bB.regs_out1).
Lemma KS_tsW6bB_1_ok : BG.kept_ok 80 PtsW6bB.regs0 PtsW6bB.regs_out1 KS_tsW6bB_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_243 ())). Qed.
Definition KS_tsW6bB_2 : list nat := Eval vm_compute in (BG.kept_list 80 PtsW6bB.regs0 PtsW6bB.regs_out2).
Lemma KS_tsW6bB_2_ok : BG.kept_ok 80 PtsW6bB.regs0 PtsW6bB.regs_out2 KS_tsW6bB_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_244 ())). Qed.
Lemma tsW6bB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 56%nat) -> getr R (reg 11) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 -> getr R (reg 22) = Z_to_bv 64 (V 61%nat) -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 24) = Z_to_bv 64 (-1) -> getr R (reg 25) = Z_to_bv 64 (V 54%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true ->
  L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 27 <= (V 46%nat) <= 268435457 ->
  25 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 -> L5.writable RSEGS M (V 47%nat) 26 -> L5.defined M (V 47%nat) 26 ->
  ((V 47%nat) + 26 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 26 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 26 <= ((V 2%nat) - 672)) -> 0 <= (V 53%nat) <= 20 ->
  L5.writable RSEGS M ((V 47%nat) + (V 53%nat)) 2 -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 47%nat) + (V 53%nat))) -> (((V 2%nat) - 672) + 672 <= ((V 47%nat) + (V 53%nat)) \/ ((V 47%nat) + (V 53%nat)) + 2 <= ((V 2%nat) - 672)) -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 47%nat) + (V 53%nat))) ->
  0 <= (V 54%nat) <= 18 -> 48 <= (V 55%nat) <= 57 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= bv_unsigned a < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= i < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46d58 M) (st fx' R' 0x46d38 M')
        /\ (forall x, In x KS_tsW6bB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 54%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ (V 54%nat) < 18
        /\ 1 <= (((V 61%nat) - 18446744073709551615) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d58 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_tsW6bB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ (((V 61%nat) - 18446744073709551615) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d58 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_tsW6bB_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ 18 <= (V 54%nat)
        /\ 1 <= (((V 61%nat) - 18446744073709551615) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_245 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsWr1C := BndP_Ns_079.LibSegNs_tsWr1C.
Definition KS_tsWr1C_0 : list nat := Eval vm_compute in (BG.kept_list 80 PtsWr1C.regs0 PtsWr1C.regs_out0).
Lemma KS_tsWr1C_0_ok : BG.kept_ok 80 PtsWr1C.regs0 PtsWr1C.regs_out0 KS_tsWr1C_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_246 ())). Qed.
Definition KS_tsWr1C_1 : list nat := Eval vm_compute in (BG.kept_list 80 PtsWr1C.regs0 PtsWr1C.regs_out1).
Lemma KS_tsWr1C_1_ok : BG.kept_ok 80 PtsWr1C.regs0 PtsWr1C.regs_out1 KS_tsWr1C_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_247 ())). Qed.
Lemma tsWr1C_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> 4096 <= (V 55%nat) <= 140737487306752 -> 4096 <= (V 56%nat) <= 140737487306752 -> L5.defined M (V 56%nat) 1 ->
  L5.writable RSEGS M (V 56%nat) 1 -> L5.defined M ((V 55%nat) - 1) 1 -> L5.writable RSEGS M ((V 55%nat) - 1) 1 -> (((V 55%nat) - 1) + 1 <= (V 56%nat) \/ (V 56%nat) + 1 <= ((V 55%nat) - 1)) ->
  (((V 2%nat) - 672) + 672 <= ((V 55%nat) - 1) \/ ((V 55%nat) - 1) + 1 <= ((V 2%nat) - 672)) -> (((V 2%nat) - 672) + 672 <= (V 56%nat) \/ (V 56%nat) + 1 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M ((V 55%nat) - 1) (V 57%nat) -> 0 <= (V 57%nat) <= 255 ->
  L5.u8_at RSEGS M (V 56%nat) (V 58%nat) -> 0 <= (V 58%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 55%nat) - 1) <= bv_unsigned a < ((V 55%nat) - 1) + 1) -> ~ (((V 56%nat) + 0) <= bv_unsigned a < ((V 56%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 55%nat) - 1) <= i < ((V 55%nat) - 1) + 1) -> ~ (((V 56%nat) + 0) <= i < ((V 56%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46dd8 M) (st fx' R' 0x46dd8 M')
        /\ (forall x, In x KS_tsWr1C_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 55%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 56%nat) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 57%nat)
        /\ (V 55%nat) < (((V 56%nat) + 18446744073709551615) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (V 56%nat) (V 57%nat)
        /\ L5.u8_at RSEGS M' ((V 55%nat) - 1) (V 58%nat))
      \/ (msteps RSEGS (st fx R 0x46dd8 M) (st fx' R' 0x46df8 M')
        /\ (forall x, In x KS_tsWr1C_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 55%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 56%nat) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 57%nat)
        /\ (((V 56%nat) + 18446744073709551615) mod 2 ^ 64) <= (V 55%nat)
        /\ L5.u8_at RSEGS M' (V 56%nat) (V 57%nat)
        /\ L5.u8_at RSEGS M' ((V 55%nat) - 1) (V 58%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWsPX ()) [] (Mh_0197_blobs1.kr_b_248 ())). Qed.
(* [comment removed for export] *)

End PQTSWPX.

End PnTsWsPX.
Module PnTsWs2LP.
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsWs2LP () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z;lxor_nonnegK46Stdlib9micromega5Tauto8GFormula09C56Stdlib6ZArith6BinInt1Z9log2_lxorC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4a9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP7KS_tw4aC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4a<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4a3NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4a3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4a3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP:KS_tw4a_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4b9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP7KS_tw4bC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4b<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw4b3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP:KS_tw4b_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_tw6a_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_tw6a_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6a9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_tw6a_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_tw6b_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_tw6b_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptw6b9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_tw6b_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwsg5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwsg9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_twsg_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwsg9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_twsg_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwsg<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InK59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP@defined_of_KUnkaC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwsg3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwsg2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwsg3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwsg3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwsg3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwsg6cells0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwsg3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP<KS_twsg_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP<KS_twsg_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_twr0_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr09regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_twr0_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr03ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr03ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr03kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP<KS_twr0_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr06cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP<KS_twr0_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_twr1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP9KS_twr1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr13ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr13ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP<KS_twr1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP5Ptwr16cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2LP8PQTSW2LP<KS_twr1_1_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQTSW2LP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_249 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_250 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_251 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_252 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_253 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_254 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_255 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_256 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_257 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_258 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_259 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_260 ())). Qed.
(* [comment removed for export] *)
Lemma lxor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_261 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lxor _ _ < 256 => apply lxor_byte; byte_go
  | |- 0 <= ?x mod 18446744073709551616 < 256 => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia); byte_go
  | |- 0 <= ?x mod 2 ^ 64 < 256 => rewrite (Z.mod_small x (2 ^ 64)) by (zfacts; lia); byte_go
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; rewrite ?Z.lxor_0_l, ?Z.lxor_0_r, ?Z.lor_0_l, ?Z.lor_0_r; byte_go.
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
Module Ptw4a := BndP_Ns_080.LibSegNs_tw4a.
Definition KS_tw4a : list nat := Eval vm_compute in (BG.kept_list 80 Ptw4a.regs0 Ptw4a.regs_out0).
Lemma KS_tw4a_ok : BG.kept_ok 80 Ptw4a.regs0 Ptw4a.regs_out0 KS_tw4a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_262 ())). Qed.
Lemma tw4a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 1 ->
  L5.u8_at RSEGS M ((V 2%nat) - 152) (V 58%nat) -> 0 <= (V 58%nat) <= 255 -> Z.testbit (V 58%nat) 0 = false -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 112) (V 52%nat) -> 0 <= (V 52%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46d04 M) (st fx' R' 0x46d38 M')
        /\ (forall x, In x KS_tw4a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((-1) * (V 52%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_263 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptw4b := BndP_Ns_080.LibSegNs_tw4b.
Definition KS_tw4b : list nat := Eval vm_compute in (BG.kept_list 80 Ptw4b.regs0 Ptw4b.regs_out0).
Lemma KS_tw4b_ok : BG.kept_ok 80 Ptw4b.regs0 Ptw4b.regs_out0 KS_tw4b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_264 ())). Qed.
Lemma tw4b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 0 ->
  L5.u8_at RSEGS M ((V 2%nat) - 152) (V 58%nat) -> 0 <= (V 58%nat) <= 255 -> Z.testbit (V 58%nat) 0 = false -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 52%nat) ->
  0 <= (V 52%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46d04 M) (st fx' R' 0x46d38 M')
        /\ (forall x, In x KS_tw4b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((-1) * (V 52%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_265 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptw6a := BndP_Ns_080.LibSegNs_tw6a.
Definition KS_tw6a_0 : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6a.regs0 Ptw6a.regs_out0).
Lemma KS_tw6a_0_ok : BG.kept_ok 80 Ptw6a.regs0 Ptw6a.regs_out0 KS_tw6a_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_266 ())). Qed.
Definition KS_tw6a_1 : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6a.regs0 Ptw6a.regs_out1).
Lemma KS_tw6a_1_ok : BG.kept_ok 80 Ptw6a.regs0 Ptw6a.regs_out1 KS_tw6a_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_267 ())). Qed.
Definition KS_tw6a_2 : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6a.regs0 Ptw6a.regs_out2).
Lemma KS_tw6a_2_ok : BG.kept_ok 80 Ptw6a.regs0 Ptw6a.regs_out2 KS_tw6a_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_268 ())). Qed.
Lemma tw6a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 -> getr R (reg 22) = Z_to_bv 64 (V 51%nat) -> getr R (reg 23) = Z_to_bv 64 0 -> getr R (reg 24) = Z_to_bv 64 0 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) ->
  0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true -> L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 47 <= (V 46%nat) <= 268435457 -> 45 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 ->
  L5.writable RSEGS M (V 47%nat) 32 -> L5.defined M (V 47%nat) 32 -> ((V 47%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) ->
  (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 32 <= ((V 2%nat) - 672)) -> 0 <= (V 53%nat) <= 30 -> L5.writable RSEGS M ((V 47%nat) + (V 53%nat)) 2 -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 47%nat) + (V 53%nat))) ->
  (((V 2%nat) - 672) + 672 <= ((V 47%nat) + (V 53%nat)) \/ ((V 47%nat) + (V 53%nat)) + 2 <= ((V 2%nat) - 672)) -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 47%nat) + (V 53%nat))) -> 0 <= (V 54%nat) <= 18 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= bv_unsigned a < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= i < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x46d38 M')
        /\ (forall x, In x KS_tw6a_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 54%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ (V 54%nat) < 18
        /\ 1 <= ((((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8) - 0) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x46d70 M')
        /\ (forall x, In x KS_tw6a_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + (V 53%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ ((((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8) - 0) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x46d70 M')
        /\ (forall x, In x KS_tw6a_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 54%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ 18 <= (V 54%nat)
        /\ 1 <= ((((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8) - 0) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0197 ()) [] (Mh_0197_blobs1.kr_b_269 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptw6b := BndP_Ns_080.LibSegNs_tw6b.
Definition KS_tw6b_0 : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6b.regs0 Ptw6b.regs_out0).
Lemma KS_tw6b_0_ok : BG.kept_ok 80 Ptw6b.regs0 Ptw6b.regs_out0 KS_tw6b_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_270 ())). Qed.
Definition KS_tw6b_1 : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6b.regs0 Ptw6b.regs_out1).
Lemma KS_tw6b_1_ok : BG.kept_ok 80 Ptw6b.regs0 Ptw6b.regs_out1 KS_tw6b_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_271 ())). Qed.
Definition KS_tw6b_2 : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6b.regs0 Ptw6b.regs_out2).
Lemma KS_tw6b_2_ok : BG.kept_ok 80 Ptw6b.regs0 Ptw6b.regs_out2 KS_tw6b_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_272 ())). Qed.
Lemma tw6b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 -> getr R (reg 22) = Z_to_bv 64 (V 51%nat) -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 24) = Z_to_bv 64 (-1) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) ->
  0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true -> L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 47 <= (V 46%nat) <= 268435457 -> 45 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 ->
  L5.writable RSEGS M (V 47%nat) 32 -> L5.defined M (V 47%nat) 32 -> ((V 47%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) ->
  (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 32 <= ((V 2%nat) - 672)) -> 0 <= (V 53%nat) <= 18 -> L5.writable RSEGS M ((V 47%nat) + (V 53%nat)) 2 -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 47%nat) + (V 53%nat))) ->
  (((V 2%nat) - 672) + 672 <= ((V 47%nat) + (V 53%nat)) \/ ((V 47%nat) + (V 53%nat)) + 2 <= ((V 2%nat) - 672)) -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 47%nat) + (V 53%nat))) -> 0 <= (V 54%nat) <= 18 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= bv_unsigned a < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= i < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x46d38 M')
        /\ (forall x, In x KS_tw6b_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 54%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ (V 54%nat) < 18
        /\ 1 <= ((((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8) - 18446744073709551615) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_tw6b_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ ((((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8) - 18446744073709551615) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_tw6b_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ 18 <= (V 54%nat)
        /\ 1 <= ((((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8) - 18446744073709551615) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0197 ()) [] (Mh_0197_blobs1.kr_b_273 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptwsg := BndP_Ns_082.LibSegNs_twsg.
Definition KS_twsg_0 : list nat := Eval vm_compute in (BG.kept_list 80 Ptwsg.regs0 Ptwsg.regs_out0).
Lemma KS_twsg_0_ok : BG.kept_ok 80 Ptwsg.regs0 Ptwsg.regs_out0 KS_twsg_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_274 ())). Qed.
Definition KS_twsg_1 : list nat := Eval vm_compute in (BG.kept_list 80 Ptwsg.regs0 Ptwsg.regs_out1).
Lemma KS_twsg_1_ok : BG.kept_ok 80 Ptwsg.regs0 Ptwsg.regs_out1 KS_twsg_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_275 ())). Qed.
Lemma twsg_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) ->
  0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true -> L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 47 <= (V 46%nat) <= 268435457 -> 45 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 ->
  L5.writable RSEGS M (V 47%nat) 32 -> L5.defined M (V 47%nat) 32 -> ((V 47%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) ->
  (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 32 <= ((V 2%nat) - 672)) -> 0 <= (V 53%nat) <= 30 -> L5.writable RSEGS M ((V 47%nat) + (V 53%nat)) 2 -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 47%nat) + (V 53%nat))) ->
  (((V 2%nat) - 672) + 672 <= ((V 47%nat) + (V 53%nat)) \/ ((V 47%nat) + (V 53%nat)) + 2 <= ((V 2%nat) - 672)) -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 47%nat) + (V 53%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= bv_unsigned a < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= i < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46d70 M) (st fx' R' 0x46d88 M')
        /\ (forall x, In x KS_twsg_0 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (Z.land (V 37%nat) 2)
        /\ (((Z.land (V 37%nat) 2) - 0) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d70 M) (st fx' R' 0x46d88 M')
        /\ (forall x, In x KS_twsg_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290184
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + (V 53%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) 45
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290184
        /\ 1 <= (((Z.land (V 37%nat) 2) - 0) mod 2 ^ 64)
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_276 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptwr0 := BndP_Ns_082.LibSegNs_twr0.
Definition KS_twr0_0 : list nat := Eval vm_compute in (BG.kept_list 80 Ptwr0.regs0 Ptwr0.regs_out0).
Lemma KS_twr0_0_ok : BG.kept_ok 80 Ptwr0.regs0 Ptwr0.regs_out0 KS_twr0_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_277 ())). Qed.
Definition KS_twr0_1 : list nat := Eval vm_compute in (BG.kept_list 80 Ptwr0.regs0 Ptwr0.regs_out1).
Lemma KS_twr0_1_ok : BG.kept_ok 80 Ptwr0.regs0 Ptwr0.regs_out1 KS_twr0_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_278 ())). Qed.
Lemma twr0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) ->
  0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true -> L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 47 <= (V 46%nat) <= 268435457 -> 45 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 ->
  L5.writable RSEGS M (V 47%nat) 32 -> L5.defined M (V 47%nat) 32 -> ((V 47%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) ->
  (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 32 <= ((V 2%nat) - 672)) -> 1 <= (V 53%nat) <= 31 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46d88 M) (st fx' R' 0x46dd8 M')
        /\ (forall x, In x KS_twr0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 47%nat) + (V 53%nat)) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ (V 47%nat) < (((((V 47%nat) + (V 53%nat)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x46d88 M) (st fx' R' 0x46df8 M')
        /\ (forall x, In x KS_twr0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 47%nat) + (V 53%nat)) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ (((((V 47%nat) + (V 53%nat)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64) <= (V 47%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_279 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptwr1 := BndP_Ns_082.LibSegNs_twr1.
Definition KS_twr1_0 : list nat := Eval vm_compute in (BG.kept_list 80 Ptwr1.regs0 Ptwr1.regs_out0).
Lemma KS_twr1_0_ok : BG.kept_ok 80 Ptwr1.regs0 Ptwr1.regs_out0 KS_twr1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_280 ())). Qed.
Definition KS_twr1_1 : list nat := Eval vm_compute in (BG.kept_list 80 Ptwr1.regs0 Ptwr1.regs_out1).
Lemma KS_twr1_1_ok : BG.kept_ok 80 Ptwr1.regs0 Ptwr1.regs_out1 KS_twr1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_281 ())). Qed.
Lemma twr1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> 4096 <= (V 55%nat) <= 140737487306752 ->
  4096 <= (V 56%nat) <= 140737487306752 -> L5.defined M (V 56%nat) 1 -> L5.writable RSEGS M (V 56%nat) 1 -> L5.defined M ((V 55%nat) - 1) 1 ->
  L5.writable RSEGS M ((V 55%nat) - 1) 1 -> (((V 55%nat) - 1) + 1 <= (V 56%nat) \/ (V 56%nat) + 1 <= ((V 55%nat) - 1)) -> (((V 2%nat) - 672) + 672 <= ((V 55%nat) - 1) \/ ((V 55%nat) - 1) + 1 <= ((V 2%nat) - 672)) -> (((V 2%nat) - 672) + 672 <= (V 56%nat) \/ (V 56%nat) + 1 <= ((V 2%nat) - 672)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 55%nat) - 1) <= bv_unsigned a < ((V 55%nat) - 1) + 1) -> ~ (((V 56%nat) + 0) <= bv_unsigned a < ((V 56%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 55%nat) - 1) <= i < ((V 55%nat) - 1) + 1) -> ~ (((V 56%nat) + 0) <= i < ((V 56%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46dd8 M) (st fx' R' 0x46dd8 M')
        /\ (forall x, In x KS_twr1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 55%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 56%nat) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 55%nat)
        /\ (V 55%nat) < (((V 56%nat) + 18446744073709551615) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x46dd8 M) (st fx' R' 0x46df8 M')
        /\ (forall x, In x KS_twr1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 55%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 56%nat) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 55%nat)
        /\ (((V 56%nat) + 18446744073709551615) mod 2 ^ 64) <= (V 55%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2LP ()) [] (Mh_0197_blobs1.kr_b_282 ())). Qed.
(* [comment removed for export] *)

End PQTSW2LP.

End PnTsWs2LP.
Module PnTsWs2PX.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsWs2PX () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K5zpolyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;zpoly_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX5Ptw6A5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX5Ptw6A9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX7KS_tw6AC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zpoly_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX5Ptw6A<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX5Ptw6A3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX5Ptw6A2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX5Ptw6A3NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX5Ptw6A3kn0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop04I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX5Ptw6A3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX:KS_tw6A_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX:KS_tw6aB_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX:KS_tw6aB_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX:KS_tw6aB_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapK69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InK59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00K59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX@defined_of_KUnkaC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX=KS_tw6aB_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX=KS_tw6aB_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6aB3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX=KS_tw6aB_2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX:KS_tw6bB_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX:KS_tw6bB_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX:KS_tw6bB_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX=KS_tw6bB_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX=KS_tw6bB_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptw6bB3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX=KS_tw6bB_2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptwr1C5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptwr1C9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX:KS_twr1C_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptwr1C9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX:KS_twr1C_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptwr1C<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptwr1C3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptwr1C2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptwr1C3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptwr1C3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptwr1C3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptwr1C3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX=KS_twr1C_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX6Ptwr1C6cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2PX8PQTSW2PX=KS_twr1C_1_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQTSW2PX.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_283 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_284 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_285 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_286 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_287 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_288 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_289 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_290 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_291 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_292 ())). Qed.
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
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5K.zpoly_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5K.zpoly]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5K.zpoly_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5K.zpoly]; pvz_unfold ZA; reflexivity | solve_modk k ].
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
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5K.zpoly]; pvz_unfold ZA; f_equal; clear; lia]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5K.zpoly]; pvz_unfold ZA; f_equal; clear; lia ].
(* [comment removed for export] *)
Module Ptw6A := BndP_Ns_080.LibSegNs_tw6A.
Definition KS_tw6A : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6A.regs0 Ptw6A.regs_out0).
Lemma KS_tw6A_ok : BG.kept_ok 80 Ptw6A.regs0 Ptw6A.regs_out0 KS_tw6A = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_293 ())). Qed.
Lemma tw6A_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 -> getr R (reg 22) = Z_to_bv 64 (V 51%nat) -> getr R (reg 23) = Z_to_bv 64 (V 59%nat) -> getr R (reg 24) = Z_to_bv 64 (V 60%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) ->
  0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true -> L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 47 <= (V 46%nat) <= 268435457 -> 45 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 ->
  L5.writable RSEGS M (V 47%nat) 32 -> L5.defined M (V 47%nat) 32 -> ((V 47%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) ->
  (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 32 <= ((V 2%nat) - 672)) -> 0 <= (V 53%nat) <= 30 -> L5.writable RSEGS M ((V 47%nat) + (V 53%nat)) 2 -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 47%nat) + (V 53%nat))) ->
  (((V 2%nat) - 672) + 672 <= ((V 47%nat) + (V 53%nat)) \/ ((V 47%nat) + (V 53%nat)) + 2 <= ((V 2%nat) - 672)) -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 47%nat) + (V 53%nat))) -> 0 <= (V 54%nat) <= 18 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46d38 M) (st fx' R' 0x46d58 M')
        /\ (forall x, In x KS_tw6A -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_AND (EAluw Instr.ALU_SUB (EVar 51) (EMd Instr.M_MUL (ELit 10) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EVar 51) (ELit 14757395258967641293)) (ELit 3)))) (ELit (-49))) (ELit 48))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_AND (EAluw Instr.ALU_SUB (EVar 51) (EMd Instr.M_MUL (ELit 10) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EVar 51) (ELit 14757395258967641293)) (ELit 3)))) (ELit (-49))) (ELit 48)) (ELit 255))
        /\ bv_unsigned (getr R' (reg 22)) = ((((V 51%nat) * 14757395258967641293) / 2 ^ 64) / 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_294 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptw6aB := BndP_Ns_080.LibSegNs_tw6aB.
Definition KS_tw6aB_0 : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6aB.regs0 Ptw6aB.regs_out0).
Lemma KS_tw6aB_0_ok : BG.kept_ok 80 Ptw6aB.regs0 Ptw6aB.regs_out0 KS_tw6aB_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_295 ())). Qed.
Definition KS_tw6aB_1 : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6aB.regs0 Ptw6aB.regs_out1).
Lemma KS_tw6aB_1_ok : BG.kept_ok 80 Ptw6aB.regs0 Ptw6aB.regs_out1 KS_tw6aB_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_296 ())). Qed.
Definition KS_tw6aB_2 : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6aB.regs0 Ptw6aB.regs_out2).
Lemma KS_tw6aB_2_ok : BG.kept_ok 80 Ptw6aB.regs0 Ptw6aB.regs_out2 KS_tw6aB_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_297 ())). Qed.
Lemma tw6aB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 56%nat) -> getr R (reg 11) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 -> getr R (reg 22) = Z_to_bv 64 (V 61%nat) -> getr R (reg 23) = Z_to_bv 64 0 -> getr R (reg 24) = Z_to_bv 64 0 -> getr R (reg 25) = Z_to_bv 64 (V 54%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) ->
  0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true -> L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 47 <= (V 46%nat) <= 268435457 -> 45 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 ->
  L5.writable RSEGS M (V 47%nat) 32 -> L5.defined M (V 47%nat) 32 -> ((V 47%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) ->
  (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 32 <= ((V 2%nat) - 672)) -> 0 <= (V 53%nat) <= 30 -> L5.writable RSEGS M ((V 47%nat) + (V 53%nat)) 2 -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 47%nat) + (V 53%nat))) ->
  (((V 2%nat) - 672) + 672 <= ((V 47%nat) + (V 53%nat)) \/ ((V 47%nat) + (V 53%nat)) + 2 <= ((V 2%nat) - 672)) -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 47%nat) + (V 53%nat))) -> 0 <= (V 54%nat) <= 18 -> 48 <= (V 55%nat) <= 57 ->
  0 <= (V 61%nat) <= 1844674407370955161 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= bv_unsigned a < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= i < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46d58 M) (st fx' R' 0x46d38 M')
        /\ (forall x, In x KS_tw6aB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 54%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ (V 54%nat) < 18
        /\ 1 <= (((V 61%nat) - 0) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d58 M) (st fx' R' 0x46d70 M')
        /\ (forall x, In x KS_tw6aB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + (V 53%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ (((V 61%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d58 M) (st fx' R' 0x46d70 M')
        /\ (forall x, In x KS_tw6aB_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 54%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ 18 <= (V 54%nat)
        /\ 1 <= (((V 61%nat) - 0) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_298 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptw6bB := BndP_Ns_080.LibSegNs_tw6bB.
Definition KS_tw6bB_0 : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6bB.regs0 Ptw6bB.regs_out0).
Lemma KS_tw6bB_0_ok : BG.kept_ok 80 Ptw6bB.regs0 Ptw6bB.regs_out0 KS_tw6bB_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_299 ())). Qed.
Definition KS_tw6bB_1 : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6bB.regs0 Ptw6bB.regs_out1).
Lemma KS_tw6bB_1_ok : BG.kept_ok 80 Ptw6bB.regs0 Ptw6bB.regs_out1 KS_tw6bB_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_300 ())). Qed.
Definition KS_tw6bB_2 : list nat := Eval vm_compute in (BG.kept_list 80 Ptw6bB.regs0 Ptw6bB.regs_out2).
Lemma KS_tw6bB_2_ok : BG.kept_ok 80 Ptw6bB.regs0 Ptw6bB.regs_out2 KS_tw6bB_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_301 ())). Qed.
Lemma tw6bB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 56%nat) -> getr R (reg 11) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 -> getr R (reg 22) = Z_to_bv 64 (V 61%nat) -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 24) = Z_to_bv 64 (-1) -> getr R (reg 25) = Z_to_bv 64 (V 54%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) ->
  0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true -> L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 47 <= (V 46%nat) <= 268435457 -> 45 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 ->
  L5.writable RSEGS M (V 47%nat) 32 -> L5.defined M (V 47%nat) 32 -> ((V 47%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) ->
  (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 32 <= ((V 2%nat) - 672)) -> 0 <= (V 53%nat) <= 18 -> L5.writable RSEGS M ((V 47%nat) + (V 53%nat)) 2 -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 47%nat) + (V 53%nat))) ->
  (((V 2%nat) - 672) + 672 <= ((V 47%nat) + (V 53%nat)) \/ ((V 47%nat) + (V 53%nat)) + 2 <= ((V 2%nat) - 672)) -> (((V 47%nat) + (V 53%nat)) + 2 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 47%nat) + (V 53%nat))) -> 0 <= (V 54%nat) <= 18 -> 48 <= (V 55%nat) <= 57 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= bv_unsigned a < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> ~ ((((V 47%nat) + (V 53%nat)) + 0) <= i < (((V 47%nat) + (V 53%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46d58 M) (st fx' R' 0x46d38 M')
        /\ (forall x, In x KS_tw6bB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 54%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 53%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 49%nat)
        /\ (V 54%nat) < 18
        /\ 1 <= (((V 61%nat) - 18446744073709551615) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d58 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_tw6bB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ (((V 61%nat) - 18446744073709551615) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))
      \/ (msteps RSEGS (st fx R 0x46d58 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_tw6bB_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ 18 <= (V 54%nat)
        /\ 1 <= (((V 61%nat) - 18446744073709551615) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (V 53%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((V 47%nat) + (V 53%nat)) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) ((V 53%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 14757395258967641293
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 2%nat) - 136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 290144
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 2%nat) - 192) 192
        /\ L5.u8_at RSEGS M' (V 45%nat) (V 49%nat)
        /\ L5.u64_at RSEGS M' (V 45%nat) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 47%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_302 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptwr1C := BndP_Ns_082.LibSegNs_twr1C.
Definition KS_twr1C_0 : list nat := Eval vm_compute in (BG.kept_list 80 Ptwr1C.regs0 Ptwr1C.regs_out0).
Lemma KS_twr1C_0_ok : BG.kept_ok 80 Ptwr1C.regs0 Ptwr1C.regs_out0 KS_twr1C_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_303 ())). Qed.
Definition KS_twr1C_1 : list nat := Eval vm_compute in (BG.kept_list 80 Ptwr1C.regs0 Ptwr1C.regs_out1).
Lemma KS_twr1C_1_ok : BG.kept_ok 80 Ptwr1C.regs0 Ptwr1C.regs_out1 KS_twr1C_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_304 ())). Qed.
Lemma twr1C_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> 4096 <= (V 55%nat) <= 140737487306752 ->
  4096 <= (V 56%nat) <= 140737487306752 -> L5.defined M (V 56%nat) 1 -> L5.writable RSEGS M (V 56%nat) 1 -> L5.defined M ((V 55%nat) - 1) 1 ->
  L5.writable RSEGS M ((V 55%nat) - 1) 1 -> (((V 55%nat) - 1) + 1 <= (V 56%nat) \/ (V 56%nat) + 1 <= ((V 55%nat) - 1)) -> (((V 2%nat) - 672) + 672 <= ((V 55%nat) - 1) \/ ((V 55%nat) - 1) + 1 <= ((V 2%nat) - 672)) -> (((V 2%nat) - 672) + 672 <= (V 56%nat) \/ (V 56%nat) + 1 <= ((V 2%nat) - 672)) ->
  L5.u8_at RSEGS M ((V 55%nat) - 1) (V 57%nat) -> 0 <= (V 57%nat) <= 255 -> L5.u8_at RSEGS M (V 56%nat) (V 58%nat) -> 0 <= (V 58%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 55%nat) - 1) <= bv_unsigned a < ((V 55%nat) - 1) + 1) -> ~ (((V 56%nat) + 0) <= bv_unsigned a < ((V 56%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 55%nat) - 1) <= i < ((V 55%nat) - 1) + 1) -> ~ (((V 56%nat) + 0) <= i < ((V 56%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x46dd8 M) (st fx' R' 0x46dd8 M')
        /\ (forall x, In x KS_twr1C_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 55%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 56%nat) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 57%nat)
        /\ (V 55%nat) < (((V 56%nat) + 18446744073709551615) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (V 56%nat) (V 57%nat)
        /\ L5.u8_at RSEGS M' ((V 55%nat) - 1) (V 58%nat))
      \/ (msteps RSEGS (st fx R 0x46dd8 M) (st fx' R' 0x46df8 M')
        /\ (forall x, In x KS_twr1C_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 55%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 56%nat) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 57%nat)
        /\ (((V 56%nat) + 18446744073709551615) mod 2 ^ 64) <= (V 55%nat)
        /\ L5.u8_at RSEGS M' (V 56%nat) (V 57%nat)
        /\ L5.u8_at RSEGS M' ((V 55%nat) - 1) (V 58%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2PX ()) [] (Mh_0197_blobs1.kr_b_305 ())). Qed.
(* [comment removed for export] *)

End PQTSW2PX.

End PnTsWs2PX.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155.
Module PnTsWs2DHP.
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsWs2DHP () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z;lxor_nonnegK46Stdlib9micromega5Tauto8GFormula09C56Stdlib6ZArith6BinInt1Z9log2_lxorC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwhD05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwhD09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP8KS_twhD0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwhD0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP=word_of_zpolyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0=C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP9land_byteC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP8lor_byteC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP@defined_of_KUnkaC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwhD03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwhD02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwhD03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwhD06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwhD03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwhD03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP;KS_twhD0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1S9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP9KS_twhD1SC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1S<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1S6cells0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1S3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1S3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP<KS_twhD1S_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1M9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP9KS_twhD1MC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1M<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1M6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1M3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP<KS_twhD1M_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1L9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP9KS_twhD1LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1L<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1L6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7PtwhD1L3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP<KS_twhD1L_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP8KS_twtD0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP;KS_twtD0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP8KS_twtD1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP6PtwtD13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP;KS_twtD1_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQTSW2DHP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_306 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_307 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_308 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_309 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_310 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_311 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_312 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_313 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_314 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_315 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_316 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_317 ())). Qed.
(* [comment removed for export] *)
Lemma lxor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_318 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lxor _ _ < 256 => apply lxor_byte; byte_go
  | |- 0 <= ?x mod 18446744073709551616 < 256 => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia); byte_go
  | |- 0 <= ?x mod 2 ^ 64 < 256 => rewrite (Z.mod_small x (2 ^ 64)) by (zfacts; lia); byte_go
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; rewrite ?Z.lxor_0_l, ?Z.lxor_0_r, ?Z.lor_0_l, ?Z.lor_0_r; byte_go.
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
Module PtwhD0 := BndP_Ns_081.LibSegNs_twhD0.
Definition KS_twhD0 : list nat := Eval vm_compute in (BG.kept_list 80 PtwhD0.regs0 PtwhD0.regs_out0).
Lemma KS_twhD0_ok : BG.kept_ok 80 PtwhD0.regs0 PtwhD0.regs_out0 KS_twhD0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_319 ())). Qed.
Lemma twhD0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 45%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = true -> L5.u64_at RSEGS M ((V 34%nat) + 8) 2 -> L5.u64_at RSEGS M ((V 34%nat) + 16) 8 -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 39%nat) ->
  4096 <= (V 39%nat) <= 140737487306752 -> L5.u64_at RSEGS M (V 39%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 39%nat) + 8) (V 38%nat) -> (((V 2%nat) - 672) + 672 <= (V 39%nat) \/ (V 39%nat) + 16 <= ((V 2%nat) - 672)) ->
  ((V 39%nat) + 16 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 39%nat)) -> ((V 39%nat) + 16 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 39%nat)) -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 672) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 672) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46c40 M) (st fx' R' 0xbe8b0 M')
        /\ (forall x, In x KS_twhD0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 277500
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 18) = Z_to_bv 64 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 2
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 120) (Z.lor (Z.land (V 37%nat) 2) (Z.land ((((2 * ((V 50%nat) / 2)) mod 2 ^ 64) + 1) mod 2 ^ 64) 253))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 289924
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 672) 448
        /\ L5.defined M' ((V 2%nat) - 192) 72
        /\ L5.defined M' ((V 2%nat) - 119) 7).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_320 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtwhD1S := BndP_Ns_081.LibSegNs_twhD1S.
Definition KS_twhD1S : list nat := Eval vm_compute in (BG.kept_list 251 PtwhD1S.regs0 PtwhD1S.regs_out0).
Lemma KS_twhD1S_ok : BG.kept_ok 251 PtwhD1S.regs0 PtwhD1S.regs_out0 KS_twhD1S = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_321 ())). Qed.
Lemma twhD1S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 201%nat) < 2 ^ 64 -> 0 <= (V 205%nat) < 2 ^ 64 -> 0 <= (V 206%nat) < 2 ^ 64 -> 0 <= (V 207%nat) < 2 ^ 64 -> 0 <= (V 211%nat) < 2 ^ 64 -> 0 <= (V 212%nat) < 2 ^ 64 -> 0 <= (V 213%nat) < 2 ^ 64 -> 0 <= (V 214%nat) < 2 ^ 64 -> 0 <= (V 215%nat) < 2 ^ 64 -> 0 <= (V 216%nat) < 2 ^ 64 -> 0 <= (V 217%nat) < 2 ^ 64 -> 0 <= (V 228%nat) < 2 ^ 64 -> 0 <= (V 229%nat) < 2 ^ 64 -> 0 <= (V 230%nat) < 2 ^ 64 -> 0 <= (V 231%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 201%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 (V 205%nat) -> getr R (reg 6) = Z_to_bv 64 (V 206%nat) -> getr R (reg 7) = Z_to_bv 64 (V 207%nat) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 11) = Z_to_bv 64 (V 211%nat) -> getr R (reg 12) = Z_to_bv 64 (V 212%nat) -> getr R (reg 13) = Z_to_bv 64 (V 213%nat) -> getr R (reg 14) = Z_to_bv 64 (V 214%nat) -> getr R (reg 15) = Z_to_bv 64 (V 215%nat) -> getr R (reg 16) = Z_to_bv 64 (V 216%nat) -> getr R (reg 17) = Z_to_bv 64 (V 217%nat) -> getr R (reg 18) = Z_to_bv 64 2 -> getr R (reg 28) = Z_to_bv 64 (V 228%nat) -> getr R (reg 29) = Z_to_bv 64 (V 229%nat) -> getr R (reg 30) = Z_to_bv 64 (V 230%nat) -> getr R (reg 31) = Z_to_bv 64 (V 231%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  0 <= (V 37%nat) <= 255 -> Z.testbit (V 37%nat) 0 = true -> 4096 <= (V 39%nat) <= 140737487306752 -> (((V 2%nat) - 672) + 672 <= (V 39%nat) \/ (V 39%nat) + 16 <= ((V 2%nat) - 672)) ->
  ((V 39%nat) + 16 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 39%nat)) -> ((V 39%nat) + 16 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 39%nat)) -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 96) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 112) 2 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (Z.lor (Z.land (V 37%nat) 2) (Z.land ((((2 * ((V 50%nat) / 2)) mod 2 ^ 64) + 1) mod 2 ^ 64) 253)) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 18%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 200) 289924 -> L5.u64_at RSEGS M ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24))) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23))) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22))) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20))) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19))) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 9%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.defined M ((V 2%nat) - 256) 32 -> L5.defined M ((V 2%nat) - 192) 72 ->
  L5.defined M ((V 2%nat) - 119) 7 -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 8) 2 -> L5.u64_at RSEGS M ((V 34%nat) + 16) 8 ->
  L5.u64_at RSEGS M ((V 34%nat) + 24) (V 39%nat) -> L5.u64_at RSEGS M (V 39%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 39%nat) + 8) (V 38%nat) -> L5.defined M ((V 2%nat) - 672) 416 ->
  4096 <= (V 41%nat) <= 140737487306752 -> L5.writable RSEGS M (V 41%nat) 64 -> (((V 2%nat) - 672) + 672 <= (V 41%nat) \/ (V 41%nat) + 64 <= ((V 2%nat) - 672)) -> (65536 + 748736 <= (V 41%nat) \/ (V 41%nat) + 64 <= 65536) ->
  ((V 41%nat) + 64 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 41%nat)) -> ((V 41%nat) + 64 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 41%nat)) -> ((V 41%nat) + 64 <= (V 39%nat) \/ (V 39%nat) + 16 <= (V 41%nat)) -> L5.defined M (V 41%nat) 64 ->
  L5.u8_at RSEGS M (V 45%nat) 0 -> L5.u64_at RSEGS M (V 45%nat) (V 49%nat) -> Z.testbit (V 49%nat) 0 = false -> 0 <= Z.land (V 49%nat) 255 <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 672) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 672) -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x43bfc M) (st fx' R' 0xbe8b0 M')
        /\ (forall x, In x KS_twhD1S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 418016
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 272)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 47
        /\ getr R' (reg 10) = Z_to_bv 64 48
        /\ bv_unsigned (getr R' (reg 11)) = ((72057594037927936 * (V 49%nat)) mod 2 ^ 64)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 22
        /\ getr R' (reg 19) = Z_to_bv 64 48
        /\ bv_unsigned (getr R' (reg 20)) = (((72057594037927936 * (V 49%nat)) mod 2 ^ 64) / 144115188075855872)
        /\ getr R' (reg 21) = Z_to_bv 64 22
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 ((2 * ((V 49%nat) / 2)) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 289960
        /\ L5.u64_at RSEGS M' (V 41%nat) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 41%nat) + 8) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 2
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 120) (Z.lor (Z.land (V 37%nat) 2) (Z.land ((((2 * ((V 50%nat) / 2)) mod 2 ^ 64) + 1) mod 2 ^ 64) 253))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 18%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 9%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 8%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 192) 72
        /\ L5.defined M' ((V 2%nat) - 119) 7
        /\ L5.defined M' ((V 2%nat) - 672) 408
        /\ L5.defined M' ((V 41%nat) + 16) 48).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_322 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtwhD1M := BndP_Ns_081.LibSegNs_twhD1M.
Definition KS_twhD1M : list nat := Eval vm_compute in (BG.kept_list 251 PtwhD1M.regs0 PtwhD1M.regs_out0).
Lemma KS_twhD1M_ok : BG.kept_ok 251 PtwhD1M.regs0 PtwhD1M.regs_out0 KS_twhD1M = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_323 ())). Qed.
Lemma twhD1M_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 201%nat) < 2 ^ 64 -> 0 <= (V 205%nat) < 2 ^ 64 -> 0 <= (V 206%nat) < 2 ^ 64 -> 0 <= (V 207%nat) < 2 ^ 64 -> 0 <= (V 211%nat) < 2 ^ 64 -> 0 <= (V 212%nat) < 2 ^ 64 -> 0 <= (V 213%nat) < 2 ^ 64 -> 0 <= (V 214%nat) < 2 ^ 64 -> 0 <= (V 215%nat) < 2 ^ 64 -> 0 <= (V 216%nat) < 2 ^ 64 -> 0 <= (V 217%nat) < 2 ^ 64 -> 0 <= (V 228%nat) < 2 ^ 64 -> 0 <= (V 229%nat) < 2 ^ 64 -> 0 <= (V 230%nat) < 2 ^ 64 -> 0 <= (V 231%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 201%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 (V 205%nat) -> getr R (reg 6) = Z_to_bv 64 (V 206%nat) -> getr R (reg 7) = Z_to_bv 64 (V 207%nat) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 11) = Z_to_bv 64 (V 211%nat) -> getr R (reg 12) = Z_to_bv 64 (V 212%nat) -> getr R (reg 13) = Z_to_bv 64 (V 213%nat) -> getr R (reg 14) = Z_to_bv 64 (V 214%nat) -> getr R (reg 15) = Z_to_bv 64 (V 215%nat) -> getr R (reg 16) = Z_to_bv 64 (V 216%nat) -> getr R (reg 17) = Z_to_bv 64 (V 217%nat) -> getr R (reg 18) = Z_to_bv 64 2 -> getr R (reg 28) = Z_to_bv 64 (V 228%nat) -> getr R (reg 29) = Z_to_bv 64 (V 229%nat) -> getr R (reg 30) = Z_to_bv 64 (V 230%nat) -> getr R (reg 31) = Z_to_bv 64 (V 231%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  0 <= (V 37%nat) <= 255 -> Z.testbit (V 37%nat) 0 = true -> 4096 <= (V 39%nat) <= 140737487306752 -> (((V 2%nat) - 672) + 672 <= (V 39%nat) \/ (V 39%nat) + 16 <= ((V 2%nat) - 672)) ->
  ((V 39%nat) + 16 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 39%nat)) -> ((V 39%nat) + 16 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 39%nat)) -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 96) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 112) 2 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (Z.lor (Z.land (V 37%nat) 2) (Z.land ((((2 * ((V 50%nat) / 2)) mod 2 ^ 64) + 1) mod 2 ^ 64) 253)) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 18%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 200) 289924 -> L5.u64_at RSEGS M ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24))) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23))) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22))) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20))) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19))) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 9%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.defined M ((V 2%nat) - 256) 32 -> L5.defined M ((V 2%nat) - 192) 72 ->
  L5.defined M ((V 2%nat) - 119) 7 -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 8) 2 -> L5.u64_at RSEGS M ((V 34%nat) + 16) 8 ->
  L5.u64_at RSEGS M ((V 34%nat) + 24) (V 39%nat) -> L5.u64_at RSEGS M (V 39%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 39%nat) + 8) (V 38%nat) -> L5.defined M ((V 2%nat) - 672) 416 ->
  4096 <= (V 41%nat) <= 140737487306752 -> L5.writable RSEGS M (V 41%nat) 64 -> (((V 2%nat) - 672) + 672 <= (V 41%nat) \/ (V 41%nat) + 64 <= ((V 2%nat) - 672)) -> (65536 + 748736 <= (V 41%nat) \/ (V 41%nat) + 64 <= 65536) ->
  ((V 41%nat) + 64 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 41%nat)) -> ((V 41%nat) + 64 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 41%nat)) -> ((V 41%nat) + 64 <= (V 39%nat) \/ (V 39%nat) + 16 <= (V 41%nat)) -> L5.defined M (V 41%nat) 64 ->
  L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true -> L5.u64_at RSEGS M (V 45%nat) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 45%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 27 <= (V 46%nat) <= 45 -> Z.testbit (V 46%nat) 0 = true ->
  25 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 43 -> 4096 <= (V 47%nat) <= 140737487306752 -> L5.defined M (V 47%nat) 26 -> ((V 47%nat) + 26 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) ->
  ((V 47%nat) + 26 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 26 <= ((V 2%nat) - 672)) -> ((V 41%nat) + 64 <= (V 47%nat) \/ (V 47%nat) + 26 <= (V 41%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 672) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 672) -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x43bfc M) (st fx' R' 0xbe8b0 M')
        /\ (forall x, In x KS_twhD1M -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 418016
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 272)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 47
        /\ getr R' (reg 10) = Z_to_bv 64 48
        /\ getr R' (reg 11) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 22
        /\ getr R' (reg 19) = Z_to_bv 64 48
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((2 * ((V 46%nat) / 2)) - 1)
        /\ getr R' (reg 22) = Z_to_bv 64 1
        /\ getr R' (reg 23) = Z_to_bv 64 ((2 * ((V 46%nat) / 2)) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 289960
        /\ L5.u64_at RSEGS M' (V 41%nat) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 41%nat) + 8) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 2
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 120) (Z.lor (Z.land (V 37%nat) 2) (Z.land ((((2 * ((V 50%nat) / 2)) mod 2 ^ 64) + 1) mod 2 ^ 64) 253))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 18%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 9%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 8%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 192) 72
        /\ L5.defined M' ((V 2%nat) - 119) 7
        /\ L5.defined M' ((V 2%nat) - 672) 408
        /\ L5.defined M' ((V 41%nat) + 16) 48).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_324 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtwhD1L := BndP_Ns_081.LibSegNs_twhD1L.
Definition KS_twhD1L : list nat := Eval vm_compute in (BG.kept_list 251 PtwhD1L.regs0 PtwhD1L.regs_out0).
Lemma KS_twhD1L_ok : BG.kept_ok 251 PtwhD1L.regs0 PtwhD1L.regs_out0 KS_twhD1L = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_325 ())). Qed.
Lemma twhD1L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 201%nat) < 2 ^ 64 -> 0 <= (V 205%nat) < 2 ^ 64 -> 0 <= (V 206%nat) < 2 ^ 64 -> 0 <= (V 207%nat) < 2 ^ 64 -> 0 <= (V 211%nat) < 2 ^ 64 -> 0 <= (V 212%nat) < 2 ^ 64 -> 0 <= (V 213%nat) < 2 ^ 64 -> 0 <= (V 214%nat) < 2 ^ 64 -> 0 <= (V 215%nat) < 2 ^ 64 -> 0 <= (V 216%nat) < 2 ^ 64 -> 0 <= (V 217%nat) < 2 ^ 64 -> 0 <= (V 228%nat) < 2 ^ 64 -> 0 <= (V 229%nat) < 2 ^ 64 -> 0 <= (V 230%nat) < 2 ^ 64 -> 0 <= (V 231%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 201%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 (V 205%nat) -> getr R (reg 6) = Z_to_bv 64 (V 206%nat) -> getr R (reg 7) = Z_to_bv 64 (V 207%nat) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 11) = Z_to_bv 64 (V 211%nat) -> getr R (reg 12) = Z_to_bv 64 (V 212%nat) -> getr R (reg 13) = Z_to_bv 64 (V 213%nat) -> getr R (reg 14) = Z_to_bv 64 (V 214%nat) -> getr R (reg 15) = Z_to_bv 64 (V 215%nat) -> getr R (reg 16) = Z_to_bv 64 (V 216%nat) -> getr R (reg 17) = Z_to_bv 64 (V 217%nat) -> getr R (reg 18) = Z_to_bv 64 2 -> getr R (reg 28) = Z_to_bv 64 (V 228%nat) -> getr R (reg 29) = Z_to_bv 64 (V 229%nat) -> getr R (reg 30) = Z_to_bv 64 (V 230%nat) -> getr R (reg 31) = Z_to_bv 64 (V 231%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) ->
  0 <= (V 37%nat) <= 255 -> Z.testbit (V 37%nat) 0 = true -> 4096 <= (V 39%nat) <= 140737487306752 -> (((V 2%nat) - 672) + 672 <= (V 39%nat) \/ (V 39%nat) + 16 <= ((V 2%nat) - 672)) ->
  ((V 39%nat) + 16 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 39%nat)) -> ((V 39%nat) + 16 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 39%nat)) -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 -> ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 96) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 112) 2 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (Z.lor (Z.land (V 37%nat) 2) (Z.land ((((2 * ((V 50%nat) / 2)) mod 2 ^ 64) + 1) mod 2 ^ 64) 253)) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 18%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 200) 289924 -> L5.u64_at RSEGS M ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24))) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23))) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22))) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20))) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19))) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 9%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.defined M ((V 2%nat) - 256) 32 -> L5.defined M ((V 2%nat) - 192) 72 ->
  L5.defined M ((V 2%nat) - 119) 7 -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 8) 2 -> L5.u64_at RSEGS M ((V 34%nat) + 16) 8 ->
  L5.u64_at RSEGS M ((V 34%nat) + 24) (V 39%nat) -> L5.u64_at RSEGS M (V 39%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 39%nat) + 8) (V 38%nat) -> L5.defined M ((V 2%nat) - 672) 416 ->
  4096 <= (V 41%nat) <= 140737487306752 -> L5.writable RSEGS M (V 41%nat) 64 -> (((V 2%nat) - 672) + 672 <= (V 41%nat) \/ (V 41%nat) + 64 <= ((V 2%nat) - 672)) -> (65536 + 748736 <= (V 41%nat) \/ (V 41%nat) + 64 <= 65536) ->
  ((V 41%nat) + 64 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 41%nat)) -> ((V 41%nat) + 64 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 41%nat)) -> ((V 41%nat) + 64 <= (V 39%nat) \/ (V 39%nat) + 16 <= (V 41%nat)) -> L5.defined M (V 41%nat) 64 ->
  L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true -> L5.u64_at RSEGS M (V 45%nat) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 45%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 47 <= (V 46%nat) <= 268435457 -> 45 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 ->
  4096 <= (V 47%nat) <= 140737487306752 -> L5.writable RSEGS M (V 47%nat) 32 -> L5.defined M (V 47%nat) 32 -> ((V 47%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) ->
  ((V 47%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 32 <= ((V 2%nat) - 672)) -> ((V 41%nat) + 64 <= (V 47%nat) \/ (V 47%nat) + 32 <= (V 41%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 672) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 672) -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x43bfc M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_twhD1L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 19) = Z_to_bv 64 10
        /\ getr R' (reg 20) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 21) = Z_to_bv 64 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 152) 0
        /\ L5.u64_at RSEGS M' (V 41%nat) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 41%nat) + 8) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 2
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 120) (Z.lor (Z.land (V 37%nat) 2) (Z.land ((((2 * ((V 50%nat) / 2)) mod 2 ^ 64) + 1) mod 2 ^ 64) 253))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 18%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 289924
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 18%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 9%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 8%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 256) 32
        /\ L5.defined M' ((V 2%nat) - 192) 8
        /\ L5.defined M' ((V 2%nat) - 183) 7
        /\ L5.defined M' ((V 2%nat) - 151) 7
        /\ L5.defined M' ((V 2%nat) - 119) 7
        /\ L5.defined M' ((V 2%nat) - 672) 416
        /\ L5.defined M' ((V 41%nat) + 16) 48).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_326 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtwtD0 := BndP_Ns_082.LibSegNs_twtD0.
Definition KS_twtD0 : list nat := Eval vm_compute in (BG.kept_list 80 PtwtD0.regs0 PtwtD0.regs_out0).
Lemma KS_twtD0_ok : BG.kept_ok 80 PtwtD0.regs0 PtwtD0.regs_out0 KS_twtD0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_327 ())). Qed.
Lemma twtD0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.u8_at RSEGS M ((V 2%nat) - 184) 0 -> L5.u8_at RSEGS M ((V 2%nat) - 152) (V 58%nat) -> 0 <= (V 58%nat) <= 255 -> Z.testbit (V 58%nat) 0 = false ->
  L5.u8_at RSEGS M ((V 2%nat) - 120) (V 57%nat) -> 0 <= (V 57%nat) <= 255 -> Z.testbit (V 57%nat) 0 = true -> L5.u64_at RSEGS M ((V 2%nat) - 104) 8 ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737487306752 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 73%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46df8 M) (st fx' R' 0x63dc4 M')
        /\ (forall x, In x KS_twtD0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290392
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 64).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_328 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtwtD1 := BndP_Ns_082.LibSegNs_twtD1.
Definition KS_twtD1 : list nat := Eval vm_compute in (BG.kept_list 251 PtwtD1.regs0 PtwtD1.regs_out0).
Lemma KS_twtD1_ok : BG.kept_ok 251 PtwtD1.regs0 PtwtD1.regs_out0 KS_twtD1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_329 ())). Qed.
Lemma twtD1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 201%nat) < 2 ^ 64 -> 0 <= (V 205%nat) < 2 ^ 64 -> 0 <= (V 206%nat) < 2 ^ 64 -> 0 <= (V 207%nat) < 2 ^ 64 -> 0 <= (V 210%nat) < 2 ^ 64 -> 0 <= (V 211%nat) < 2 ^ 64 -> 0 <= (V 212%nat) < 2 ^ 64 -> 0 <= (V 213%nat) < 2 ^ 64 -> 0 <= (V 214%nat) < 2 ^ 64 -> 0 <= (V 215%nat) < 2 ^ 64 -> 0 <= (V 216%nat) < 2 ^ 64 -> 0 <= (V 217%nat) < 2 ^ 64 -> 0 <= (V 228%nat) < 2 ^ 64 -> 0 <= (V 229%nat) < 2 ^ 64 -> 0 <= (V 230%nat) < 2 ^ 64 -> 0 <= (V 231%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 201%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 5) = Z_to_bv 64 (V 205%nat) -> getr R (reg 6) = Z_to_bv 64 (V 206%nat) -> getr R (reg 7) = Z_to_bv 64 (V 207%nat) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 210%nat) -> getr R (reg 11) = Z_to_bv 64 (V 211%nat) -> getr R (reg 12) = Z_to_bv 64 (V 212%nat) -> getr R (reg 13) = Z_to_bv 64 (V 213%nat) -> getr R (reg 14) = Z_to_bv 64 (V 214%nat) -> getr R (reg 15) = Z_to_bv 64 (V 215%nat) -> getr R (reg 16) = Z_to_bv 64 (V 216%nat) -> getr R (reg 17) = Z_to_bv 64 (V 217%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 136) -> getr R (reg 19) = Z_to_bv 64 10 -> getr R (reg 20) = Z_to_bv 64 14757395258967641293 -> getr R (reg 21) = Z_to_bv 64 18 -> getr R (reg 28) = Z_to_bv 64 (V 228%nat) -> getr R (reg 29) = Z_to_bv 64 (V 229%nat) -> getr R (reg 30) = Z_to_bv 64 (V 230%nat) -> getr R (reg 31) = Z_to_bv 64 (V 231%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  0 <= (V 58%nat) <= 255 -> Z.testbit (V 58%nat) 0 = false -> 0 <= (V 57%nat) <= 255 -> Z.testbit (V 57%nat) 0 = true ->
  L5.u8_at RSEGS M ((V 2%nat) - 184) 0 -> L5.u8_at RSEGS M ((V 2%nat) - 152) (V 58%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) 8 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 73%nat) -> L5.defined M ((V 2%nat) - 672) 480 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46e58 M) (st fx' R' 0x46e88 M')
        /\ (forall x, In x KS_twtD1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 73%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DHP ()) [] (Mh_0197_blobs1.kr_b_330 ())). Qed.
(* [comment removed for export] *)

End PQTSW2DHP.

End PnTsWs2DHP.
Module PnTsWs2HP.
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0163.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsWs2HP () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z;lxor_nonnegK46Stdlib9micromega5Tauto8GFormula09C56Stdlib6ZArith6BinInt1Z9log2_lxorC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_twhLC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhL<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP=word_of_zpolyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP9land_le_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z:mul_div_leC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP@defined_of_KUnkaC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhL6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhL3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP:KS_twhL_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_twhSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhS6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP:KS_twhS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2S9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_tw2SC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2S<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2S3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2S3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP:KS_tw2S_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3S9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_tw3SC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3S<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3S6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3S3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3S3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP:KS_tw3S_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhM5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhM9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_twhMC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhM<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhM3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhM2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhM3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhM6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhM3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5PtwhM3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP:KS_twhM_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2M9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_tw2MC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2M<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw2M3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP:KS_tw2M_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3M9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_tw3MC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3M<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw3M3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP:KS_tw3M_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw4M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw4M9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_tw4MC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw4M<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw4M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw4M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw4M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw4M6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw4M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP5Ptw4M3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP:KS_tw4M_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQTSW2HP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_331 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_332 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_333 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_334 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_335 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_336 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_337 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_338 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_339 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_340 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_341 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_342 ())). Qed.
(* [comment removed for export] *)
Lemma lxor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_343 ())). Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lxor _ _ < 256 => apply lxor_byte; byte_go
  | |- 0 <= ?x mod 18446744073709551616 < 256 => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia); byte_go
  | |- 0 <= ?x mod 2 ^ 64 < 256 => rewrite (Z.mod_small x (2 ^ 64)) by (zfacts; lia); byte_go
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; rewrite ?Z.lxor_0_l, ?Z.lxor_0_r, ?Z.lor_0_l, ?Z.lor_0_r; byte_go.
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
Module PtwhL := BndP_Ns_081.LibSegNs_twhL.
Definition KS_twhL : list nat := Eval vm_compute in (BG.kept_list 80 PtwhL.regs0 PtwhL.regs_out0).
Lemma KS_twhL_ok : BG.kept_ok 80 PtwhL.regs0 PtwhL.regs_out0 KS_twhL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_344 ())). Qed.
Lemma twhL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 45%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 2 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true ->
  L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 47 <= (V 46%nat) <= 268435457 ->
  45 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 268435455 -> 4096 <= (V 47%nat) <= 140737487306752 -> L5.writable RSEGS M (V 47%nat) 32 -> L5.defined M (V 47%nat) 32 ->
  ((V 47%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 32 <= ((V 2%nat) - 672)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 672) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 672) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46c40 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_twhL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 19) = Z_to_bv 64 10
        /\ getr R' (reg 20) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 21) = Z_to_bv 64 18
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 152) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 2
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 120) ((((4 * ((V 50%nat) / 4)) mod 2 ^ 64) + (Z.land (V 37%nat) 2)) mod 2 ^ 64)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 672) 488
        /\ L5.defined M' ((V 2%nat) - 183) 7
        /\ L5.defined M' ((V 2%nat) - 151) 7
        /\ L5.defined M' ((V 2%nat) - 119) 7).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_345 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtwhS := BndP_Ns_082.LibSegNs_twhS.
Definition KS_twhS : list nat := Eval vm_compute in (BG.kept_list 80 PtwhS.regs0 PtwhS.regs_out0).
Lemma KS_twhS_ok : BG.kept_ok 80 PtwhS.regs0 PtwhS.regs_out0 KS_twhS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_346 ())). Qed.
Lemma twhS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 45%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 2 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) 0 -> L5.u64_at RSEGS M (V 45%nat) (V 49%nat) -> Z.testbit (V 49%nat) 0 = false ->
  0 <= Z.land (V 49%nat) 255 <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 672) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 672) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46c40 M) (st fx' R' 0xbe8b0 M')
        /\ (forall x, In x KS_twhS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 418016
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 272)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 47
        /\ getr R' (reg 10) = Z_to_bv 64 48
        /\ bv_unsigned (getr R' (reg 11)) = ((72057594037927936 * (V 49%nat)) mod 2 ^ 64)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 22
        /\ getr R' (reg 18) = Z_to_bv 64 2
        /\ getr R' (reg 19) = Z_to_bv 64 48
        /\ bv_unsigned (getr R' (reg 20)) = (((72057594037927936 * (V 49%nat)) mod 2 ^ 64) / 144115188075855872)
        /\ getr R' (reg 21) = Z_to_bv 64 22
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 ((2 * ((V 49%nat) / 2)) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 289960
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 2
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 120) ((((4 * ((V 50%nat) / 4)) mod 2 ^ 64) + (Z.land (V 37%nat) 2)) mod 2 ^ 64)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 672) 408
        /\ L5.defined M' ((V 2%nat) - 192) 72
        /\ L5.defined M' ((V 2%nat) - 119) 7).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_347 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptw2S := BndP_Ns_079.LibSegNs_tw2S.
Definition KS_tw2S : list nat := Eval vm_compute in (BG.kept_list 80 Ptw2S.regs0 Ptw2S.regs_out0).
Lemma KS_tw2S_ok : BG.kept_ok 80 Ptw2S.regs0 Ptw2S.regs_out0 KS_tw2S = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_348 ())). Qed.
Lemma tw2S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 272) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 47 -> getr R (reg 10) = Z_to_bv 64 (V 48%nat) -> getr R (reg 19) = Z_to_bv 64 48 -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 22 -> getr R (reg 22) = Z_to_bv 64 0 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> 4096 <= (V 48%nat) <= 140737487306752 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x660e0 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_tw2S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 418144
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 45%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 45%nat) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_349 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptw3S := BndP_Ns_080.LibSegNs_tw3S.
Definition KS_tw3S : list nat := Eval vm_compute in (BG.kept_list 80 Ptw3S.regs0 Ptw3S.regs_out0).
Lemma KS_tw3S_ok : BG.kept_ok 80 Ptw3S.regs0 Ptw3S.regs_out0 KS_tw3S = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_350 ())). Qed.
Lemma tw3S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 272) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 47 -> getr R (reg 18) = Z_to_bv 64 (V 48%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 45%nat) + 1) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 22 -> getr R (reg 22) = Z_to_bv 64 0 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) ->
  L5.writable RSEGS M (V 45%nat) 24 -> 4096 <= (V 48%nat) <= 140737487306752 -> L5.u64_at RSEGS M ((V 2%nat) - 200) 289960 -> L5.u64_at RSEGS M ((V 2%nat) - 208) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) 2 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 240) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 248) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 256) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 264) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 2%nat) - 184) <= bv_unsigned a < ((V 2%nat) - 184) + 64) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 2%nat) - 184) <= i < ((V 2%nat) - 184) + 64) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x66160 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_tw3S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 19) = Z_to_bv 64 10
        /\ getr R' (reg 20) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 21) = Z_to_bv 64 18
        /\ getr R' (reg 22) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 152) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) 0
        /\ L5.u64_at RSEGS M' (V 45%nat) 49
        /\ L5.defined M' ((V 2%nat) - 672) 488
        /\ L5.defined M' ((V 2%nat) - 183) 7
        /\ L5.defined M' ((V 2%nat) - 151) 7
        /\ L5.defined M' ((V 2%nat) - 120) 120
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 289960
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (V 71%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 73%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) (V 74%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_351 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtwhM := BndP_Ns_082.LibSegNs_twhM.
Definition KS_twhM : list nat := Eval vm_compute in (BG.kept_list 80 PtwhM.regs0 PtwhM.regs_out0).
Lemma KS_twhM_ok : BG.kept_ok 80 PtwhM.regs0 PtwhM.regs_out0 KS_twhM = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_352 ())). Qed.
Lemma twhM_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 40%nat) -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 45%nat) ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> L5.u8_at RSEGS M ((V 2%nat) - 120) (V 50%nat) -> 0 <= (V 50%nat) <= 255 -> 140735332483744 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 672)) -> L5.u8_at RSEGS M (V 34%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 ->
  Z.testbit (V 37%nat) 0 = false -> L5.u64_at RSEGS M ((V 34%nat) + 8) 2 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 36%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.writable RSEGS M (V 45%nat) 24 ->
  ((V 34%nat) + 32 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 34%nat)) -> L5.u8_at RSEGS M (V 45%nat) (V 49%nat) -> 0 <= (V 49%nat) <= 255 -> Z.testbit (V 49%nat) 0 = true ->
  L5.u64_at RSEGS M (V 45%nat) (V 46%nat) -> L5.u64_at RSEGS M ((V 45%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 27 <= (V 46%nat) <= 45 ->
  Z.testbit (V 46%nat) 0 = true -> 25 <= (((Z.land (V 46%nat) 18446744073709551614) + 18446744073709551615) mod 2 ^ 64) <= 43 -> 4096 <= (V 47%nat) <= 140737487306752 -> L5.defined M (V 47%nat) 26 ->
  ((V 47%nat) + 26 <= (V 45%nat) \/ (V 45%nat) + 24 <= (V 47%nat)) -> ((V 47%nat) + 26 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 47%nat)) -> (((V 2%nat) - 672) + 672 <= (V 47%nat) \/ (V 47%nat) + 26 <= ((V 2%nat) - 672)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 672) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 672) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x46c40 M) (st fx' R' 0xbe8b0 M')
        /\ (forall x, In x KS_twhM -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 418016
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 272)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 47
        /\ getr R' (reg 10) = Z_to_bv 64 48
        /\ getr R' (reg 11) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 22
        /\ getr R' (reg 18) = Z_to_bv 64 2
        /\ getr R' (reg 19) = Z_to_bv 64 48
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((2 * ((V 46%nat) / 2)) - 1)
        /\ getr R' (reg 22) = Z_to_bv 64 1
        /\ getr R' (reg 23) = Z_to_bv 64 ((2 * ((V 46%nat) / 2)) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 289960
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 2
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 120) ((((4 * ((V 50%nat) / 4)) mod 2 ^ 64) + (Z.land (V 37%nat) 2)) mod 2 ^ 64)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.defined M' ((V 2%nat) - 672) 408
        /\ L5.defined M' ((V 2%nat) - 192) 72
        /\ L5.defined M' ((V 2%nat) - 119) 7).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_353 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptw2M := BndP_Ns_079.LibSegNs_tw2M.
Definition KS_tw2M : list nat := Eval vm_compute in (BG.kept_list 80 Ptw2M.regs0 Ptw2M.regs_out0).
Lemma KS_tw2M_ok : BG.kept_ok 80 Ptw2M.regs0 Ptw2M.regs_out0 KS_tw2M = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_354 ())). Qed.
Lemma tw2M_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 272) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 47 -> getr R (reg 10) = Z_to_bv 64 (V 48%nat) -> getr R (reg 19) = Z_to_bv 64 48 -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 (V 75%nat) -> getr R (reg 22) = Z_to_bv 64 1 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> L5.u64_at RSEGS M ((V 45%nat) + 8) 0 ->
  L5.u64_at RSEGS M ((V 45%nat) + 16) (V 47%nat) -> 4096 <= (V 47%nat) <= 140737487306752 -> 4096 <= (V 48%nat) <= 140737487306752 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x660e0 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_tw2M -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 418144
        /\ getr R' (reg 11) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_355 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptw3M := BndP_Ns_080.LibSegNs_tw3M.
Definition KS_tw3M : list nat := Eval vm_compute in (BG.kept_list 80 Ptw3M.regs0 Ptw3M.regs_out0).
Lemma KS_tw3M_ok : BG.kept_ok 80 Ptw3M.regs0 Ptw3M.regs_out0 KS_tw3M = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_356 ())). Qed.
Lemma tw3M_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 272) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 47 -> getr R (reg 18) = Z_to_bv 64 (V 48%nat) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 (V 75%nat) -> getr R (reg 22) = Z_to_bv 64 1 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) -> 4096 <= (V 47%nat) <= 140737487306752 ->
  4096 <= (V 48%nat) <= 140737487306752 -> 25 <= (V 75%nat) <= 43 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x66160 M) (st fx' R' 0x63dc4 M')
        /\ (forall x, In x KS_tw3M -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 418192
        /\ getr R' (reg 10) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 75%nat) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_357 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Ptw4M := BndP_Ns_080.LibSegNs_tw4M.
Definition KS_tw4M : list nat := Eval vm_compute in (BG.kept_list 80 Ptw4M.regs0 Ptw4M.regs_out0).
Lemma KS_tw4M_ok : BG.kept_ok 80 Ptw4M.regs0 Ptw4M.regs_out0 KS_tw4M = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_358 ())). Qed.
Lemma tw4M_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 272) -> getr R (reg 8) = Z_to_bv 64 (V 45%nat) -> getr R (reg 9) = Z_to_bv 64 47 -> getr R (reg 18) = Z_to_bv 64 (V 48%nat) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 22) = Z_to_bv 64 1 ->
  140735332483744 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 672) 672 -> L5.img_clear M 65536 814272 ->
  L5.defined M ((V 2%nat) - 672) 672 -> 140735332483744 <= (V 45%nat) <= 140737488355304 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 672) + 672 <= (V 45%nat) \/ (V 45%nat) + 24 <= ((V 2%nat) - 672)) ->
  L5.writable RSEGS M (V 45%nat) 24 -> 4096 <= (V 48%nat) <= 140737487306752 -> L5.u64_at RSEGS M ((V 2%nat) - 200) 289960 -> L5.u64_at RSEGS M ((V 2%nat) - 208) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) 2 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 240) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 248) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 256) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 264) (V 74%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 672) <= bv_unsigned a < ((V 2%nat) - 672) + 480) -> ~ (((V 2%nat) - 184) <= bv_unsigned a < ((V 2%nat) - 184) + 64) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 672) <= i < ((V 2%nat) - 672) + 480) -> ~ (((V 2%nat) - 184) <= i < ((V 2%nat) - 184) + 64) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x66190 M) (st fx' R' 0x42450 M')
        /\ (forall x, In x KS_tw4M -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 290052
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 19) = Z_to_bv 64 10
        /\ getr R' (reg 20) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 21) = Z_to_bv 64 18
        /\ getr R' (reg 22) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 74%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 10000000000000000000
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 152) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 8) 0
        /\ L5.u64_at RSEGS M' (V 45%nat) 49
        /\ L5.defined M' ((V 2%nat) - 672) 488
        /\ L5.defined M' ((V 2%nat) - 183) 7
        /\ L5.defined M' ((V 2%nat) - 151) 7
        /\ L5.defined M' ((V 2%nat) - 120) 120
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 289960
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) (V 71%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 73%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) (V 74%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2HP ()) [] (Mh_0197_blobs1.kr_b_359 ())). Qed.
(* [comment removed for export] *)

End PQTSW2HP.

End PnTsWs2HP.
